# This file is a part of Julia. License is MIT: https://julialang.org/license

#####################
# structs/constants #
#####################

struct Constant
    val
end

const Fields = Vector{Any} # TODO Vector{TypeLattice}
const _TOP_FIELDS = Fields()

struct ConditionalInfo
    var::SlotNumber
    vtype    # TODO ::TypeLattice
    elsetype # TODO ::TypeLattice
    function ConditionalInfo(var::SlotNumber, @nospecialize(vtype), @nospecialize(elsetype))
        return new(var, vtype, elsetype)
    end
end

struct InterConditionalInfo
    slot::Int
    vtype    # TODO ::TypeLattice
    elsetype # TODO ::TypeLattice
    function InterConditionalInfo(slot::Int, @nospecialize(vtype), @nospecialize(elsetype))
        return new(slot, vtype, elsetype)
    end
end
const AnyConditionalInfo = Union{ConditionalInfo,InterConditionalInfo}
const _TOP_CONDITIONAL_INFO = ConditionalInfo(SlotNumber(0), Any, Any)

struct PartialTypeVarInfo
    tv::TypeVar
    PartialTypeVarInfo(tv::TypeVar) = new(tv)
end
const _TOP_PARTIALTYPEVAR_INFO = PartialTypeVarInfo(TypeVar(:⊤))

"""
    x::TypeLattice

The lattice for Julia's native type inference implementation.
`TypeLattice` has following lattice properties and these attributes are combined to create
a partial lattice whose height is infinite.

---
- `x.constant::Union{Nothing,Constant}` \\
  If `x.constant !== nothing`, it means `x` is constant-folded.
  The actual constant value can be retrieved using `constant(x)`.
  Note that it is valid if `x` has other lattice properties even when it is constant-folded.
  For example, `x` may have "interesting" `x.conditional` property when `isConst(x)`.

  See also:
  - constructor: `Const(val)`
  - property query: `isConst(x)`
  - value retrieval: `constant(x)`

---
- `x.fields::Vector{Any}` \\
  Keeps field information about a partially constant-folded `struct`.
  When fields of a `struct` are fully known we just form `Const`, but even when some of the
  fields can not be folded inference will try to keep constant information of other foled
  fields with this lattice property.
  If this `x.fields` is empty `x` does not have the partially constant-folded information at all.
  This lattice property assumes the following invariants:
  - `immutabletype(x.typ)`: since inference does not reason about memory-effects of object fields
  - `x.typ` is concrete or `Tuple` type: the lattice assumes `Const ⊑ PartialStruct ⊑ concrete type ⊑ abstract type`

  See also:
  - constructor: `PartialStruct(typ, fields)`
  - property query: `isPartialStruct(x)`

---
- `x.conditional :: Union{ConditionalInfo, InterConditionalInfo}` \\
  The lattice property that comes along with `Bool`.
  It keeps some information about how this `Bool` value was created in order to enable a
  limited amount of type constraint back-propagation.
  In particular, if we branch on an object that has this lattice property `cnd::ConditionalInfo`,
  then we may assume that in the "then" branch, the type of `cnd.var::SlotNumber` will be
  limited by `cnd.vtype` and in the "else" branch, it will be limited by `cnd.elsetype`.
  By default, this lattice is initialized as `_TOP_CONDITIONAL_INFO`, which does not convey
  any useful information (and thus should never be used).
  Example:
  ```
  cond = isa(x::Union{Int, String}, Int) # ::Conditional(:(x), Int, String)
  if cond
      ... # x::Int
  else
      ... # x::String
  end
  ```

  In an inter-procedural context, this property can be `x.conditional::InterConditionalInfo`.
  It is very similar to `ConditionalInfo`, but conveys inter-procedural constraints imposed
  on call arguments.
  They are separated to catch logic errors: the lattice property is `InterConditionalInfo`
  while processing a call, then `ConditionalInfo` everywhere else.
  Thus `ConditionalInfo` and `InterConditionalInfo` should not appear in the same context --
  their usages are disjoint -- though we define the lattice for `InterConditionalInfo`.

  See also:
  - constructor: `Conditional(::SlotNumber, vtype, elsetype)` / `InterConditional(::Int, vtype, elsetype)`
  - property query: `isConditional(x)` / `isInterConditional(x)` / `isAnyConditional(x)`
  - property retrieval: `conditional(x)` / `interconditional(x)`
  - property widening: `widenconditional(x)`

---
- `x.partialtypevar :: PartialTypeVarInfo`
  Tracks an identity of `TypeVar` so that `x` can produce better inference for `UnionAll`
  construction.
  By default `x.partialtypevar` is initialized with `_TOP_PARTIALTYPEVAR_INFO` (no information).

  See also:
  - constructor: `PartialTypeVar(::TypeVar, lb_certain::Bool, ub_certain::Bool)`
  - property query: `isPartialTypeVar(x)`

---
"""
struct TypeLattice <: _AbstractLattice
    typ::Type
    # COMBAK capitalize these field names ?
    constant::Union{Nothing,Constant}
    fields::Fields
    conditional::AnyConditionalInfo
    partialtypevar::PartialTypeVarInfo

    function TypeLattice(@nospecialize(typ);
                         constant::Union{Nothing,Constant}  = nothing,
                         fields::Fields                     = _TOP_FIELDS,
                         conditional::AnyConditionalInfo    = _TOP_CONDITIONAL_INFO,
                         partialtypevar::PartialTypeVarInfo = _TOP_PARTIALTYPEVAR_INFO,
                         )
        # TODO remove these safe-checks
        if isa(typ, TypeLattice)
            return typ
        elseif isa(typ, CompilerTypes)
            return typ
        end
        return new(widenconst(typ)::Type, constant, fields, conditional, partialtypevar)
    end
end

NativeType(@nospecialize typ) = TypeLattice(typ::Type)
# NOTE once we pack all extended lattice types into `TypeLattice`, we don't need this `unwraptype`:
# - `unwraptype`: unwrap `NativeType` to native Julia type
# - `widenconst`: unwrap any extended type lattice to native Julia type
unwraptype(@nospecialize t) = (isa(t, TypeLattice) && t === NativeType(t.typ)) ? t.typ : t

function Const(@nospecialize val)
    typ = isa(val, Type) ? Type{val} : typeof(val)
    constant = Constant(val)
    return TypeLattice(typ; constant)
end
isConst(@nospecialize typ) = isa(typ, TypeLattice) && typ.constant !== nothing
# access to the `x.constant.val` field with improved type instability where `isConst(x)` holds
# TODO once https://github.com/JuliaLang/julia/pull/41199 is merged,
# all usages of this function can be simply replaced with `x.constant.val`
@inline constant(x::TypeLattice) = (x.constant::Constant).val

function PartialStruct(@nospecialize(typ), fields::Fields)
    @assert (isconcretetype(typ) || istupletype(typ)) "invalid PartialStruct typ"
    typ = typ::DataType
    @assert !ismutabletype(typ) "invalid PartialStruct typ"
    for field in fields
        @assert !isConditional(field) "invalid PartialStruct field"
    end
    return TypeLattice(typ; fields)
end
istupletype(@nospecialize typ) = isa(typ, DataType) && typ.name.name === :Tuple
isPartialStruct(@nospecialize typ) = isa(typ, TypeLattice) && length(typ.fields) ≠ 0

# TODO do some assertions ?
function Conditional(var::SlotNumber, @nospecialize(vtype), @nospecialize(elsetype))
    if vtype == ⊥
        constant = Constant(false)
    elseif elsetype == ⊥
        constant = Constant(true)
    else
        constant = nothing
    end
    conditional = ConditionalInfo(var, vtype, elsetype)
    return TypeLattice(Bool; constant, conditional)
end
function InterConditional(slot::Int, @nospecialize(vtype), @nospecialize(elsetype))
    if vtype == ⊥
        constant = Constant(false)
    elseif elsetype == ⊥
        constant = Constant(true)
    else
        constant = nothing
    end
    conditional = InterConditionalInfo(slot, vtype, elsetype)
    return TypeLattice(Bool; constant, conditional)
end
isConditional(@nospecialize typ) = isa(typ, TypeLattice) && isa(typ.conditional, ConditionalInfo) && typ.conditional !== _TOP_CONDITIONAL_INFO
isInterConditional(@nospecialize typ) = isa(typ, TypeLattice) && isa(typ.conditional, InterConditionalInfo)
isAnyConditional(@nospecialize typ) = isa(typ, TypeLattice) && (isConditional(typ) || isInterConditional(typ))
# access to the `x.conditional` field with improved type instability where
# `isConditional(x)` or `isInterConditional(x)` hold
# TODO once https://github.com/JuliaLang/julia/pull/41199 is merged,
# all usages of this function can be simply replaced with `x.conditional`
@inline conditional(x::TypeLattice) = x.conditional::ConditionalInfo
@inline interconditional(x::TypeLattice) = x.conditional::InterConditionalInfo

function PartialTypeVar(
    tv::TypeVar,
    # N.B.: Currently unused, but could be used to form something like `Constant`
    # if the bounds are pulled out of this `TypeVar`
    lb_certain::Bool, ub_certain::Bool)
    partialtypevar = PartialTypeVarInfo(tv)
    return TypeLattice(TypeVar; partialtypevar)
end
isPartialTypeVar(@nospecialize typ) = isa(typ, TypeLattice) && typ.partialtypevar !== _TOP_PARTIALTYPEVAR_INFO

# Wraps a type and represents that the value may also be undef at this point.
# (only used in optimize, not abstractinterpret)
# N.B. in the lattice, this is epsilon bigger than `typ` (even Any)
struct MaybeUndef <: _AbstractLattice
    typ
    MaybeUndef(@nospecialize(typ)) = new(typ)
end

struct StateUpdate
    var::SlotNumber
    vtype::VarState
    state::VarTable
    conditional::Bool
end

# Represent that the type estimate has been approximated, due to "causes"
# (only used in abstract interpretion, doesn't appear in optimization)
# N.B. in the lattice, this is epsilon smaller than `typ` (except Union{})
struct LimitedAccuracy <: _AbstractLattice
    typ::AbstractLattice
    causes::IdSet{InferenceState}
    @latticeop args function LimitedAccuracy(@nospecialize(typ), causes::IdSet{InferenceState})
        @assert !isa(typ, LimitedAccuracy) "malformed LimitedAccuracy"
        return new(typ, causes)
    end
end

@inline @latticeop args function collect_limitations!(@nospecialize(typ), sv::InferenceState)
    if isa(typ, LimitedAccuracy)
        union!(sv.pclimitations, typ.causes)
        return typ.typ
    end
    return typ
end

"""
    struct NotFound end
    const NOT_FOUND = NotFound()

A special sigleton that represents a variable has not been analyzed yet.
Particularly, all SSA value types are initialized as `NOT_FOUND` when creating a new `InferenceState`.
Note that this is only used for `smerge`, which updates abstract state `VarTable`,
and thus we don't define the lattice for this.
"""
struct NotFound end

const NOT_FOUND = NotFound()

const CompilerTypes = Union{
    MaybeUndef,
    NotFound,
    PartialOpaque,
    LimitedAccuracy,
    TypeofVararg,
}
x::CompilerTypes == y::CompilerTypes = x === y
x::Type == y::CompilerTypes = false
x::CompilerTypes == y::Type = false

x::TypeLattice == y::TypeLattice = x.typ == y.typ
x::TypeLattice == y::CompilerTypes = false
x::CompilerTypes == y::TypeLattice = false
# allow comparison with unwrapped types (TODO remove me, this is just for prototyping)
x::Type == y::TypeLattice = x === unwraptype(y)
x::TypeLattice == y::Type = unwraptype(x) === y

#################
# lattice logic #
#################

# `Conditional` and `InterConditional` are valid in opposite contexts
# (i.e. local inference and inter-procedural call), as such they will never be compared
function issubconditional(a::TypeLattice, b::TypeLattice)
    if is_same_conditionals(a, b)
        a, b = a.conditional, b.conditional
        if a.vtype ⊑ b.vtype
            if a.elsetype ⊑ b.elsetype
                return true
            end
        end
    end
    return false
end

function is_same_conditionals(a::TypeLattice, b::TypeLattice)
    if isConditional(a)
        return is_same_conditionals(conditional(a), conditional(b))
    else
        return is_same_conditionals(interconditional(a), interconditional(b))
    end
end
is_same_conditionals(a::ConditionalInfo, b::ConditionalInfo) = slot_id(a.var) == slot_id(b.var)
is_same_conditionals(a::InterConditionalInfo, b::InterConditionalInfo) = a.slot == b.slot

@latticeop args is_lattice_bool(@nospecialize(typ)) = typ !== ⊥ && typ ⊑ Bool

function maybe_extract_const_bool(x::TypeLattice)
    if isConst(x)
        val = constant(x)
        return isa(val, Bool) ? val : nothing
    end
    cnd = x.conditional
    (cnd.vtype === Bottom && !(cnd.elsetype === Bottom)) && return false
    (cnd.elsetype === Bottom && !(cnd.vtype === Bottom)) && return true
    return nothing
end
maybe_extract_const_bool(@nospecialize c) = nothing

function ⊑(@nospecialize(a), @nospecialize(b))
    a = unwraptype(a)
    b = unwraptype(b)
    if isa(b, LimitedAccuracy)
        if !isa(a, LimitedAccuracy)
            return false
        end
        if b.causes ⊈ a.causes
            return false
        end
        b = b.typ
    end
    isa(a, LimitedAccuracy) && (a = a.typ)
    if isa(a, MaybeUndef) && !isa(b, MaybeUndef)
        return false
    end
    isa(a, MaybeUndef) && (a = a.typ)
    isa(b, MaybeUndef) && (b = b.typ)
    b === Any && return true
    a === Any && return false
    a === Union{} && return true
    b === Union{} && return false
    @assert !isa(a, TypeVar) "invalid lattice item"
    @assert !isa(b, TypeVar) "invalid lattice item"
    if isAnyConditional(a)
        if isAnyConditional(b)
            return issubconditional(a, b)
        elseif isConst(b) && isa(constant(b), Bool)
            return maybe_extract_const_bool(a) === constant(b)
        end
        a = Bool
    elseif isAnyConditional(b)
        return false
    end
    if isPartialStruct(a)
        if isPartialStruct(b)
            if !(length(a.fields) == length(b.fields) && a.typ <: b.typ)
                return false
            end
            for i in 1:length(b.fields)
                # XXX: let's handle varargs later
                ⊑(a.fields[i], b.fields[i]) || return false
            end
            return true
        end
        return isa(b, Type) && a.typ <: b
    elseif isPartialStruct(b)
        if isConst(a)
            aval = constant(a)
            nfields(aval) == length(b.fields) || return false
            widenconst(b).name === widenconst(a).name || return false
            # We can skip the subtype check if b is a Tuple, since in that
            # case, the ⊑ of the elements is sufficient.
            if b.typ.name !== Tuple.name && !(widenconst(a) <: widenconst(b))
                return false
            end
            for i in 1:nfields(aval)
                # XXX: let's handle varargs later
                isdefined(aval, i) || return false
                ⊑(Const(getfield(aval, i)), b.fields[i]) || return false
            end
            return true
        end
        return false
    end
    if isa(a, PartialOpaque)
        if isa(b, PartialOpaque)
            (a.parent === b.parent && a.source === b.source) || return false
            return (widenconst(a) <: widenconst(b)) &&
                ⊑(a.env, b.env)
        end
        return widenconst(a) ⊑ b
    end
    if isConst(a)
        aval = constant(a)
        if isConst(b)
            return aval === constant(b)
        end
        # TODO: `b` could potentially be a `PartialTypeVar` here, in which case we might be
        # able to return `true` in more cases; in the meantime, just returning this is the
        # most conservative option.
        return isa(b, Type) && isa(aval, b)
    elseif isConst(b)
        if isa(a, DataType) && isdefined(a, :instance)
            return a.instance === constant(b)
        end
        return false
    elseif isPartialTypeVar(a) && b === TypeVar
        return true
    elseif isa(a, Type) && isa(b, Type)
        return a <: b
    else # handle this conservatively in the remaining cases
        return a === b
    end
end

# Check if two lattice elements are partial order equivalent. This is basically
# `a ⊑ b && b ⊑ a` but with extra performance optimizations.
function is_lattice_equal(@nospecialize(a), @nospecialize(b))
    # COMBAK this egal comparison is really senseless now
    a === b && return true
    if isPartialStruct(a)
        isPartialStruct(b) || return false
        length(a.fields) == length(b.fields) || return false
        widenconst(a) == widenconst(b) || return false
        for i in 1:length(a.fields)
            is_lattice_equal(a.fields[i], b.fields[i]) || return false
        end
        return true
    end
    isPartialStruct(b) && return false
    if isConst(a)
        isConst(b) && return constant(a) === constant(b)
        if issingletontype(b)
            return constant(a) === b.instance
        end
        return false
    end
    if isConst(b)
        if issingletontype(a)
            return a.instance === constant(b)
        end
        return false
    end
    if isa(a, PartialOpaque)
        isa(b, PartialOpaque) || return false
        widenconst(a) == widenconst(b) || return false
        a.source === b.source || return false
        a.parent === b.parent || return false
        return is_lattice_equal(a.env, b.env)
    end
    return a ⊑ b && b ⊑ a
end

widenconst(x::TypeLattice) = x.typ
widenconst(m::MaybeUndef) = widenconst(m.typ)
widenconst(t::PartialOpaque) = t.typ
widenconst(t::Type) = t
widenconst(t::TypeVar) = t
widenconst(t::Core.TypeofVararg) = t
widenconst(t::LimitedAccuracy) = error("unhandled LimitedAccuracy")

issubstate(a::VarState, b::VarState) = (a.typ ⊑ b.typ && a.undef <= b.undef)

function smerge(sa::Union{NotFound,VarState}, sb::Union{NotFound,VarState})
    sa === sb && return sa
    sa === NOT_FOUND && return sb
    sb === NOT_FOUND && return sa
    issubstate(sa, sb) && return sb
    issubstate(sb, sa) && return sa
    return VarState(tmerge(sa.typ, sb.typ), sa.undef | sb.undef)
end

@inline tchanged(@nospecialize(n), @nospecialize(o)) = o === NOT_FOUND || (n !== NOT_FOUND && !(n ⊑ o))
@inline schanged(@nospecialize(n), @nospecialize(o)) = (n !== o) && (o === NOT_FOUND || (n !== NOT_FOUND && !issubstate(n::VarState, o::VarState)))

widenconditional(@nospecialize typ) = typ
function widenconditional(typ::TypeLattice)
    if isAnyConditional(typ)
        # TODO form new `TypeLattice` with `_TOP_CONDITIONAL_INFO`
        cnd = typ.conditional
        if cnd.vtype === Bottom
            return Const(false)
        elseif cnd.elsetype === Bottom
            return Const(true)
        else
            return NativeType(Bool)
        end
    end
    return typ
end
widenconditional(t::LimitedAccuracy) = error("unhandled LimitedAccuracy")

widenwrappedconditional(@nospecialize(typ))   = widenconditional(typ)
widenwrappedconditional(typ::LimitedAccuracy) = LimitedAccuracy(widenconditional(typ.typ), typ.causes)

ignorelimited(@nospecialize typ) = typ
ignorelimited(typ::LimitedAccuracy) = typ.typ

function stupdate!(state::Nothing, changes::StateUpdate)
    newst = copy(changes.state)
    changeid = slot_id(changes.var)
    newst[changeid] = changes.vtype
    # remove any Conditional for this slot from the vtable
    # (unless this change is came from the conditional)
    if !changes.conditional
        for i = 1:length(newst)
            newtype = newst[i]
            if isa(newtype, VarState)
                newtypetyp = ignorelimited(newtype.typ)
                if isConditional(newtypetyp) && slot_id(conditional(newtypetyp).var) == changeid
                    newtypetyp = widenwrappedconditional(newtype.typ)
                    newst[i] = VarState(newtypetyp, newtype.undef)
                end
            end
        end
    end
    return newst
end

function stupdate!(state::VarTable, changes::StateUpdate)
    newstate = nothing
    changeid = slot_id(changes.var)
    for i = 1:length(state)
        if i == changeid
            newtype = changes.vtype
        else
            newtype = changes.state[i]
        end
        oldtype = state[i]
        # remove any Conditional for this slot from the vtable
        # (unless this change is came from the conditional)
        if !changes.conditional && isa(newtype, VarState)
            newtypetyp = ignorelimited(newtype.typ)
            if isConditional(newtypetyp) && slot_id(conditional(newtypetyp).var) == changeid
                newtypetyp = widenwrappedconditional(newtype.typ)
                newtype = VarState(newtypetyp, newtype.undef)
            end
        end
        if schanged(newtype, oldtype)
            newstate = state
            state[i] = smerge(oldtype, newtype)
        end
    end
    return newstate
end

function stupdate!(state::VarTable, changes::VarTable)
    newstate = nothing
    for i = 1:length(state)
        newtype = changes[i]
        oldtype = state[i]
        if schanged(newtype, oldtype)
            newstate = state
            state[i] = smerge(oldtype, newtype)
        end
    end
    return newstate
end

stupdate!(state::Nothing, changes::VarTable) = copy(changes)

stupdate!(state::Nothing, changes::Nothing) = nothing

function stupdate1!(state::VarTable, change::StateUpdate)
    changeid = slot_id(change.var)
    # remove any Conditional for this slot from the catch block vtable
    # (unless this change is came from the conditional)
    if !change.conditional
        for i = 1:length(state)
            oldtype = state[i]
            if isa(oldtype, VarState)
                oldtypetyp = ignorelimited(oldtype.typ)
                if isConditional(oldtypetyp) && slot_id(conditional(oldtypetyp).var) == changeid
                    oldtypetyp = widenconditional(oldtypetyp)
                    if oldtype.typ isa LimitedAccuracy
                        oldtypetyp = LimitedAccuracy(oldtypetyp, (oldtype.typ::LimitedAccuracy).causes)
                    end
                    state[i] = VarState(oldtypetyp, oldtype.undef)
                end
            end
        end
    end
    # and update the type of it
    newtype = change.vtype
    oldtype = state[changeid]
    if schanged(newtype, oldtype)
        state[changeid] = smerge(oldtype, newtype)
        return true
    end
    return false
end
