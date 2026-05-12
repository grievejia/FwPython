import FwPython.Gradual.MRO.Lookup
import FwPython.Common.MRO.Properties

/-! ## Gradual method lookup metatheory -/

theorem findGMethodInMro_provenance
    (h : findGMethodInMro ct mro methodName = some m) :
    ∃ dname d, dname ∈ mro ∧ findGClass ct dname = some d ∧ m ∈ d.methods :=
  findMethodInMro_provenance h

theorem findGMethodInMro_name
    (h : findGMethodInMro ct mro mname = some m) : m.name = mname :=
  findMethodInMro_name h

theorem findGMethodInMro_first_definer
    {ct : GClassTable} {mro : List Identifier} {methodName : Identifier} {m : GMethod}
    (h : findGMethodInMro ct mro methodName = some m) :
    ∃ pre definerName suf d,
      mro = pre ++ definerName :: suf ∧
        findGClass ct definerName = some d ∧
        findGMethodInList d.methods methodName = some m ∧
        (∀ cname ∈ pre, ∀ gc, findGClass ct cname = some gc →
          findGMethodInList gc.methods methodName = none) :=
  findMethodInMro_first_definer h

theorem findGMethodInMro_first_definer_unique
    {mro : List Identifier}
    {prefix₁ prefix₂ suffix₁ suffix₂ : List Identifier}
    {definer₁ definer₂ methodName : Identifier}
    {d₁ d₂ : GClass} {m₁ m₂ : GMethod}
    (h₁ : mro = prefix₁ ++ definer₁ :: suffix₁)
    (hprefix₁ : ∀ cname ∈ prefix₁, ∀ gc, findGClass ct cname = some gc →
      findGMethodInList gc.methods methodName = none)
    (hfind₁ : findGClass ct definer₁ = some d₁)
    (hmethod₁ : findGMethodInList d₁.methods methodName = some m₁)
    (h₂ : mro = prefix₂ ++ definer₂ :: suffix₂)
    (hprefix₂ : ∀ cname ∈ prefix₂, ∀ gc, findGClass ct cname = some gc →
      findGMethodInList gc.methods methodName = none)
    (hfind₂ : findGClass ct definer₂ = some d₂)
    (hmethod₂ : findGMethodInList d₂.methods methodName = some m₂) :
    definer₁ = definer₂ :=
  findMethodInMro_first_definer_unique h₁ hprefix₁ hfind₁ hmethod₁ h₂ hprefix₂ hfind₂ hmethod₂

theorem findGMethodInMro_of_ancestor
    {ct : GClassTable} {cls : GClass} {mro : List Identifier}
    (hmro : GComputeMro ct cls mro)
    (hfc : findGClass ct cls.name = some cls)
    {aname : Identifier} (hmem : aname ∈ mro)
    {acls : GClass} {amro : List Identifier}
    (hfa : findGClass ct aname = some acls)
    (hmroa : GComputeMro ct acls amro)
    {mname : Identifier} {m : GMethod}
    (hmethod : findGMethodInMro ct amro mname = some m) :
    ∃ m', findGMethodInMro ct mro mname = some m' :=
  findMethodInMro_of_ancestor hmro hfc hmem hfa hmroa hmethod

theorem gMethod_in_receiver_mro_of_lookup
    {ct : GClassTable} {recvClass : Identifier} {recvCls : GClass}
    {recvMro : List Identifier} {attrName : Identifier} {m : GMethod}
    (hfind : findGClass ct recvClass = some recvCls)
    (hmro : GComputeMro ct recvCls recvMro)
    (hlookup : findGMethodInMro ct recvMro attrName = some m) :
    GMethodInReceiverMro ct recvClass m :=
  method_in_receiver_mro_of_lookup hfind hmro hlookup
