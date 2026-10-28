module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
import all Theory.SpecificGroups.AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
/-!
# An involution outside Q₈ does not centralize Q₈ in Aut(A₆)

If it did centralize the quaternion subgroup, the two would lie in one
Sylow subgroup. The marked holomorph table has only the identity and
quaternion central involution among the involutions centralizing Q₈.
Transport through the actual Sylow equivalence therefore gives a
contradiction. The private quaternion-range calculation of the parent
module is reused internally through `import all`.

Source application: Aschbacher--Smith J.2.7(8), printed p.437, for the
two-element quaternion orbit in the original H-transitivity proof.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
open Holomorph
private abbrev qembedding := M10.LocalGeometry.Coordinates.quaternionEmbedding

set_option maxRecDepth 10000 in
private theorem centralizing_involution_table (r:Model) (hr:r^2=1)
    (hc:∀q:QuaternionGroup 2,r*qembedding q=qembedding q*r) :
    ∃q:QuaternionGroup 2,qembedding q=r := by
  revert r
  decide +kernel

/-- An involution outside an embedded quaternion group cannot centralize it
in the actual automorphism group of A₆. -/
theorem exists_quaternion_noncommuting (Q:Subgroup AutA6)
    (hQ:Nonempty (Q≃*QuaternionGroup 2)) (β:AutA6) (hβ:orderOf β=2)
    (hβQ:β∉Q) : ∃q:Q,β*(q:AutA6)≠(q:AutA6)*β := by
  by_contra! hc
  obtain ⟨eQ⟩:=hQ
  have hβC : β∈centralizer (Q:Set AutA6) := fun q hq => (hc ⟨q,hq⟩).symm
  have hβN := (Subgroup.centralizer_le_normalizer _) hβC
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n:=3) (by
    rw [Nat.card_congr eQ.toEquiv,Nat.card_eq_fintype_card];decide +kernel)
  have hβp : IsPGroup 2 (zpowers β) := IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,hβ,pow_one])
  obtain ⟨T,hT⟩:=(hQp.to_sup_of_normal_left' hβp (zpowers_le.mpr hβN)).exists_le_sylow
  have hQT : Q≤(T:Subgroup AutA6):=le_sup_left.trans hT
  have hβT : β∈T:=hT (mem_sup_right (mem_zpowers β))
  let e:=Identification.sylowEquiv T
  let b:T:=⟨β,hβT⟩
  let f:QuaternionGroup 2→*Model:=e.symm.toMonoidHom.comp ((inclusion hQT).comp eQ.symm.toMonoidHom)
  have hf:Function.Injective f:=e.symm.injective.comp ((inclusion_injective hQT).comp eQ.symm.injective)
  have hR:=range_eq f hf
  have hb2 : (e.symm b)^2=1 := by
    rw [←map_pow,show b^2=1 from Subtype.ext (orderOf_eq_prime_iff.mp hβ).1,map_one]
  have hbc (q:QuaternionGroup 2) : e.symm b*qembedding q=qembedding q*e.symm b := by
    have hq:qembedding q∈f.range:=hR.symm ▸ ⟨q,rfl⟩
    obtain ⟨a,ha⟩:=hq
    rw [←ha]
    have hh : b*inclusion hQT (eQ.symm a)=inclusion hQT (eQ.symm a)*b:=Subtype.ext (hc (eQ.symm a))
    exact (map_mul e.symm _ _).symm.trans ((congrArg e.symm hh).trans (map_mul e.symm _ _))
  have hbR : e.symm b∈f.range := hR.symm ▸ centralizing_involution_table (e.symm b) hb2 hbc
  obtain ⟨a,ha⟩:=hbR
  have he:=congrArg (fun x:Model => (e x:AutA6)) ha
  change (e (e.symm (inclusion hQT (eQ.symm a))):AutA6)=(e (e.symm b):AutA6) at he
  simp only [e.apply_symm_apply] at he
  change (eQ.symm a:AutA6)=β at he
  exact hβQ (he ▸ (eQ.symm a).property)

end AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
