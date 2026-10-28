module
public import Theory.GroupTheory.InvolutionFusionCover
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The two involution class bounds for dihedral central extensions

Thompson transfer into an index-two subgroup bounds the size of a family of
pairwise nonconjugate involutions by the number of classes in that subgroup.
A dihedral eight whose involutions fuse has one class; adjoining a commuting
involution gives at most five classes. Consequently an elementary subgroup
with no fusion has order at most two or six in the respective cases.

These are the successive-transfer obstructions in Aschbacher--Smith F.5.5,
printed p.302: they exclude residual Sylow orders16 and32 once the original
endpoint dihedral subgroup and Sylow-center marking are supplied.
-/

public noncomputable section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]
theorem card_nonfused_involutions_le_of_index_two_cover {α ι : Type*} [Finite ι] (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (V : Subgroup S) (hV : V.index=2) (r : ι → G)
    (hcover : ∀ v : S, v ∈ V → orderOf (v:G)=2 → ∃ j, IsConj (r j) (v:G))
    (x : α → G) (hX : ∀ a, orderOf (x a)=2)
    (hsep : ∀ a b, IsConj (x a) (x b) → a=b) : Nat.card α ≤ Nat.card ι := by
  classical
  have hex (a:α) : ∃ j, IsConj (r j) (x a) := by
    obtain ⟨v,hv,hxv⟩ := S.exists_isConj_mem_of_index_two_ambient hno V hV (x a) (hX a)
    have hv2 : orderOf (v:G)=2 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hxv
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq (x a)).trans (hX a)
    obtain ⟨j,hj⟩ := hcover v hv hv2
    exact ⟨j,hj.trans hxv.symm⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b he
    apply hsep a b
    exact (hf a).symm.trans (he ▸ hf b)
  exact Nat.card_le_card_of_injective f hinj
theorem elementary_card_le_of_index_two_class_cover {ι : Type*} [Finite ι] (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (V : Subgroup S) (hV : V.index=2) (r : ι → G)
    (hcover : ∀ v : S, v ∈ V → orderOf (v:G)=2 → ∃ j, IsConj (r j) (v:G))
    (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hsep : ∀ x∈Z, ∀ y∈Z, IsConj x y → x=y) : Nat.card Z ≤ Nat.card ι+1 := by
  classical
  let X := {z:Z // z≠1}
  have hh := card_nonfused_involutions_le_of_index_two_cover S hno V hV r hcover (fun x:X => x.val.val)
    (fun x => orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x.val.val x.val.property)
      (fun hx => x.property (Subtype.ext hx)))
    (fun x y hc => Subtype.ext (Subtype.ext (hsep _ x.val.property _ y.val.property hc)))
  have hcard : Nat.card X=Nat.card Z-1 := by
    let := Fintype.ofFinite Z
    change Nat.card {z:Z // ¬z=1}=Nat.card Z-1
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_unique]
  have hp := Nat.card_pos (α:=Z)
  omega
end Sylow

namespace DihedralCentralExtensionTransfer
local notation "D" => DihedralGroup 4
private theorem four_classes : ∀ d:D, d^2=1 →
    d=1 ∨ d=DihedralGroup.r 2 ∨
      (∃ a:D,a*DihedralGroup.sr 0*a⁻¹=d) ∨
      (∃ a:D,a*DihedralGroup.sr 1*a⁻¹=d) := by decide +kernel
theorem five_class_cover {G : Type*} [Group G] (j : D →* G) (hj : Function.Injective j)
    (u z : G) (hz : z^2=1) (hc : ∀ d:D, Commute z (j d))
    (hf : ∀ d:D, orderOf d=2 → IsConj u (j d)) :
    ∃ r : Fin 5 → G, ∀ x:G, (∃ d:D,x=j d ∨ x=z*j d) →
      orderOf x=2 → ∃ k:Fin 5, IsConj (r k) x := by
  let r : Fin 5 → G := fun n => if n=0 then u else if n=1 then z else
    if n=2 then z*j (DihedralGroup.r 2) else if n=3 then z*j (DihedralGroup.sr 0)
      else z*j (DihedralGroup.sr 1)
  refine ⟨r,?_⟩
  intro x hx ho
  obtain ⟨d,hd|hd⟩ := hx
  · subst x
    exact ⟨0,by simpa [r] using hf d ((orderOf_injective j hj d).symm.trans ho)⟩
  · subst x
    have hs : (z*j d)^2=1 := ho ▸ pow_orderOf_eq_one _
    have hd2 : d^2=1 := by
      apply hj
      rw [map_pow,map_one]
      rw [(hc d).mul_pow,hz,one_mul] at hs
      exact hs
    have lift (v a:D) (ha:a*v*a⁻¹=d) : IsConj (z*j v) (z*j d) := by
      apply isConj_iff.mpr
      refine ⟨j a,?_⟩
      rw [←mul_assoc, (hc a).eq.symm]
      rw [mul_assoc,mul_assoc,←map_inv,←map_mul,←map_mul,←mul_assoc,ha]
    rcases four_classes d hd2 with h1|h2|⟨a,ha⟩|⟨a,ha⟩
    · exact ⟨1,by simpa [r,h1] using IsConj.refl z⟩
    · exact ⟨2,by simpa [r,h2] using IsConj.refl (z*j (DihedralGroup.r 2))⟩
    · exact ⟨3,by simpa [r] using lift (DihedralGroup.sr 0) a ha⟩
    · exact ⟨4,by simpa [r] using lift (DihedralGroup.sr 1) a ha⟩
end DihedralCentralExtensionTransfer

namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A fused index-two dihedral core excludes extra nonfused elementary involutions. -/
theorem elementary_card_le_two_of_fused_index_two (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (V : Subgroup S) (hV : V.index=2) (u : G)
    (hcover : ∀ v : S, v ∈ V → orderOf (v:G)=2 → IsConj u (v:G))
    (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hsep : ∀ x∈Z, ∀ y∈Z, IsConj x y → x=y) : Nat.card Z ≤ 2 := by
  simpa using S.elementary_card_le_of_index_two_class_cover hno V hV
    (fun _ : Fin 1 => u) (fun v hv ho => ⟨0,hcover v hv ho⟩) Z hsep

/-- A central involution extension of a fused dihedral core has at most five
classes, excluding seven pairwise nonfused central involutions. -/
theorem elementary_card_le_six_of_dihedral_extension (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (V : Subgroup S) (hV : V.index=2)
    (j : DihedralGroup 4 →* G) (hj : Function.Injective j)
    (u z : G) (hz : z^2=1) (hc : ∀ d, Commute z (j d))
    (hf : ∀ d, orderOf d=2 → IsConj u (j d))
    (hcover : ∀ v : S, v ∈ V → ∃ d, (v:G)=j d ∨ (v:G)=z*j d)
    (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hsep : ∀ x∈Z, ∀ y∈Z, IsConj x y → x=y) : Nat.card Z ≤ 6 := by
  obtain ⟨r,hr⟩ := DihedralCentralExtensionTransfer.five_class_cover j hj u z hz hc hf
  simpa using S.elementary_card_le_of_index_two_class_cover hno V hV r
    (fun v hv ho => hr v (hcover v hv) ho) Z hsep

end Sylow
