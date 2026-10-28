module

public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# An extraspecial factor for a Frattini subgroup of order two

For a finite nonabelian two-group, lift a complement to the center image in
its elementary Frattini quotient. The lift generates the group with its
center and meets that center in the Frattini subgroup. Consequently its
intrinsic center and Frattini subgroup are exactly the marked subgroup of
order two, and the lift is extraspecial.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 12.8.8(1), printed pp.851–852; this is its intrinsic group argument.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsPGroup
variable {Q : Type*} [Group Q] [Finite Q]

/-- The factor retains its actual embedding and its embedded Frattini subgroup. -/
public theorem exists_extraspecial_factor_of_frattini_card_two (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hnonab : ¬ IsMulCommutative Q) :
    ∃ F : Subgroup Q, IsExtraspecial 2 F ∧ F ⊔ center Q = ⊤ ∧
      (frattini F).map F.subtype = frattini Q := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let V := Q ⧸ frattini Q
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini Q)
  let R := (center Q).map q
  obtain ⟨W, hW⟩ := IsElementaryAbelian.exists_isCompl 2 V R
  let F := W.comap q
  have hNZ : frattini Q ≤ center Q := central_of_normal_card_two _ hphi
  have hNF : frattini Q ≤ F := by
    intro x hx
    change q x ∈ W
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [hxq]
    exact W.one_mem
  have hR : R.comap q = center Q := by
    change ((center Q).map q).comap q = _
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNZ]
  have hgen : F ⊔ center Q = ⊤ := by
    rw [← hR]
    change W.comap q ⊔ R.comap q = ⊤
    rw [comap_sup_eq q W R (QuotientGroup.mk'_surjective _),
      hW.symm.sup_eq_top, comap_top]
  have hmeet : F ⊓ center Q = frattini Q := by
    rw [← hR]
    change W.comap q ⊓ R.comap q = _
    rw [← comap_inf, hW.symm.inf_eq_bot, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hcenter : center F = (frattini Q).subgroupOf F := by
    ext x
    constructor
    · intro hx
      have hcentral : (x : Q) ∈ center Q := by
        apply mem_center_iff.mpr
        intro y
        have hy : y ∈ F ⊔ center Q := by rw [hgen]; trivial
        obtain ⟨f, hf, z, hz, rfl⟩ := mem_sup_of_normal_right.mp hy
        have hfx : f * (x : Q) = (x : Q) * f :=
          congrArg Subtype.val (mem_center_iff.mp hx ⟨f, hf⟩)
        have hzx : z * (x : Q) = (x : Q) * z := (mem_center_iff.mp hz x).symm
        calc
          (f * z) * (x : Q) = f * ((x : Q) * z) := by rw [mul_assoc, hzx]
          _ = (x : Q) * (f * z) := by rw [← mul_assoc, hfx, mul_assoc]
      exact show (x : Q) ∈ frattini Q from hmeet ▸ ⟨x.property, hcentral⟩
    · intro hx
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp (hNZ hx) y)
  have hquot : IsElementaryAbelian 2 (Q ⧸ center Q) :=
    elementary_quotient_of_frattini_le htwo (center Q) hNZ
  have hnontrivial : Nontrivial (F ⧸ center F) := by
    apply QuotientGroup.nontrivial_iff.mpr
    intro ht
    have hFZ : F ≤ center Q := by
      intro x hx
      have hxcenter : (⟨x, hx⟩ : F) ∈ center F := by rw [ht]; trivial
      rw [hcenter] at hxcenter
      exact hNZ hxcenter
    exact hnonab (center_eq_top_iff.mp (by simpa [sup_eq_right.mpr hFZ] using hgen))
  let hex : IsExtraspecial 2 F := {
    center_order_p := by
      rw [hcenter, Nat.card_congr (subgroupOfEquivOfLe hNF).toEquiv, hphi]
    quotient_elementary_abelian := hquot.central_quotient_subgroup F
    quotient_nontrivial := hnontrivial }
  refine ⟨F, hex, hgen, ?_⟩
  rw [IsExtraspecial.frattini_eq_center (p := 2), hcenter,
    map_subgroupOf_eq_of_le hNF]

end IsPGroup
