module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import Mathlib.GroupTheory.IndexNormal

/-!
# The degree-six quotient in a Goldschmidt amalgam

The opposite local two-core has index six in either vertex. Its normal core
is a normal two-subgroup, hence lies in the vertex's own two-core. The
faithful action of the quotient on six cosets bounds its order by 48:
its order divides 6!, while its own normal two-subgroup has index six.

This isolates the literal local kernel whose order must be controlled in
the characteristic-two branch of Aschbacher–Smith F.6.5, printed p.305.
It proves no bound on that kernel and assumes no classification alternative.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The opposite two-core has index six inside the original left vertex. -/
theorem IsGoldschmidtTriple.opposite_core_index_six
    (h : IsGoldschmidtTriple G₁ G₂) :
    (((pCore 2 G₂).map G₂.subtype).subgroupOf G₁).index = 6 := by
  let R := ((pCore 2 G₂).map G₂.subtype).subgroupOf G₁
  have hle : (pCore 2 G₂).map G₂.subtype ≤ G₁ := by
    exact (h.symm.local_twoCore_le_intersection.trans inf_le_right)
  have hR : Nat.card R = Nat.card (pCore 2 G₂) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact (Nat.card_congr ((pCore 2 G₂).equivMapOfInjective G₂.subtype G₂.subtype_injective).toEquiv).symm
  have hg : Nat.card G₁ = Nat.card G₂ := by
    rw [h.local_card_eq_three_mul_intersection,h.symm.local_card_eq_three_mul_intersection,
      inf_comm G₂ G₁]
  have hc := R.index_mul_card
  rw [hR,hg,SymmetricThreeTwoCore.card_eq h.quotient_right.some] at hc
  have hp := Nat.card_pos (α := pCore 2 G₂)
  change R.index = 6
  nlinarith

/-- The actual degree-six kernel lies inside the original vertex two-core. -/
theorem IsGoldschmidtTriple.opposite_core_normalCore_le_twoCore
    (_h : IsGoldschmidtTriple G₁ G₂) :
    (((pCore 2 G₂).map G₂.subtype).subgroupOf G₁).normalCore ≤ pCore 2 G₁ := by
  let R := ((pCore 2 G₂).map G₂.subtype).subgroupOf G₁
  have hp : IsPGroup 2 R := (pCore_isPGroup (p := 2) (G := G₂)).map G₂.subtype
    |>.comap_of_injective G₁.subtype G₁.subtype_injective
  exact le_sSup ⟨inferInstance,hp.to_le R.normalCore_le⟩

/-- The quotient by the literal opposite-core kernel has order dividing 48. -/
theorem IsGoldschmidtTriple.opposite_core_normalCore_index_dvd_forty_eight
    (h : IsGoldschmidtTriple G₁ G₂) :
    (((pCore 2 G₂).map G₂.subtype).subgroupOf G₁).normalCore.index ∣ 48 := by
  let R := ((pCore 2 G₂).map G₂.subtype).subgroupOf G₁
  let N := R.normalCore
  let q := QuotientGroup.mk' N
  let Q := (pCore 2 G₁).map q
  have hiQ : Q.index = 6 := by
    rw [index_map_eq (pCore 2 G₁) (QuotientGroup.mk'_surjective N)
      (by rw [QuotientGroup.ker_mk']; exact h.opposite_core_normalCore_le_twoCore)]
    change Nat.card (G₁ ⧸ pCore 2 G₁) = 6
    rw [Nat.card_congr h.quotient_left.some.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  obtain ⟨n,hn⟩ := ((pCore_isPGroup (p := 2) (G := G₁)).map q).exists_card_eq
  have hquot : N.index = 6 * 2 ^ n := by
    have hc := Q.index_mul_card
    rw [hiQ,hn] at hc
    exact hc.symm
  have hdiv : N.index ∣ 720 := by
    have hd : N.index ∣ R.index.factorial := by
      change R.normalCore.index ∣ R.index.factorial
      rw [normalCore_eq_ker,index_ker,index_eq_card,← Nat.card_perm]
      exact card_subgroup_dvd_card (MulAction.toPermHom G₁ (G₁ ⧸ R)).range
    rw [h.opposite_core_index_six] at hd
    norm_num [Nat.factorial] at hd
    exact hd
  have hd : 2 ^ n ∣ 120 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 6)).mp
    simpa only [hquot] using hdiv
  have hc : (2 ^ n).Coprime 15 := (by decide : Nat.Coprime 2 15).pow_left n
  have hd8 : 2 ^ n ∣ 8 := hc.dvd_of_dvd_mul_right (show 2 ^ n ∣ 8 * 15 from hd)
  rw [hquot]
  exact Nat.mul_dvd_mul_left 6 hd8

/-- The original vertex order is at most 48 times its degree-six kernel. -/
theorem IsGoldschmidtTriple.local_card_le_forty_eight_mul_opposite_core_kernel
    (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card G₁ ≤ 48 * Nat.card
      (((pCore 2 G₂).map G₂.subtype).subgroupOf G₁).normalCore := by
  let N := (((pCore 2 G₂).map G₂.subtype).subgroupOf G₁).normalCore
  have hi : N.index ≤ 48 :=
    Nat.le_of_dvd (by decide) h.opposite_core_normalCore_index_dvd_forty_eight
  rw [← N.index_mul_card]
  exact Nat.mul_le_mul_right _ hi

/-- The same degree-six quotient calculation on the literal images in G/O₂(G). -/
theorem IsGoldschmidtTriple.quotient_opposite_core_normalCore_index_dvd_forty_eight
    (h : IsGoldschmidtTriple G₁ G₂) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let A := G₁.map q
    let B := G₂.map q
    (((pCore 2 B).map B.subtype).subgroupOf A).normalCore.index ∣ 48 :=
  h.quotient_twoCore.opposite_core_normalCore_index_dvd_forty_eight

end CFSG.Quasithin.ChapterF
