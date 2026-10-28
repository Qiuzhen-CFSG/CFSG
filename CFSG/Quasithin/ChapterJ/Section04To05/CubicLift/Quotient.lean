module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Elementary
public import Theory.GroupTheory.InvertedThreePreimage

/-!
# The original second parabolic over S₃

The original Ru1 quotient identifies G₂/S with S₄. Composing its restriction
with the quotient by the intrinsic four-core gives a surjection to S₃ with
kernel exactly R₂. The same original map counts G₂ and its Sylow three-subgroups.
These provide the quotient inputs for the Sylow selection in J.4.4(5).

Source: Aschbacher–Smith, J.4.4, printed p.441.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The actual second parabolic has order 2¹⁴·3. -/
theorem Plane.card_parabolic : Nat.card p.parabolic = 49152 := by
  have h := p.parabolicMap.ker.index_mul_card
  rw [index_ker,p.parabolicMap_kernel,
    Nat.card_congr (subgroupOfEquivOfLe p.S_le_parabolic).toEquiv,d.ru1.card_S,
    Nat.card_congr p.parabolicImageEquivS4.toEquiv] at h
  have h4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  rw [h4] at h
  omega

/-- The source Sylow three-subgroups all have order three. -/
theorem Plane.card_sylow_three (X : Sylow 3 p.parabolic) : Nat.card X = 3 := by
  rw [X.card_eq_multiplicity,p.card_parabolic,show 49152 = 2 ^ 14 * 3 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]

/-- The original parabolic restriction followed by the four-core quotient. -/
def Plane.cubicMap : p.parabolic →* Equiv.Perm (Fin 3) :=
  (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv p.parabolicImageEquivS4).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 p.parabolicMap.range)).comp p.parabolicMap.rangeRestrict)

theorem Plane.cubicMap_surjective : Function.Surjective p.cubicMap :=
  (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv p.parabolicImageEquivS4).surjective.comp
    ((QuotientGroup.mk'_surjective _).comp p.parabolicMap.rangeRestrict_surjective)

/-- The literal kernel is the source subgroup R₂, restricted to G₂. -/
theorem Plane.cubicMap_kernel : p.cubicMap.ker = p.R₂.subgroupOf p.parabolic := by
  have hk : IsPGroup 2 p.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,p.parabolicMap_kernel]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  have hc := p.parabolicMap.rangeRestrict.comap_pCore_of_ker_isPGroup
    p.parabolicMap.rangeRestrict_surjective hk
  have hr : p.R₂.subgroupOf p.parabolic = pCore 2 p.parabolic := by
    rw [p.R₂_eq,pCoreIn]
    exact comap_map_eq_self_of_injective p.parabolic.subtype_injective _
  rw [hr]
  ext a
  change Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv p.parabolicImageEquivS4
    (QuotientGroup.mk' (pCore 2 p.parabolicMap.range) (p.parabolicMap.rangeRestrict a)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff _).trans (by
    change a ∈ (pCore 2 p.parabolicMap.range).comap p.parabolicMap.rangeRestrict ↔ _
    rw [hc])

end CFSG.Quasithin.ChapterJ.RuSubgroup
