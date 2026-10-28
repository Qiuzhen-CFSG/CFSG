module

public import Theory.Order.UniqueMaximalOver
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Characteristic control below a unique maximal Sylow overgroup

If no nontrivial characteristic subgroup of S is normal in the ambient
group, every defining characteristic normalizer is proper and contains S.
Unique maximality puts their join in the same proper subgroup. This is
the intrinsic version of the original C.5.3 control argument, also used
by the minimal-parabolic source assembly in E.2.3.

Source: Aschbacher–Smith C.1.26–29 and C.5.3, pp.132–134 and154–155.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]

theorem characteristic_control_le_unique_maximal (S N : Subgroup G)
    (hu : Order.HasUniqueMaximalOver S ⊤) (hN : S ≤ N ∧ IsCoatom N)
    (hno : ∀ C : Subgroup S, C.Characteristic → C ≠ ⊥ → ¬ (C.map S.subtype).Normal) :
    S.characteristicNormalizerClosure ≤ N := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hCne
  let := hC
  apply hu.le_maximal ⟨hN.1,hN.2.covBy_top⟩
    (S.le_normalizer.trans (normalizer_le_normalizer_characteristic_image S C))
  exact lt_top_iff_ne_top.mpr (fun he => hno C hC hCne (normalizer_eq_top_iff.mp he))

theorem characteristic_control_ne_top_of_unique_maximal (S : Subgroup G)
    (hu : Order.HasUniqueMaximalOver S ⊤)
    (hno : ∀ C : Subgroup S, C.Characteristic → C ≠ ⊥ → ¬ (C.map S.subtype).Normal) :
    S.characteristicNormalizerClosure ≠ ⊤ := by
  obtain ⟨N,hN,_⟩ := hu.2
  have hh := characteristic_control_le_unique_maximal S N hu ⟨hN.1,hN.2.isCoatom⟩ hno
  intro he
  rw [he] at hh
  exact hN.2.ne (top_unique hh)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
