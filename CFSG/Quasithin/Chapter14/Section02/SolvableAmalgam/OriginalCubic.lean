module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.CubicRigidity
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.DerivedG2Recognition
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.MathieuRecognition
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullG2Exclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.AutMathieuExclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallIndexSource

/-!
# The original cubic case of 14.2.20

The actual source pair is one of the four correctly oriented cubic amalgams.
Original 14.2.21 identifies its first vertex with the central involution
centralizer and its second vertex with M. The full G₂ and outer Mathieu
rows contradict transfer in the simple ambient group. The two inner rows
are recognized from their actual involution centralizers, giving precisely
M₁₂ or G₂(2)′. The final application takes an original outside overgroup
of Sylow index three and constructs its symmetric-three quotient.

Source: Aschbacher--Smith 14.2.20(2), 14.2.21--22 and 14.3.5,
printed pp.988--991.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.GreenBook ChapterF.SourceAssembly ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

/-- Original 14.2.20(2), with both ambient groups recognized. -/
theorem source_cubic_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    Nonempty (G ≃* Sporadic.Mathieu.M12) ∨
      Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  let : IsSimpleGroup G := hG.simple
  have c := SmallLocal.cubic_source_context hG T hempty hM hu hmany hcard e H hH eH
  obtain ⟨hHM,hMX⟩ := source_cubic_rigidity hG T hempty hM hu hmany hcard e H hH eH
  have hHC := hHM.trans c.Mc_centralizer
  have hm := SmallLocal.source_cubic_oriented_amalgam hG T hempty hM hu hmany hcard e H hH eH
  rcases hm with hd | hf | hm | ha
  · exact Or.inr (derived_g2_recognition T H _ c.intersection c.mark_card hHC hd)
  · exact (full_g2_exclusion T H _ c.intersection c.mark_card hHC hf).elim
  · exact Or.inl (mathieu_twelve_recognition T H _ c.intersection c.mark_card hHC hm)
  · exact (source_autMathieu_exclusion hG T hempty hM hu hmany hcard e H hH
      (Or.inr (Or.inr ⟨eH⟩)) hMX ha).elim

/-- The cubic quotient supplies an actual Theorem E model. -/
theorem source_theoremE_of_cubic_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    ClassificationModels.IsTheoremEModel G := by
  rcases source_cubic_recognition hG T hempty hM hu hmany hcard e H hH eH with hm | hg
  · exact .mathieu_twelve hm
  · exact .g2_derived hg

/-- The original small-index consumer for index three, including its quotient. -/
theorem source_theoremE_of_index_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G)) (hout : ¬ H ≤ M)
    (hi : (T : Subgroup G).relIndex H = 3) :
    ClassificationModels.IsTheoremEModel G := by
  obtain ⟨hmin,_⟩ := source_small_index_models hG T hempty hM hu hmany hcard e H hH hout (Or.inl hi)
  let S := T.subtype hH.2
  have hN : normalizer (T : Set G) ≤ M :=
    (source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e).trans inf_le_left
  have hproper : pCore 2 H < (S : Subgroup H) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
    intro he
    have hn : ((T : Subgroup G).subgroupOf H).Normal := by
      change (S : Subgroup H).Normal
      rw [←he]
      infer_instance
    exact hout (((normal_subgroupOf_iff_le_normalizer hH.2).mp hn).trans hN)
  obtain ⟨f⟩ := sylow_index_three_core_quotient S hi hproper
  exact source_theoremE_of_cubic_quotient hG T hempty hM hu hmany hcard e H hmin f

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
