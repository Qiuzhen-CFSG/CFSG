module

public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceReconstruction
public import Theory.GroupTheory.Amalgam.ParabolicRecognition

/-!
# The cubic size bound from the original local Sylows

The two parabolics share a Sylow subgroup locally; their join need not
have that subgroup as an ambient Sylow. Their literal inclusion maps and
trivial generated two-core give a primitive cubic amalgam. On its universal
tree, the characteristic-two hypotheses exclude the cubic residuals, and
the small alternating residual argument excludes an overlap of order at
least 64. The existing geometric source cuts then recognize the normal
base and bound the original marked overlap by 128.

This supplies exactly `CubicF112SizeInput` used in the zero-core case of
14.6.6(6). The four earlier Gol80 source cuts remain explicit, without an
extra ambient-Sylow premise.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Theorem A
and Sections 3--6; Aschbacher--Smith, F.1.12 and 14.6.6(6), pp.263,1024.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source
open SourceAssembly SourceAssembly.Goldschmidt GreenBook RankTwoAmalgam
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual local Sylows give a primitive inclusion amalgam. -/
theorem primitiveCubic_of_local_sylows (A S B : Subgroup G)
    (hSA : Chapter1.IsSylowIn 2 S A) (hSB : Chapter1.IsSylowIn 2 S B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hcore : pCore 2 (A ⊔ B : Subgroup G) = ⊥) :
    PrimitiveCubic (ofSubgroups A S B
      (Chapter1.isSylowIn_iff.mp hSA).2.1
      (Chapter1.isSylowIn_iff.mp hSB).2.1) := by
  let h₁ := (Chapter1.isSylowIn_iff.mp hSA).2.1
  let h₂ := (Chapter1.isSylowIn_iff.mp hSB).2.1
  let α := ofSubgroups A S B h₁ h₂
  have hleft : ∃ P : Sylow 2 A, (P : Subgroup A) = α.left.range := by
    obtain ⟨P,hP⟩ := hSA
    refine ⟨P, ?_⟩
    apply map_injective A.subtype_injective
    rw [hP, ← MonoidHom.range_comp]
    exact (range_subtype S).symm
  have hright : ∃ P : Sylow 2 B, (P : Subgroup B) = α.right.range := by
    obtain ⟨P,hP⟩ := hSB
    refine ⟨P, ?_⟩
    apply map_injective B.subtype_injective
    rw [hP, ← MonoidHom.range_comp]
    exact (range_subtype S).symm
  refine ⟨⟨inclusion_injective h₁, inclusion_injective h₂, hleft, hright⟩,
    faithful_ofSubgroups_of_pCore_eq_bot A S B h₁ h₂
      (Chapter1.isSylowIn_iff.mp hSA).1 hcore, ?_, ?_⟩
  · obtain ⟨P,hP⟩ := hleft
    rw [← hP]
    exact SymmetricThreeTwoCore.sylow_index_three eA P
  · obtain ⟨P,hP⟩ := hright
    rw [← hP]
    exact SymmetricThreeTwoCore.sylow_index_three eB P

private def residualEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    pResidual 2 H ≃* pResidual 2 K :=
  (e.subgroupMap (pResidual 2 H)).trans (MulEquiv.subgroupCongr (map_pResidual 2 e))

private theorem exceptional_overlap_card_le {H : Type*} [Group H]
    {A B : Subgroup H} (h : ExceptionalMarkedAmalgam A B) :
    Nat.card (A ⊓ B : Subgroup H) ≤ 128 := by
  rcases h with ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · rw [Nat.card_congr e.some.middle.toEquiv]
    have hc : Nat.card ExceptionalModels.G2.derivedB = 32 :=
      Atlas.G2.BinaryParabolicPair.card_derivedSylow
    omega
  · rw [Nat.card_congr e.some.middle.toEquiv]
    have hc : Nat.card ExceptionalModels.G2.fullB = 64 :=
      Atlas.G2.BinaryParabolicPair.card_unipotent_binary
    omega
  · rw [Nat.card_congr e.some.middle.toEquiv, MathieuTwelve.B_eq_S]
    exact (show Nat.card MathieuTwelve.S = 64 from
      Sporadic.Mathieu.M12SmallPair.card_sylowCandidate).le.trans (by decide)
  · rw [Nat.card_congr e.some.middle.toEquiv, AutMathieuTwelve.autB,
      card_map_of_injective (f := AutMathieuTwelve.ambientEquiv.toMonoidHom)
        AutMathieuTwelve.ambientEquiv.injective, AutMathieuTwelve.B_eq_S]
    exact (Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates.card_overlap
      Sporadic.Mathieu.M12ExceptionalExtension.innerModel).le

/-- Bound the original common subgroup using only local Sylow hypotheses. -/
theorem commonSylow_card_le_of_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u})
    (A S B : Subgroup G)
    (hSA : Chapter1.IsSylowIn 2 S A) (hSB : Chapter1.IsSylowIn 2 S B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hcore : pCore 2 (A ⊔ B : Subgroup G) = ⊥) : Nat.card S ≤ 128 := by
  by_cases hlarge : 64 ≤ Nat.card S
  swap
  · omega
  let α := ofSubgroups A S B (Chapter1.isSylowIn_iff.mp hSA).2.1
    (Chapter1.isSylowIn_iff.mp hSB).2.1
  have hp : PrimitiveCubic α := primitiveCubic_of_local_sylows A S B hSA hSB eA eB hcore
  let F := Universal.cosetFamily α
  have ht : CubicTreeAction F := universalCubicTreeAction α hp
  let e := Universal.markedIso α hp.sylow.left_injective hp.sylow.right_injective
  have qA : ((F false) ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3) :=
    (LocalCoreTransport.quotientEquiv 2 e.left.symm).trans eA
  have qB : ((F true) ⧸ pCore 2 (F true)) ≃* Equiv.Perm (Fin 3) :=
    (LocalCoreTransport.quotientEquiv 2 e.right.symm).trans eB
  have hC (i : Bool) : ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)) := by
    cases i
    · rintro ⟨c⟩
      exact residual_not_cubic_of_characteristicTwo hA ⟨(residualEquiv e.left).trans c⟩
    · rintro ⟨c⟩
      exact residual_not_cubic_of_characteristicTwo hB ⟨(residualEquiv e.right).trans c⟩
  have hlarge' : 64 ≤ Nat.card (F false ⊓ F true : Subgroup _) :=
    hlarge.trans_eq (Nat.card_congr e.middle.toEquiv)
  have hAlt (i : Bool) : ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)) := by
    cases i
    · exact ht.residual_not_alternating_of_large_overlap qA qB (hC true) hlarge'
    · exact ht.swap.residual_not_alternating_of_large_overlap qB qA (hC false)
        (by simpa only [Subgroup.CosetGeometry.RankTwo.swapFamily, Bool.not_false,
          Bool.not_true, inf_comm] using hlarge')
  have hr := ht.twoPerfectResidual
  have hrC (i : Bool) : ¬ Nonempty ((pResidual 2 (residualFamily F i)) ≃* Multiplicative (ZMod 3)) := by
    rintro ⟨c⟩
    exact hC i ⟨(ht.residualLocalEquiv i).symm.trans c⟩
  have hrAlt (i : Bool) : ¬ Nonempty ((pResidual 2 (residualFamily F i)) ≃* alternatingGroup (Fin 4)) := by
    rintro ⟨c⟩
    exact hAlt i ⟨(ht.residualLocalEquiv i).symm.trans c⟩
  obtain ⟨s, hs, ho, hreg, hsing⟩ :=
    hr.toCubicTreeAction.exists_large_odd_singularityIndex_of_large_residual hrC hrAlt
  have hsource : LargeTreeSource (residualFamily F) s :=
    ⟨hr, hrC, hrAlt, hs, ho, hreg, hsing⟩
  have hm := marked_base_of_source_cuts labels radius two three hsource
  have hbound : Nat.card (F false ⊓ F true : Subgroup _) ≤ 128 := by
    rcases exceptional_of_marked_residual ht hm with hAB | hBA
    · exact exceptional_overlap_card_le hAB
    · simpa only [inf_comm (F true) (F false)] using exceptional_overlap_card_le hBA
  exact (Nat.card_congr e.middle.toEquiv).le.trans hbound

/-- The exact cubic F.1.12 premise in the original Chapter 14 consumer. -/
theorem cubicF112SizeInput_of_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u}) :
    CubicF112SizeInput.{u} := by
  intro G _ _ L S h hSL hq
  have hSyl (i : Fin 2) : Chapter1.IsSylowIn 2 S (L i) := by
    unfold Chapter1.IsSylowIn
    simpa only [inf_eq_left.mpr (hSL i)] using h.sylow i
  have hB (i : Fin 2) : borel (L i) S = S :=
    borel_eq_of_cubic_local_sylow (L i) S (hSyl i) (hq i).some
  have hpar (i : Fin 2) : parabolic L S i = L i := by
    change L i ⊔ S ⊔ borel (L (other i)) S = L i
    rw [hB, sup_eq_left.mpr (hSL i), sup_eq_left.mpr (hSL i)]
  have hchar (i : Fin 2) : generalizedFitting (L i) = pCore 2 (L i) := by
    rw [← hpar i]
    exact h.characteristic_two i
  have hcore : pCore 2 (L 0 ⊔ L 1 : Subgroup G) = ⊥ := by
    have hg : generated L S = L 0 ⊔ L 1 :=
      sup_eq_left.mpr ((hSL 0).trans le_sup_left)
    rw [← hg]
    exact h.twoCore_free
  exact commonSylow_card_le_of_source_cuts labels radius two three (L 0) S (L 1)
    (hSyl 0) (hSyl 1) (hq 0).some (hq 1).some (hchar 0) (hchar 1) hcore

end CFSG.Quasithin.ChapterF.Source
