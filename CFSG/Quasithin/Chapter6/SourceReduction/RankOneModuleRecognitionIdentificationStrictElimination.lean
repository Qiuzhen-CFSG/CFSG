module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictMathieu
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictFour

/-!
# All thirteen catalogue exclusions on the literal strict action

The original type-a₂ element and nontransitivity of its moved-plane
stabilizer exclude every published G.11.2 alternative. The last four-space
row uses its original symplectic form and order clause to produce an actual
centralizing cubic inside the actor. The triple-cover row uses the genuine
component intertwiner and ambient matrix normalizer.

The source application retains U/Z(U), its faithful dotted actor, the
crossing image and the commutator form. It is conditional on the published
catalogue, whose genuine exhaustion remains with
qt-g112-low-rank-symplectic-classification. Final discharge and the strict
contradiction remain with qt-d-1222-recognition-strict-elimination;
qt-d-1222-rankone-recognition-identification supplies LocalAnalysis.

Source: Aschbacher--Smith, 6.2.19, printed p.691 (PDF p.708).
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open Representation.RankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictCatalogue
variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The four-dimensional row contradicts the original moved-plane
nontransitivity, with no subgroup-analysis or model-matching premise. -/
theorem exclude_two
    {ρ : Representation (ZMod 2) H V} {B : LinearMap.BilinForm (ZMod 2) V}
    (a : H) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hType : ∀ w, B w (ρ a w) = 0)
    (hnt : ¬ StabilizerTransitive ρ (movedSpace ρ a))
    (hc : ChapterG.Section11.CaseTwo ρ B) : False := by
  obtain ⟨hd, ho, hf, hAlt, hND, hpres⟩ := hc
  exact hnt (StrictFour.transitive_of_four_dimension ρ B hf hd hAlt hND
    hpres a ha2 ha1 hType hr ho)

/-- Conditional elimination of the full printed catalogue. Its exhaustion is
an explicit input here and must be discharged by the source assembly. -/
theorem false_of_conclusion
    {ρ : Representation (ZMod 2) H V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup H}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hd : 4 ≤ finrank (ZMod 2) V)
    (a : H) (ha : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hType : ∀ w, B w (ρ a w) = 0)
    (hnt : ¬ StabilizerTransitive ρ (movedSpace ρ a))
    (hc : ChapterG.Section11.Conclusion ρ B X) : False :=
  exclude_two a ha1 ha2 hr hType hnt
    (caseTwo_of_conclusion h hd a ha ha1 ha2 hr hType hnt hc)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictCatalogue

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Every catalogue row is impossible on the literal strict action. The only
additional source input is the actual catalogue conclusion; the genuine
classifier must supply it before the unconditional strict contradiction follows. -/
theorem LocalAnalysis.false_of_strict_catalogue
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation (T : Subgroup G) L R z) B v
      (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
      (strictCrossingImage (T : Subgroup G) L R z d)
      ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L R z d)))
    (hB : ∀ u w : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w)
    (hc : ChapterG.Section11.Conclusion (strictRepresentation (T : Subgroup G) L R z) B
      (strictCrossingImage (T : Subgroup G) L R z d)) :
    False := by
  obtain ⟨he', hX', B', v', _, _, hB', hd, _, _, _, _,
      a, ha, ha1, ha2, _, hr, _, htype, hnt⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  have hzero (u w : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) :
      B u w = 0 ↔ B' u w = 0 := by
    obtain ⟨u', hu⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) u.toMul
    obtain ⟨w', hw⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) w.toMul
    simpa only [strictHatElement, hu, hw, ofMul_toMul] using
      (hB u' w').trans (hB' u' w').symm
  exact StrictCatalogue.false_of_conclusion h hd a ha ha1 ha2 hr (fun w => (hzero w _).mpr (htype w)) hnt hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
