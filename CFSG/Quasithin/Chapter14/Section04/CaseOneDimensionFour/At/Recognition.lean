module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Construction
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalRecognition

/-!
# Recognition of the original order-32 branch with local earlier inputs

The local constructor retains H = N_G(V₁) and M = L. The checked large-core
recognition therefore gives an actual Atlas G₂(3) isomorphism when 27 divides
|G|. Otherwise the exact strongly-three-embedded alternative is retained at
that same H. A separate adapter takes the genuine universal I.4.5 theorem;
that input is still required for unconditional recognition.

Earlier Chapter 12 inputs are at the original G,T. The natural marking is
already supplied by the original higher-rank hypothesis. No universal
naturality, structure or uniqueness theorem is reconstructed.
Source: Aschbacher–Smith 14.4.3–5, pp.1007–1008, and I.4.5, p.417.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open DimensionFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L)
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
  (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
include d h structural alternatives F hne hZ hcard

/-- All local-data and completion premises are discharged in the large-core case. -/
theorem source_recognition_of_cube_dvd (hbig : 3 ^ 3 ∣ Nat.card G) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  obtain ⟨c⟩ := source_configuration d h structural alternatives F hne hZ hcard
  exact ChapterI.Section04To05.G2Recognition.nonempty_mulEquiv_of_cube_dvd c hbig

/-- The remaining alternative concerns the literal original point normalizer. -/
theorem source_recognition_or_strong_three :
    (F.H ≠ ⊤ ∧ 3 ∣ Nat.card F.H ∧
      ∀ a : G, a ∉ F.H →
        ¬ 3 ∣ Nat.card (F.H ⊓ F.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
      Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  obtain ⟨c, hcH, _⟩ := source_configuration_on d h structural alternatives F hne hZ hcard
  simpa only [hcH] using ChapterI.Section04To05.G2Recognition.recognition_or_strong_three c

/-- Final order-32 adapter with the genuine, still explicit I.4.5 theorem. -/
theorem source_recognition_of_i45
    (recognize : ∀ (X : Type u) [Group X] [Finite X],
      Nonempty (G2ThreeConfiguration X) → Nonempty (X ≃* Atlas.G2.Model (ZMod 3))) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) :=
  recognize G (source_configuration d h structural alternatives F hne hZ hcard)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
