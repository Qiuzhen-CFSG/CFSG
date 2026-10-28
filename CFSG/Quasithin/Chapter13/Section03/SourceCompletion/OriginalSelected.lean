module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.Reduction

/-!
# Constructing the original flag for the selected unitary exclusion

A common Sylow marking of the natural module pulls the native line, plane
and three-space back to the original ambient group. Their inclusions,
normalization and orders produce the entire original flag. The selected
PSU₃(3) exclusion can therefore use the completed plane-centralizer,
noncentrality and maximal-escape arguments without a supplied flag.

The earlier 12.2 and 13.3.2 implications retain producers qt-d-1222-source
and qt-d-1332-source, with final discharge at qt-theorem-d. The selected
natural-module data and the prime-normalizer premise remain explicit;
the latter still belongs to qt-d-13316-source. This is a conditional
source reduction, not an unconditional proof of Theorem 13.3.16.

Source: Aschbacher--Smith, Notation 13.3.3 and Theorem 13.3.16,
printed pp.885,893--896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE OriginalPlaneCentralizers
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem coordinateGroup_mono (E : Additive V ≃ₗ[F] W)
    {P Q : Submodule F W} (h : P ≤ Q) : coordinateGroup E P ≤ coordinateGroup E Q := by
  intro x hx
  let v : Additive V := Additive.ofMul ⟨x, coordinateGroup_le E P hx⟩
  exact (mem_coordinateGroup E Q v).mpr (h ((mem_coordinateGroup E P v).mp hx))

/-- Existence of the original Sylow-invariant flag, in one compatible
natural-module coordinate frame. -/
theorem exists_unitary_original_flag (T : Sylow 2 G) (L : Subgroup G)
    (hLN : L ≤ normalizer (V : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hNL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer V L) v,
      E0 (automizerRepresentation V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v)) :
    ∃ Z B U : Subgroup G, Z ≤ B ∧ B ≤ U ∧ U ≤ V ∧
      (T : Subgroup G) ≤ normalizer (Z : Set G) ∧
      (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      Nat.card Z = 2 ∧ Nat.card B = 4 ∧ Nat.card U = 8 := by
  obtain ⟨rho,E,he,ht,_⟩ := exists_unitary_sylow_marking T L hLN hNL e E0 he0
  have hnorm (S : Submodule F W)
      (hpres : ∀ g : Atlas.G2.Model F, g ∈ Atlas.G2.unipotent → ∀ v ∈ S,
        Atlas.G2.Restricted.NaturalCoordinates.action F g v ∈ S) :
      (T : Subgroup G) ≤ normalizer (coordinateGroup E S : Set G) := by
    apply normalizes_marked_subgroup _ _ rho E he (coordinateGroup_le E S) hTN
    intro t v hv
    rw [coordinateGroup_space] at hv ⊢
    exact hpres _ (ht ⟨_,⟨inclusion hTN t,t.property,rfl⟩,rfl⟩) v hv
  have hcard (S : Submodule F W) : Nat.card (coordinateGroup E S) = Nat.card S := by
    rw [← card_pointCoordinateSubspace E _ (coordinateGroup_le E S),coordinateGroup_space]
  have hps : plane ≤ seed := by
    intro v hv
    have hv' := (mem_plane v).mp hv
    exact (mem_seed v).mpr ⟨hv'.2.1,hv'.2.2.1,hv'.2.2.2⟩
  exact ⟨coordinateGroup E pointLine,coordinateGroup E plane,coordinateGroup E seed,
    coordinateGroup_mono E pointLine_le_plane,coordinateGroup_mono E hps,
    coordinateGroup_le E seed,
    hnorm pointLine (fun g hg v hv => (unipotent_fixes_pointLine g hg v hv).symm ▸ hv),
    hnorm plane unipotent_preserves_plane,hnorm seed unipotent_preserves_seed,
    (hcard pointLine).trans card_pointLine,(hcard plane).trans card_plane,
    (hcard seed).trans card_seed⟩

open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u

/-- The completed geometry constructs its own original flag before the
conditional terminal contradiction. Only odd-local control remains local. -/
theorem unitary_original_false_without_flag
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    [IsElementaryAbelian 2 V] (s : Context T L V)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L)
    (hodd : UnitaryPrimeNormalizerControl L V) : False := by
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  obtain ⟨Z,B,U,hZB,hBU,hUV,hTZ,hTB,hTU,hZ,hB,hU⟩ :=
    exists_unitary_original_flag T L s.chosen.normalizes hTN hNL
      s.actor s.coordinates s.equivariant
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,U,Z,normalizer (Z : Set G)⟩
  exact unitary_original_false_of_prime_normalizer_control D s earlier hUV
    (hZB.trans (hBU.trans hUV)) hTZ hTU hZ hU B (hBU.trans hUV)
    hTB hB rfl h1332 fixed five hodd

/-- The literal PSU₃(3) quotient is excluded without any flag, rank,
plane-centralizer, noncentrality, maximal-action or MS-classification input.
The odd-normalizer premise still belongs to this source assembly task. -/
theorem unitary_original_quotient_exclusion_of_prime_normalizer_control
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    [IsElementaryAbelian 2 V]
    (h : Hypothesis1331 T L) (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (chosen : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E : Additive V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he : ∀ (l : inducedAutomizer V L) v,
      E (automizerRepresentation V l v) = Atlas.G2.Natural.derivedAction F (e l) (E v))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L)
    (hodd : UnitaryPrimeNormalizerControl L V) :
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3 := by
  rintro ⟨K,_,_,J,hK,hJ,⟨eJ⟩⟩
  let s : Context T L V :=
    ⟨h,hmax,eJ.trans (J.projectiveEquivBinaryG2Derived hK hJ),chosen,structural,e,E,he⟩
  exact unitary_original_false_without_flag s earlier h1332 fixed five hodd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
