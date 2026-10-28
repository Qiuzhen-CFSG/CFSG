module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzuki
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionStabilization
public import Theory.Representation.SL2.NaturalImageFixedLine
public import Theory.Representation.BinaryOffender.CrossedComponentPair

/-!
# Excluding crossed support of the original kernel pair

A starred elementary actor swapping two crossed component supports has a
one-dimensional fixed space on either support under its index-two stabilizer.
The normal natural SL₂ component preserves these supports. Clifford
homogeneity and two-group copy selection put an invariant natural copy inside
either support, so the fixed-line estimate forces its field to have order at
most four. This contradicts the surviving odd-degree natural Hall branch.

The actual source application keeps the same marked quotient, starred actor,
Suzuki component, exchanger and commutator identity. The general pair-support
dichotomy then forces both literal Suzuki factors to move the whole original
module. This removes crossed support, not the remaining full-movement tensor
case. Its exclusion, the original source separation/decomposition and the
SeedAnalysisAt assembly remain with qt-d-10-nona5-central-hall-orders.
Both original seed orientations remain in the hypotheses.

Source: Aschbacher--Smith D.2.9(6), D.3.8--9 and D.3.21,
printed pp.182--183,199--201 and204--207.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalPairElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance naturalPairFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := Module.Finite.of_finite
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance naturalPairComponentNormal : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance naturalPairAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A starred actor cannot exchange cross-centralizing component supports in
the actual natural normalizer image over a field larger than four. -/
theorem natural_starred_kernel_pair_not_crossed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 4 < Nat.card F)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (hJK : J ≤ (movedNaturalImageQuotientAction D e I E hE).ker)
    (hindex : (normalizer (J : Set (actionImage (movedStabilizerAction D)))).index = 2)
    (a : actionImage (movedStabilizerAction D)) (ha : a ∈ A)
    (han : a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D)))) :
    ¬ subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤ J ≤
      fixedSpace (imageRepresentation (movedStabilizerAction D))
        (J.map (MulAut.conj a).toMonoidHom) := by
  intro hcross
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (inferInstance : ρ.IsIrreducible)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have ha2 : a * a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  obtain ⟨hcomp,hdim,hperm⟩ := crossed_component_pair_complement σ
    (imageRepresentation_injective ρ) hi J hJ hindex a han ha2 hcross
  let X := subspaceCommutator σ ⊤ J
  have hXn : X ≠ ⊥ := by
    intro hz
    change 2 < Module.finrank (ZMod 2) X at hdim
    rw [hz,finrank_bot] at hdim
    omega
  have hm : X.map (σ a) ≠ X := by
    intro he
    have hd : Disjoint X X := by
      have hd : Disjoint X (X.map (σ a)) := hcomp.disjoint
      rwa [he] at hd
    have hz : X = ⊥ := disjoint_self.mp hd
    exact hXn hz
  let P := A ⊓ subspaceStabilizer σ X
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective
    (inclusion (show P ≤ A from inf_le_left)) (inclusion_injective _)
  have hline := ChosenSource325.starred_swapping_fixed_finrank_one σ X hA ha hm hcomp hdim
    (fun b _ => hperm b)
  obtain ⟨_,hC⟩ := movedNaturalImage_component_and_centralizer D e I E hE
  have hSJ : movedStabilizerComponentImage D ≤ centralizer (J : Set (actionImage ρ)) :=
    le_centralizer_iff.mp (hJK.trans hC.le)
  have hSX : movedStabilizerComponentImage D ≤ subspaceStabilizer σ X :=
    subspaceCommutator_invariant_normalizer σ
      (le_subspaceStabilizer σ ⊤ (by intros; trivial))
      (hSJ.trans (centralizer_le_normalizer (J : Set (actionImage ρ))))
  have hKX : movedStabilizerComponent D ≤ subspaceStabilizer ρ X := by
    intro k hk v
    exact hSX (show actionHom ρ k ∈ movedStabilizerComponentImage D from ⟨⟨k,hk⟩,rfl⟩) v
  have hcoords (l : movedStabilizerComponent D) (v : Fin 2 → F) :
      E ((movedNaturalComponentProjection D e l).val.mulVec v) = I.toRepresentation l (E v) := by
    rw [←hE]
    congr 1
    exact (SL2AutomorphismNatural.action_conj _ _).symm
  exact (not_lt_of_ge (SL2AutomorphismNatural.card_le_four_of_homogeneous_image_fixed_line
    ρ (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I hI E hcoords X hXn hKX P inf_le_right hline)) hF

local instance naturalPairGaloisAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) :=
  ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- The literal exchanged Suzuki pair surviving the original natural Hall
context moves the entire original moved module under each of its factors. -/
theorem source_natural_starred_actor_suzuki_full_movement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    Odd n ∧ ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      1 < rank A ∧
      ⊥ < A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker < A ∧
      IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      (∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) ∧
      ⁅componentOrbit J A,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ =
        componentOrbit J A ∧ componentOrbit J A ≠ ⊥ ∧
      (normalizer (J : Set (actionImage (movedStabilizerAction D)))).index = 2 ∧
      ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧
        a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D))) ∧
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
        subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤ J = ⊤ ∧
        subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤
          (J.map (MulAut.conj a).toMonoidHom) = ⊤ := by
  obtain ⟨ho,A,J,hA,hr,hbot,hproper,hJ,hJK,hSuz,hm,hne,hi,a,ha,han,horbit⟩ :=
    source_natural_starred_actor_suzuki_pair D c ht htn hsep n hn e I hI E hE
  refine ⟨ho,A,J,hA,hr,hbot,hproper,hJ,hJK,hSuz,hm,hne,hi,a,ha,han,horbit,?_⟩
  have hF : 4 < Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    have hn2 : 2 < n := by obtain ⟨k,hk⟩ := ho; omega
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hn2
  have hnot := natural_starred_kernel_pair_not_crossed D c ht htn hsep e I hI E hE hF
    A J hA hJ hJK hi a ha han
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  have hirr : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (movedStabilizerAction_irreducible D c ht htn hsep)
  exact (component_pair_crossed_or_full σ (imageRepresentation_injective ρ) hirr
    J hJ hi a han).resolve_left hnot
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
