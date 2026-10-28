module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalTransvections
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalOmegaLine
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalAssembly

/-!
# The original Chapter 12 quotient action in the numerical branch

The chosen module discharges the normalizer premise for the actual action
of C_G(z) on U/⟨z⟩. Its kernel meets the original commutator layer in the
two-core intersection, and the faithful image has trivial two-core before
the order-eight conclusion is known. In the order-four branch the marked
common-center action satisfies the repaired G.3 theorem on that same image.

The earlier H-star centralization produces a minimal H-star subgroup inside
the escaping involution centralizer. The odd-distance argument excluding
the order-sixteen intersection and the ambient four-space contradiction
excluding the order-four intersection remain to be proved.

Source: Aschbacher--Smith, 6.2.8--11, printed pp.684--686, applied to
[R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The earlier kernel and two-core statements, independent of 6.2.12. -/
theorem source_local_quotient_action_geometry
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    pCore 2 (LocalQuotientAction.action (T : Subgroup G) L (wholeReduced T L) z).range = ⊥ ∧
    commutatorLayer T L ⊓ LocalQuotientAction.kernel (T : Subgroup G) L (wholeReduced T L) z =
      commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 ∧
    Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) *
      Nat.card (((commutatorLayer T L).subgroupOf (centralizer ({z} : Set G))).map
        (LocalQuotientAction.action (T : Subgroup G) L (wholeReduced T L) z)) = 16 := by
  have hp := (source_local_layer_normalizers D h h611 hnatural).1
  exact ⟨LocalQuotientAction.action_range_core h611 hnatural hz ho hT,
    LocalQuotientAction.layer_inf_kernel h611 hnatural hz ho hT hp,
    LocalQuotientAction.layer_image_card h611 hnatural hz ho hT hp⟩

/-- The genuine G.3 source-use theorem applied to the original faithful image
in the contrary order-four branch of 6.2.11. -/
theorem source_local_four_intersection_G3
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    letI := (LocalQuotientAction.reduced_space h611 hnatural hz ho hT).elementary
    let A := (LocalQuotientAction.linearAction (T : Subgroup G) L (wholeReduced T L) z).range
    ∃ x : Additive (LocalQuotientAction.space (T : Subgroup G) L (wholeReduced T L) z), x ≠ 0 ∧
      x.toMul ∈ LocalQuotientAction.seedLine (T : Subgroup G) L (wholeReduced T L) z ∧
      pCore 2 A = ⊥ ∧
      ChapterG.Section03.Hypotheses A (MulAction.orbit A x) ∧
      ChapterG.Section03.FullAction A (MulAction.orbit A x) ∧
      ChapterG.Section03.Decomposition A (MulAction.orbit A x) ∧
      ChapterG.Section03.LocalStructure A (MulAction.orbit A x) :=
  LocalQuotientAction.four_image_G3 h611 hnatural hz ho hT
    (source_local_layer_normalizers D h h611 hnatural).1 hcard

/-- The actual minimal subgroup starting the graph argument, from exactly
the earlier 6.1.5 H-star centralization premise. -/
theorem source_local_exists_centralizer_hstar
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ∃ z ∈ ZS (T : Subgroup G) L (wholeReduced T L), orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      ∃ Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        Y ≤ centralizer ({z} : Set G) ∧ ChapterE.generationParameter Y = 1 ∧
        (T : Subgroup G) ≤ Y ⊓ normalizer (L : Set G) ∧
        Y ⊓ normalizer (L : Set G) ⋖ Y ∧
        (∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ⋖ Y → X = Y ⊓ normalizer (L : Set G)) := by
  obtain ⟨z, hz, ho, hT, _, _, he, _⟩ :=
    source_local_omega_geometry_of_hstar_centralization h611 hnatural hout hcentral
  exact ⟨z, hz, ho, hT, local_exists_hstar_in_centralizer h611 ho hT he⟩

/-- The literal order-two action conclusion of 6.2.11 supplies the order-eight
premise of the existing LocalAnalysis assembly. Both source obligations remain
explicit here: omega-centralizer escape and the order of the actual image. -/
theorem source_local_analysis_of_omega_escape_and_image_two
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hescape : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (himage : Nat.card (((commutatorLayer T L).subgroupOf (centralizer ({z} : Set G))).map
      (LocalQuotientAction.action (T : Subgroup G) L (wholeReduced T L) z)) = 2) :
    LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z := by
  have hc := (source_local_quotient_action_geometry D h h611 hnatural hz ho hT).2.2
  rw [himage] at hc
  exact source_local_analysis_of_omega_escape_and_core_card D h h611 hnatural hescape hz ho hT
    (by omega)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
