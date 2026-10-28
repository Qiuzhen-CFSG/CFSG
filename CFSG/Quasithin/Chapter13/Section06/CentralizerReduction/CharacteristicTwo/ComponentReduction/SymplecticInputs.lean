module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Solvable
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.SourceExclusion
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity
public import Theory.GroupTheory.NormalizerAction.Sylow
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry

/-!
# Inputs from the normalized component to the symplectic contradiction

The faithful component image is K/Z(K). The exact I.1.3 multiplier input
makes its projection a genuine isomorphism, with the quotient triangle
retained. Binary cubic witnesses eliminate source alternative (ii), so the
remaining inner source alternative gives actual Lᵥ containment in K.

From that containment, a genuine whole-component model and the original
centralizer Sylow construct the specified symplectic Sylow and the earlier
residual Borel placement. Solvability and intrinsic solvable-Sylow control
are proved inputs; no Borel placement is assumed. The final transport keeps
K as a subgroup of Gᵥ and then embeds it literally into G.

The multiplier theorem itself remains with qt-i01-lie-symplectic. Its precise
needed conclusion is (universalProjection (Sp F)).ker = ⊥ for |F|=2^n, n>1.
The nonsplit extension alternatives must still be excluded by the existing
root-rigidity owner before applying the two-inner-alternatives lemma.
Source: Aschbacher–Smith, 13.6.6 (p.927) and I.1.3 (p.407).
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.SymplecticInputs
open A5Module NormalizedBorel SymplecticBorel
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] [Finite F] [Finite G] in
/-- The whole model retains the actual quotient triangle. Triviality of the
universal kernel is the precise independent I.1.3 input, not a proved fact here. -/
theorem exists_whole_model_of_trivial_universal_kernel
    (K : Subgroup G) (hK : IsComponent G K)
    (eStar : NormalizerAction.componentImage K ≃* Sp F)
    (hm : (universalProjection (Sp F)).ker = ⊥) :
    ∃ e : K ≃* Sp F, ∀ k : K,
      e k = eStar (NormalizerAction.componentCentralQuotientEquiv K
        (QuotientGroup.mk' (center K) k)) := by
  let : IsQuasisimple K := hK.2
  let q := (NormalizerAction.componentCentralQuotientEquiv K).trans eStar
  let f : Cover K (Sp F) := {
    toMonoidHom := q.toMonoidHom.comp (QuotientGroup.mk' (center K))
    surjective := q.surjective.comp (QuotientGroup.mk'_surjective (center K))
    isPerfect := inferInstance
    ker_le_center := by
      intro k hk
      apply (QuotientGroup.eq_one_iff k).mp
      apply q.injective
      exact hk.trans (map_one q).symm }
  exact ⟨MulEquiv.ofBijective f.toMonoidHom
    ⟨f.injective_of_universalProjection_ker_eq_bot hm, f.surjective⟩, fun _ => rfl⟩

/-- Source alternative (ii) cannot have symplectic component image. The
central-cover rank passage and the binary cubic witness are both proved. -/
theorem not_rank_one_of_symplectic_component_image
    (K : Subgroup G) (eStar : NormalizerAction.componentImage K ≃* Sp F) :
    ¬ primeRank 3 K ≤ 1 := by
  intro hr
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hquot := NormalizerAction.componentImage_rank_le_one K (by decide) hr
  rw [primeRank_equiv 3 eStar] at hquot
  have htwo : 2 ≤ primeRank 3 (Sp F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (primeRank_le_of_injective 3 (commutator (Sp F)).subtype
        (commutator (Sp F)).subtype_injective)
  omega

variable {L V : Subgroup G}

/-- Retain the actual source alternatives. Inner action alone does not put
the original residual inside the component because its action has a kernel. -/
theorem residual_le_component_of_inner_source_alternatives
    (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (eStar : NormalizerAction.componentImage K ≃* Sp F)
    (hcases : (residual s ≤ primeToResidual 3 (Gv (markedV s)) ∧
      K = primeToResidual 3 (Gv (markedV s))) ∨ primeRank 3 K ≤ 1) :
    residual s ≤ K := by
  rcases hcases with ⟨hres, heq⟩ | hr
  · exact hres.trans_eq heq.symm
  · exact False.elim (not_rank_one_of_symplectic_component_image K eStar hr)

@[expose] noncomputable def ambientModel {v : G} (K : Subgroup (Gv v)) (e : K ≃* Sp F) :
    K.map (Gv v).subtype ≃* Sp F :=
  (K.equivMapOfInjective (Gv v).subtype (Gv v).subtype_injective).symm.trans e

/-- The literal ambient Sylow and earlier residual Borel placement are
constructed from the whole component model and actual Lᵥ≤K source branch. -/
theorem exists_ambient_sylow_and_residual_borel
    (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : K ≃* Sp F) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hTN : localT T (markedV s) ≤ X K) (hDK : residual s ≤ K) :
    ∃ S : Sylow 2 (Sp F),
      (localSylow (K.map (Gv (markedV s)).subtype) (ambientModel K e) S :
        Subgroup (K.map (Gv (markedV s)).subtype)).map
          (K.map (Gv (markedV s)).subtype).subtype =
            Tv T (markedV s) ⊓ K.map (Gv (markedV s)).subtype ∧
      Lv L (markedV s) ≤ borelIn (K.map (Gv (markedV s)).subtype) (ambientModel K e) S ∧
      Tv T (markedV s) ≤ normalizer (K.map (Gv (markedV s)).subtype : Set G) := by
  let H := Gv (markedV s)
  let A := K.map H.subtype
  let i := K.equivMapOfInjective H.subtype H.subtype_injective
  let ea := ambientModel K e
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hK.1
  let Qa := Q.mapSurjective (f := i.toMonoidHom) i.surjective
  let S := Qa.mapSurjective (f := ea.toMonoidHom) ea.surjective
  have hQa : (Qa : Subgroup A).map A.subtype = Tv T (markedV s) ⊓ A := by
    change ((Q : Subgroup K).map i.toMonoidHom).map A.subtype = _
    rw [map_map]
    change (Q : Subgroup K).map (H.subtype.comp K.subtype) = _
    rw [← map_map, hQ, subgroupOf_map_subtype, map_inf _ _ _ H.subtype_injective, hP]
    change (T.subgroupOf H).map H.subtype ⊓ A = _
    rw [subgroupOf_map_subtype]
    rfl
  have hS : (localSylow A ea S : Subgroup A) = Qa := by
    rw [localSylow_coe]
    change ((Qa : Subgroup A).map ea.toMonoidHom).comap ea.toMonoidHom = Qa
    exact comap_map_eq_self_of_injective ea.injective _
  have hSyl : (localSylow A ea S : Subgroup A).map A.subtype = Tv T (markedV s) ⊓ A :=
    congrArg (fun U : Subgroup A => U.map A.subtype) hS |>.trans hQa
  have hnorm : Tv T (markedV s) ≤ normalizer (A : Set G) := by
    have hh := (map_mono hTN).trans (le_normalizer_map H.subtype)
    change (T.subgroupOf H).map H.subtype ≤ normalizer (A : Set G) at hh
    simpa only [subgroupOf_map_subtype, Tv, H] using hh
  have hDA : Lv L (markedV s) ≤ A := by
    have hh := map_mono (f := H.subtype) hDK
    change ((Lv L (markedV s)).subgroupOf H).map H.subtype ≤ A at hh
    rwa [map_subgroupOf_eq_of_le (Lv_le_Gv L (markedV s))] at hh
  let J := residual s ⊔ localT T (markedV s)
  let : Group.IsSolvable J := residual_sup_localT_isSolvable s T hk hTL (hP ▸ P.isPGroup')
  have hJmap : J.map H.subtype = Lv L (markedV s) ⊔ Tv T (markedV s) := by
    change (residual s ⊔ localT T (markedV s)).map H.subtype = _
    rw [Subgroup.map_sup]
    change ((Lv L (markedV s)).subgroupOf H).map H.subtype ⊔
      (T.subgroupOf H).map H.subtype = _
    rw [map_subgroupOf_eq_of_le (Lv_le_Gv L (markedV s)), subgroupOf_map_subtype]
    rfl
  have hjSol : Group.IsSolvable (Lv L (markedV s) ⊔ Tv T (markedV s) : Subgroup G) := by
    rw [← hJmap]
    exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective J)
  let := hjSol
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  have hc : SolvableSylowControl 2 A := SolvableSylowControl.of_equiv ea
    (solvable_overgroups_of_orthogonal_root_orbits hF hn
      (solvable_unipotent_point_orbit_orthogonal hlarge))
  have hN := hc.normalizes_sylow A (Lv L (markedV s) ⊔ Tv T (markedV s)) Qa
    (sup_le (hDA.trans A.le_normalizer) hnorm)
    (hQa.le.trans (inf_le_left.trans le_sup_right))
  refine ⟨S, hSyl, ?_, hnorm⟩
  rw [borelIn_eq_relative_normalizer A ea (Tv T (markedV s)) S hSyl]
  exact le_inf hDA (le_sup_left.trans (hQa ▸ hN))

/-- Actual 13.6.6 source application after the normalized-component sieve.
Beyond the earlier source setup, the only inputs are the true component,
its faithful symplectic image, I.1.3's exact universal-kernel conclusion,
normalization by the actual local Sylow, and the source inner alternatives.
The whole component model, local Sylow, residual Borel placement, Baumann
containment, local index and inverter are all constructed. -/
theorem false_of_symplectic_component_image
    {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃
      (markedZ d.flag.module))
    (hcounter : IsA5Counterexample G)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup (Gv (markedV d.flag.module)))
    (hK : IsComponent (Gv (markedV d.flag.module)) K)
    (eStar : NormalizerAction.componentImage K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hI13 : (universalProjection (Sp F)).ker = ⊥)
    (hTN : localT (T : Subgroup G) (markedV d.flag.module) ≤ X K)
    (hcases : (residual d.flag.module ≤ primeToResidual 3 (Gv (markedV d.flag.module)) ∧
      K = primeToResidual 3 (Gv (markedV d.flag.module))) ∨ primeRank 3 K ≤ 1) :
    False := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have hk : IsPGroup 2 d.flag.module.action.ker := by
    rw [d.flag.action_kernel]
    exact pCore_isPGroup
  have hP : (c.reductions.centralizerSylow : Subgroup (Gv (markedV d.flag.module))) =
      localT (T : Subgroup G) (markedV d.flag.module) := by
    apply map_injective (Gv (markedV d.flag.module)).subtype_injective
    rw [c.reductions.sylow_image]
    change Tv (T : Subgroup G) (markedV d.flag.module) =
      ((T : Subgroup G).subgroupOf (Gv (markedV d.flag.module))).map
        (Gv (markedV d.flag.module)).subtype
    exact (subgroupOf_map_subtype _ _).symm
  obtain ⟨e, _⟩ := exists_whole_model_of_trivial_universal_kernel K hK eStar hI13
  have hDK := residual_le_component_of_inner_source_alternatives d.flag.module K eStar hcases
  obtain ⟨S, hSyl, hD, hTK⟩ := exists_ambient_sylow_and_residual_borel
    d.flag.module (T : Subgroup G) K hK e hF hn hk earlier.T_normalizes_L
    c.reductions.centralizerSylow hP hTN hDK
  exact SourceExclusion.false_of_earlier_local_source d V₃ earlier hcounter hfusion
    (K.map (Gv (markedV d.flag.module)).subtype) (ambientModel K e) hF hn S
    (map_subtype_le K) hTK hSyl hD

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.SymplecticInputs
