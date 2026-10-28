module
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Geometry

/-!
# Nonabelian rank-two recognition inputs on the original closure

Original 14.2.4 supplies the literal RankTwoHypothesis. The early local
closure and kernel theorems then identify the Frattini subgroup of U with
the marked point and give V ∩ Z(U) = V₁. The two actual projections of V
have the same kernel, proving 14.3.11 by a canonical quotient equivalence.
The small-Frattini construction supplies an extraspecial factor and the
marked commutator and square forms, invariant under the actual H/O₂(H)
actions. The final source application identifies H with the original Mc
and U with its original conjugate span; no flag or local-kernel premise
is retained.

These are the inputs to the later recognition argument, not a classification
of U or H/O₂(H). In particular the factor need not yet be all of U.

Source: Aschbacher--Smith, 12.8.8(1--3), printed pp.851--852;
14.3.10--11 and the opening setup for 14.3.15, printed pp.993--994.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The original closure, center intersection and action kernel. -/
structure ClosureGeometry (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] : Prop where
  two : IsPGroup 2 F.U
  frattini_point : frattini F.U = (F.Vi 1).subgroupOf F.U
  seed_center : V ⊓ F.ZU = F.Vi 1
  tilde_kernel : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H

/-- All early local inputs in the nonabelian rank-two source branch. -/
theorem rankTwo_closure_geometry {K : GroupClass} {L M : Subgroup G}
    (h : RankTwoHypothesis K T L M) (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] (hne : ¬ IsMulCommutative F.U) :
    ClosureGeometry F := by
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  refine ⟨F.localKernel_UH_isPGroup h.simpleQTKE L M F.H (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat
    (h.pointNormalizer_mem_Hz F), ?_, ?_, ?_⟩
  · exact F.localKernel_frattini_eq_point h.simpleQTKE L M (by decide)
      h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat
      (h.flag_escape F) hne
  · exact F.seed_inf_center_eq_point L (by decide) h.L_normalizes_seed
      (F.localKernel_irreducible L (by decide) h.L_normalizes_seed hnat) hne
  · exact F.localKernel_eq_pCore h.simpleQTKE L M F.H (by decide)
      h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat
      h.M_eq_normalizer h.unique h.seed_centralizer_le h.centralizer_L
      (h.pointNormalizer_mem_Hz F)

variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]

/-- The literal map from the original seed into the central quotient. -/
noncomputable def seedHatMap : V →* hatImage F V :=
  ((QuotientGroup.mk' (center F.U)).comp
    (inclusion (le_conjugateSpanBy V F.H))).codRestrict _
      (fun v => ⟨⟨v, le_conjugateSpanBy V F.H v.property⟩, v.property, rfl⟩)

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem seedHatMap_surjective : Function.Surjective (seedHatMap F) := by
  intro q
  obtain ⟨u, hu, he⟩ := q.property
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

omit [Finite G] in
/-- The two seed projections have the same literal kernel. -/
theorem seed_projection_kernels (hc : V ⊓ F.ZU = F.Vi 1) :
    (F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H)).ker =
      (seedHatMap F).ker := by
  ext v
  change F.tildeMap V _ v = 1 ↔ seedHatMap F v = 1
  rw [Subtype.ext_iff, Subtype.ext_iff]
  change F.tildeProjection ⟨v, _⟩ = 1 ↔
    QuotientGroup.mk' (center F.U) ⟨v, _⟩ = 1
  simp only [tildeProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  change (v : G) ∈ F.Vi 1 ↔ (⟨v, le_conjugateSpanBy V F.H v.property⟩ : F.U) ∈ center F.U
  constructor
  · intro hv
    have hz : (v : G) ∈ F.ZU := (show F.Vi 1 ≤ F.ZU from hc ▸ inf_le_right) hv
    obtain ⟨u, hu, he⟩ := hz
    exact (show u = ⟨v, _⟩ from Subtype.ext he) ▸ hu
  · intro hv
    rw [← hc]
    exact ⟨v.property, ⟨_, hv, rfl⟩⟩

/-- The canonical comparison on V, rather than an abstract rank coincidence. -/
noncomputable def seedQuotientEquiv (hc : V ⊓ F.ZU = F.Vi 1) :
    F.tilde V ≃* hatImage F V :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H))
      (F.tildeMap_surjective V _)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (seed_projection_kernels F hc)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (seedHatMap F) (seedHatMap_surjective F)))

/-- Original 14.3.11, on the original hat and tilde images. -/
theorem seed_ranks (d : ClosureGeometry F) :
    primeRank 2 (hatImage F V) = primeRank 2 (F.tilde V) :=
  (primeRank_equiv 2 (seedQuotientEquiv F d.seed_center)).symm

/-- The factor in source 12.8.8(1) retains the original marked Frattini subgroup. -/
theorem extraspecial_factor (d : ClosureGeometry F) (hn : 1 ≤ n)
    (hne : ¬ IsMulCommutative F.U) :
    ∃ E : Subgroup F.U, IsExtraspecial 2 E ∧ E ⊔ center F.U = ⊤ ∧
      (frattini E).map E.subtype = (F.Vi 1).subgroupOf F.U :=
  F.exists_extraspecial_factor_of_point hn d.two d.frattini_point hne

/-- The actual H/O₂(H) action preserves the nondegenerate alternating form. -/
theorem symplectic_form (d : ClosureGeometry F) (hn : 1 ≤ n) :
    ∃ he : IsElementaryAbelian 2 F.Uhat, letI := he
    ∃ hc : pCore 2 F.H ≤ F.uhatAction.ker,
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat),
      B.IsAlt ∧ B.Nondegenerate ∧
      (∀ x y : F.Uhat, B (Additive.ofMul x) (Additive.ofMul y) =
        (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn d.frattini_point)
          (F.uhatCommutator d.two x y)).toAdd) ∧
      ∀ (h : HStar F.H) (x y : F.Uhat),
        B (Additive.ofMul (F.uhatStarAction hc h x))
          (Additive.ofMul (F.uhatStarAction hc h y)) =
        B (Additive.ofMul x) (Additive.ofMul y) := by
  let he := F.uhat_elementary_of_point hn d.two d.frattini_point
  let := he
  let hc := F.pCore_le_uhatAction_ker_of_tilde_kernel hn d.tilde_kernel
  refine ⟨he, hc, F.uhatBilinearForm hn d.two d.frattini_point,
    F.uhatBilinearForm_isAlt hn d.two d.frattini_point,
    F.uhatBilinearForm_nondegenerate hn d.two d.frattini_point,
    F.uhatBilinearForm_apply hn d.two d.frattini_point, ?_⟩
  exact F.uhatBilinearForm_star_invariant hn d.two d.frattini_point hc

/-- The original square form is preserved on U/V₁, without assuming Z(U)=V₁. -/
theorem quadratic_form (d : ClosureGeometry F) (hn : 1 ≤ n) :
    ∃ he : IsElementaryAbelian 2 (F.tilde F.U), letI := he
    ∃ hc : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker,
    ∃ q : QuadraticForm (ZMod 2) (Additive (F.tilde F.U)),
      (∀ x : F.tilde F.U, q (Additive.ofMul x) =
        (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn d.frattini_point)
          (F.tildeSquare hn d.two d.frattini_point x)).toAdd) ∧
      ∀ (h : HStar F.H) (x : F.tilde F.U),
        q (Additive.ofMul (F.tildeStarAction hc h x)) = q (Additive.ofMul x) := by
  let he := F.tilde_elementary_of_point d.two d.frattini_point
  let := he
  refine ⟨he, d.tilde_kernel.symm.le,
    F.tildeQuadraticForm hn d.two d.frattini_point,
    F.tildeQuadraticForm_apply hn d.two d.frattini_point, ?_⟩
  exact F.tildeQuadraticForm_star_invariant hn d.two d.frattini_point d.tilde_kernel.symm.le

/-- At rank two the actual seed image is a line in U/Z(U). -/
theorem rankTwo_seed_line {M : Subgroup G}
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] (d : ClosureGeometry F) :
    ∃ he : IsElementaryAbelian 2 F.Uhat, letI := he
      Module.finrank (ZMod 2) (hatSpace F (rankTwoSeed T M)) = 1 := by
  let he := F.uhat_elementary_of_point (by decide) d.two d.frattini_point
  let := he
  refine ⟨he, ?_⟩
  have hh := finrank_hatSpace_plane F (by decide) d.seed_center
  exact (congrArg (fun A : Subgroup G =>
    Module.finrank (ZMod 2) (hatSpace F A)) F.last).symm.trans hh

/-- Specialize to the original Mc closure, deriving its flag and every local input. -/
theorem source_recognition_preparation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ∃ he : IsElementaryAbelian 2 (rankTwoSeed T M), letI := he
    ∃ F : InvariantFlag T (rankTwoSeed T M) 2,
      F.Vi 1 = centralInvolutions T ∧ F.H = Mc ∧
      F.U = conjugateSpanBy (localModule T M) Mc ∧ ClosureGeometry F ∧
      primeRank 2 (hatImage F (rankTwoSeed T M)) = primeRank 2 (F.tilde (rankTwoSeed T M)) ∧
      ∃ E : Subgroup F.U, IsExtraspecial 2 E ∧ E ⊔ center F.U = ⊤ ∧
        (frattini E).map E.subtype = (F.Vi 1).subgroupOf F.U := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let he := rankTwoSeed_elementary h
  let := he
  obtain ⟨_, F, _⟩ := h.exists_flag_geometry
  have hp : F.Vi 1 = centralInvolutions T :=
    (h.sylowOmega_eq_point F).symm.trans (sylowOmega_eq_centralInvolutions T)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hZ,hMc,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hFH : F.H = Mc := by
    change normalizer (F.Vi 1 : Set G) = Mc
    rw [hp, hMc]
    exact le_antisymm (normalizer_le_centralizer_of_card_two _ hZ)
      (Subgroup.centralizer_le_normalizer _)
  have hFU : F.U = conjugateSpanBy (localModule T M) Mc := by
    change conjugateSpanBy (rankTwoSeed T M) F.H = _
    rw [hFH]
    exact congrArg (fun W : Subgroup G => conjugateSpanBy W Mc)
      (rankTwoSeed_eq_localModule T M)
  have hneF : ¬ IsMulCommutative F.U := hFU ▸ hne
  have d := rankTwo_closure_geometry h F hneF
  exact ⟨he,F,hp,hFH,hFU,d,seed_ranks F d,extraspecial_factor F d (by decide) hneF⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
