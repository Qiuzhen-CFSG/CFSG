module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.LayerGeometry
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.OuterSubgroups
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Local outer actors in the actual orthogonal source representation

Let X be the literal subgroup R_t ⟨t⟩ from `LayerGeometry`, and suppose the
actual involution t acts as conjugation in the marked Hermitian coordinates.
Every element of X is a fixed-field root or that root times t. The displacement
formulas put all displacements in the fixed K-plane of R_t, proving quadraticity.

An outer subgroup of rank one fixes the hyperplane trace(z) = u b and has
binary codimension s. An outer subgroup of rank at least two contains a
nonidentity inner root and fixes exactly the common K-plane, giving binary
codimension 2s. All K-dimensions are computed on transported model subspaces;
no K-module structure is imposed on the original binary module V.

For s>1 the outer threshold-two actors have rank s or s+1, or rank one when
s=2. The minimum 2s/(s+1) within this outer family occurs exactly at X.
These are separate statements: the threshold family is larger than {X}.
The realization identity remains explicit, and global placement and global
minima require the independent ambient classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.3.1.2,
printed p.454, and the threshold definition D.2.1, printed p.178.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal Pointwise
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance localActorFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance localActorBinarySpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L)

/-- The K-span of the original binary fixed vectors in the marked model.
The local fixed-space theorems below prove that the image is already a K-space. -/
def fixedModelSpace (A : Subgroup G) : Submodule (fixedField s) (Space s) :=
  Submodule.span (fixedField s) (M.coordinates '' (fixedSpace ρ A : Set V))

theorem fixedModelSpace_eq_of_mem_iff (A : Subgroup G)
    (P : Submodule (fixedField s) (Space s))
    (hP : ∀ v, v ∈ fixedSpace ρ A ↔ M.coordinates v ∈ P) :
    M.fixedModelSpace A = P := by
  have he : M.coordinates '' (fixedSpace ρ A : Set V) = (P : Set (Space s)) := by
    ext X
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hP v).mp hv
    · intro hX
      obtain ⟨v, rfl⟩ := M.coordinates.surjective X
      exact ⟨v, (hP v).mpr hX, rfl⟩
  rw [fixedModelSpace, he, Submodule.span_eq]

/-- Binary coordinates on a fixed space identified with a literal model K-space. -/
def fixedCoordinatesEquiv (A : Subgroup G)
    (P : Submodule (fixedField s) (Space s))
    (hP : ∀ v, v ∈ fixedSpace ρ A ↔ M.coordinates v ∈ P) :
    fixedSpace ρ A ≃ₗ[ZMod 2] P where
  toFun v := ⟨M.coordinates v, (hP v).mp v.property⟩
  invFun X := ⟨M.coordinates.symm X, (hP _).mpr (by rw [M.coordinates.apply_symm_apply]; exact X.property)⟩
  left_inv v := by apply Subtype.ext; exact M.coordinates.symm_apply_apply v
  right_inv X := by apply Subtype.ext; exact M.coordinates.apply_symm_apply X
  map_add' _ _ := by apply Subtype.ext; exact M.coordinates.map_add _ _
  map_smul' _ _ := by apply Subtype.ext; exact M.coordinates.map_smul _ _

theorem fixedCodim_of_model_space (A : Subgroup G)
    (P : Submodule (fixedField s) (Space s))
    (hP : ∀ v, v ∈ fixedSpace ρ A ↔ M.coordinates v ∈ P) :
    fixedCodim ρ A + s * Module.finrank (fixedField s) P = 4 * s := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  have he := fixedCodim_add_finrank ρ A
  rw [(M.fixedCoordinatesEquiv A P hP).finrank_eq,
    model_subspace_binary_finrank, M.finrank_eq] at he
  exact he

/-- Fixed vectors transported along the marked layer embedding, with the literal
image subgroup on the original carrier. -/
theorem mem_modelImage_fixedSpace_iff
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) (v : V) :
    v ∈ fixedSpace ρ (M.modelImage B) ↔
      M.coordinates v ∈ fixedSpace (SL2.BinarySmall.hermitian s) B := by
  constructor
  · intro hv b
    have he := congrArg M.coordinates (hv ⟨M.modelEmbedding b, mem_map_of_mem _ b.property⟩)
    change M.coordinates (ρ (M.modelEmbedding b) v) = M.coordinates v at he
    rw [M.modelEmbedding_intertwines] at he
    exact he
  · intro hv g
    obtain ⟨b, hb, he⟩ := g.property
    apply M.coordinates.injective
    change M.coordinates (ρ g.val v) = M.coordinates v
    rw [← he, M.modelEmbedding_intertwines]
    exact hv ⟨b, hb⟩

section ActualActor
variable [L.Normal] {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
  (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
  (hreal : ∀ v, M.coordinates (ρ t v) = conjugationLinear s (M.coordinates v))

include ht2 htL ht hreal

omit hreal in
/-- Every element of the literal X is a fixed-field root or that root times t. -/
theorem outerActor_mem_cases {g : G} (hg : g ∈ M.outerActor t) :
    ∃ u : fixedField s, g = M.modelEmbedding (upper s u.val) ∨
      g = M.modelEmbedding (upper s u.val) * t := by
  classical
  let R := M.modelImage (fixedRootGroup s)
  have hc : t ∈ centralizer (R : Set G) := by
    rintro a ⟨b, hb, rfl⟩
    exact ((M.commute_modelEmbedding_iff ht b).mpr hb.2).symm
  have hn : zpowers t ≤ normalizer (R : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hc)
  have hg' : g ∈ (R : Set G) * (zpowers t : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left R (zpowers t) hn]
    exact hg
  obtain ⟨a, ⟨a', ha', rfl⟩, b, hb, hab⟩ := hg'
  obtain ⟨u, rfl⟩ := (mem_fixedRootGroup_iff s a').mp ha'
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 (fun he => htL (he ▸ L.one_mem))
  have hfin : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ht2⟩
  change b ∈ zpowers t at hb
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hto] at hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  have hi2 : i < 2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  refine ⟨u, ?_⟩
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using hab.symm)
  · exact Or.inr (by simpa using hab.symm)

omit ht2 htL ht [L.Normal] in
theorem outerRoot_intertwines (u : fixedField s) (v : V) :
    M.coordinates (ρ (M.modelEmbedding (upper s u.val) * t) v) =
      outerRootAction s u (M.coordinates v) := by
  rw [map_mul, Module.End.mul_apply, M.modelEmbedding_intertwines, hreal]
  rfl

/-- Every local displacement belongs to the actual fixed root plane. -/
theorem outerActor_displacement_mem {g : G} (hg : g ∈ M.outerActor t) (v : V) :
    M.coordinates (ρ g v - v) ∈
      fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) := by
  rw [map_sub]
  obtain ⟨u, he | he⟩ := M.outerActor_mem_cases ht2 htL ht hg
  · rw [he, M.modelEmbedding_intertwines]
    exact rootDifference_mem_fixedRoot s u (M.coordinates v)
  · rw [he, M.outerRoot_intertwines hreal]
    exact outerRootDifference_mem_fixedRoot s u (M.coordinates v)

theorem outerActor_fixes_plane {g : G} (hg : g ∈ M.outerActor t) {v : V}
    (hv : M.coordinates v ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s)) :
    ρ g v = v := by
  apply M.coordinates.injective
  obtain ⟨u, he | he⟩ := M.outerActor_mem_cases ht2 htL ht hg
  · rw [he, M.modelEmbedding_intertwines]
    exact hv ⟨upper s u.val, (mem_fixedRootGroup_iff s _).mpr ⟨u, rfl⟩⟩
  · rw [he, M.outerRoot_intertwines hreal]
    exact outerRoot_fixes_fixedRoot s u hv

/-- Quadraticity on the original representation, conditional only on realization. -/
theorem outerActor_quadratic : IsQuadratic ρ (M.outerActor t) := by
  intro a ha b hb v
  exact M.outerActor_fixes_plane ht2 htL ht hreal ha
    (M.outerActor_displacement_mem ht2 htL ht hreal hb v)

theorem outerActor_fixed_iff (v : V) :
    v ∈ fixedSpace ρ (M.outerActor t) ↔ M.coordinates v ∈
      Representation.invariants ((action s).comp (fixedRootGroup s).subtype) := by
  constructor
  · intro hv a
    have he := congrArg M.coordinates (hv ⟨M.modelEmbedding a,
      mem_sup_left (mem_map_of_mem M.modelEmbedding a.property)⟩)
    change M.coordinates (ρ (M.modelEmbedding a) v) = M.coordinates v at he
    rw [M.modelEmbedding_intertwines] at he
    exact he
  · intro hv g
    exact M.outerActor_fixes_plane ht2 htL ht hreal g.property hv

/-- X fixes the K-plane of R_t, transported from the given binary module. -/
theorem outerActor_fixedModelSpace : M.fixedModelSpace (M.outerActor t) =
    Representation.invariants ((action s).comp (fixedRootGroup s).subtype) :=
  M.fixedModelSpace_eq_of_mem_iff _ _ (M.outerActor_fixed_iff ht2 htL ht hreal)

theorem outerActor_fixed_Kfinrank :
    Module.finrank (fixedField s) (M.fixedModelSpace (M.outerActor t)) = 2 := by
  rw [M.outerActor_fixedModelSpace ht2 htL ht hreal, fixedRoot_fixed_Kfinrank]

theorem outerActor_fixedCodim : fixedCodim ρ (M.outerActor t) = 2 * s := by
  have he := M.fixedCodim_of_model_space _ _ (M.outerActor_fixed_iff ht2 htL ht hreal)
  rw [fixedRoot_fixed_Kfinrank] at he
  omega

theorem outerActor_actionRatio :
    actionRatio ρ (M.outerActor t) = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) := by
  rw [actionRatio, M.outerActor_fixedCodim ht2 htL ht hreal,
    M.outerActor_rank ht2 htL ht]
  norm_cast

/-- Equality of the literal binary fixed subspaces in the source module. -/
theorem outerActor_fixedSpace_eq_root :
    fixedSpace ρ (M.outerActor t) = fixedSpace ρ (M.modelImage (fixedRootGroup s)) := by
  ext v
  rw [M.outerActor_fixed_iff ht2 htL ht hreal, M.mem_modelImage_fixedSpace_iff]
  rfl

end ActualActor
section Subactors
variable [Finite G] [L.Normal] (h : SourceHypotheses ρ L)
  {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
  (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
  (hreal : ∀ v, M.coordinates (ρ t v) = conjugationLinear s (M.coordinates v))
  {A : Subgroup G} (hAX : A ≤ M.outerActor t) (hout : ¬ A ≤ L)

include h ht2 htL ht hreal hAX hout

omit h hreal [Finite G] in
/-- Every outer subgroup under consideration is automatically nontrivial elementary. -/
theorem localOuter_elementary : IsElementaryTwo A :=
  (M.outerActor_elementary ht2 htL ht).of_le hAX (fun he => hout (he ▸ bot_le))

omit hreal in
/-- Rank one is precisely the cyclic outer case, with an actual root-times-t generator. -/
theorem localOuter_rank_one_generator (hr : rank A = 1) :
    ∃ u : fixedField s, A = zpowers (M.modelEmbedding (upper s u.val) * t) := by
  have hAE := M.localOuter_elementary ht2 htL ht hAX hout
  let : IsElementaryAbelian 2 A := hAE.2
  have hi : A ⊓ L = ⊥ := by
    by_contra hne
    have hp := (hAE.of_le inf_le_left hne).rank_pos
    have he := M.outer_elementary_rank h A hout
    omega
  obtain ⟨a, ha, haL⟩ := Set.not_subset.mp hout
  obtain ⟨u, he | he⟩ := M.outerActor_mem_cases ht2 htL ht (hAX ha)
  · exact (haL (he ▸ M.modelImage_le_layer _
      (mem_map_of_mem _ ((mem_fixedRootGroup_iff s _).mpr ⟨u, rfl⟩)))).elim
  · refine ⟨u, ?_⟩
    rw [M.outer_elementary_decomposition h A ha haL, hi, bot_sup_eq, he]

omit h ht2 htL ht hAX hout [Finite G] [L.Normal] in
/-- The equation trace(z)=u b for the literal cyclic outer generator. -/
theorem outerRoot_cyclic_fixed_iff (u : fixedField s) (v : V) :
    v ∈ fixedSpace ρ (zpowers (M.modelEmbedding (upper s u.val) * t)) ↔
      M.coordinates v ∈ outerRootFixedHyperplane s u := by
  rw [mem_fixedSpace_zpowers_iff, ← M.coordinates.injective.eq_iff,
    M.outerRoot_intertwines hreal]
  exact (mem_outerRootFixedHyperplane_iff s u _).symm

/-- The transported fixed K-space of any rank-one outer actor is a hyperplane. -/
theorem localOuter_rank_one_fixed_space (hr : rank A = 1) :
    ∃ u : fixedField s,
      A = zpowers (M.modelEmbedding (upper s u.val) * t) ∧
      M.fixedModelSpace A = outerRootFixedHyperplane s u := by
  obtain ⟨u, rfl⟩ := M.localOuter_rank_one_generator h ht2 htL ht hAX hout hr
  exact ⟨u, rfl, M.fixedModelSpace_eq_of_mem_iff _ _ (M.outerRoot_cyclic_fixed_iff hreal u)⟩

theorem localOuter_rank_one_Kfinrank (hr : rank A = 1) :
    Module.finrank (fixedField s) (M.fixedModelSpace A) = 3 := by
  obtain ⟨u, _, he⟩ := M.localOuter_rank_one_fixed_space h ht2 htL ht hreal hAX hout hr
  rw [he, outerRootFixedHyperplane_finrank]

theorem localOuter_rank_one_fixedCodim (hr : rank A = 1) : fixedCodim ρ A = s := by
  obtain ⟨u, rfl⟩ := M.localOuter_rank_one_generator h ht2 htL ht hAX hout hr
  have he := M.fixedCodim_of_model_space _ _ (M.outerRoot_cyclic_fixed_iff hreal u)
  rw [outerRootFixedHyperplane_finrank] at he
  omega

theorem localOuter_rank_one_actionRatio (hr : rank A = 1) : actionRatio ρ A = s := by
  rw [actionRatio, M.localOuter_rank_one_fixedCodim h ht2 htL ht hreal hAX hout hr, hr]
  simp

/-- A noncyclic outer subgroup contains a nonidentity inner fixed-field root,
which forces exactly the common fixed K-plane. -/
theorem localOuter_noncyclic_fixed_iff (hr : 2 ≤ rank A) (v : V) :
    v ∈ fixedSpace ρ A ↔ M.coordinates v ∈
      Representation.invariants ((action s).comp (fixedRootGroup s).subtype) := by
  have hAE := M.localOuter_elementary ht2 htL ht hAX hout
  let : IsElementaryAbelian 2 A := hAE.2
  constructor
  · intro hv
    have hi : A ⊓ L ≠ ⊥ := by
      intro he
      have hh := M.outer_elementary_rank h A hout
      rw [he, Representation.BinaryOffender.rank_bot] at hh
      omega
    obtain ⟨a, ha, ha1⟩ := (A ⊓ L).bot_or_exists_ne_one.resolve_left hi
    have haR : a ∈ M.modelImage (fixedRootGroup s) := by
      rw [← M.outerActor_inf_layer h ht2 htL ht]
      exact ⟨hAX ha.1, ha.2⟩
    obtain ⟨g, hg, rfl⟩ := haR
    obtain ⟨u, rfl⟩ := (mem_fixedRootGroup_iff s g).mp hg
    have hu : u ≠ 0 := by
      intro he
      subst u
      exact ha1 (by rw [show upper s (0 : fixedField s).val = 1 from transvection_coeff_zero _, map_one])
    apply (fixedField_root_fixed_iff s hu (M.coordinates v)).mp
    have he := congrArg M.coordinates (hv ⟨_, ha.1⟩)
    change M.coordinates (ρ (M.modelEmbedding (upper s u.val)) v) = M.coordinates v at he
    rw [M.modelEmbedding_intertwines] at he
    exact he
  · intro hv g
    exact M.outerActor_fixes_plane ht2 htL ht hreal (hAX g.property) hv

theorem localOuter_noncyclic_fixedModelSpace (hr : 2 ≤ rank A) :
    M.fixedModelSpace A = Representation.invariants ((action s).comp (fixedRootGroup s).subtype) :=
  M.fixedModelSpace_eq_of_mem_iff _ _
    (M.localOuter_noncyclic_fixed_iff h ht2 htL ht hreal hAX hout hr)

theorem localOuter_noncyclic_Kfinrank (hr : 2 ≤ rank A) :
    Module.finrank (fixedField s) (M.fixedModelSpace A) = 2 := by
  rw [M.localOuter_noncyclic_fixedModelSpace h ht2 htL ht hreal hAX hout hr,
    fixedRoot_fixed_Kfinrank]

theorem localOuter_noncyclic_fixedCodim (hr : 2 ≤ rank A) : fixedCodim ρ A = 2 * s := by
  have he := M.fixedCodim_of_model_space _ _
    (M.localOuter_noncyclic_fixed_iff h ht2 htL ht hreal hAX hout hr)
  rw [fixedRoot_fixed_Kfinrank] at he
  omega

theorem localOuter_noncyclic_actionRatio (hr : 2 ≤ rank A) :
    actionRatio ρ A = (2 * s : ℕ) / (rank A : ℝ≥0∞) := by
  rw [actionRatio, M.localOuter_noncyclic_fixedCodim h ht2 htL ht hreal hAX hout hr]

omit h hreal hout in
theorem localOuter_rank_le : rank A ≤ s + 1 := by
  rw [← M.outerActor_rank ht2 htL ht]
  exact Nat.log_mono_right (Nat.card_le_card_of_injective (Subgroup.inclusion hAX)
    (Subgroup.inclusion_injective hAX))

omit h hout [Finite G] in
theorem localOuter_quadratic : IsQuadratic ρ A := by
  intro a ha b hb v
  exact M.outerActor_quadratic ht2 htL ht hreal a (hAX ha) b (hAX hb) v

/-- The exact threshold-two classification within X. Cyclic actors at s=2
remain present; the threshold condition does not characterize X. -/
theorem localOuter_threshold_iff (hs : 1 < s) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      rank A = s ∨ rank A = s + 1 ∨ (s = 2 ∧ rank A = 1) := by
  have hAE := M.localOuter_elementary ht2 htL ht hAX hout
  have hq := M.localOuter_quadratic ht2 htL ht hreal hAX
  have hp := hAE.rank_pos
  have hb := M.localOuter_rank_le ht2 htL ht hAX
  have hthreshold : actionRatio ρ A ≤ 2 ↔ fixedCodim ρ A ≤ 2 * rank A := by
    simpa using actionRatio_le_nat_iff ρ hAE 2
  rw [and_iff_right hAE, and_iff_right hq, hthreshold]
  by_cases hr : rank A = 1
  · rw [M.localOuter_rank_one_fixedCodim h ht2 htL ht hreal hAX hout hr]
    omega
  · have hr2 : 2 ≤ rank A := by omega
    rw [M.localOuter_noncyclic_fixedCodim h ht2 htL ht hreal hAX hout hr2]
    omega

/-- The minimum among outer elementary subgroups of X is attained only by X. -/
theorem localOuter_minimum (hs : 1 < s) :
    (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ≤ actionRatio ρ A ∧
      (actionRatio ρ A = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ↔ A = M.outerActor t) := by
  have hAE := M.localOuter_elementary ht2 htL ht hAX hout
  have hp := hAE.rank_pos
  have hb := M.localOuter_rank_le ht2 htL ht hAX
  have hX := M.outerActor_elementary ht2 htL ht
  have hXratio := M.outerActor_actionRatio ht2 htL ht hreal
  by_cases hr : rank A = 1
  · have hratio := M.localOuter_rank_one_actionRatio h ht2 htL ht hreal hAX hout hr
    have hlt : (2 * s : ℕ) / (s + 1 : ℝ≥0∞) < (s : ℝ≥0∞) := by
      apply (ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp))).mpr
      have hn : 2 * s < s * (s + 1) := by nlinarith
      exact_mod_cast hn
    refine ⟨by rw [hratio]; exact hlt.le, ?_⟩
    constructor
    · intro he
      rw [hratio] at he
      exact (ne_of_lt hlt he.symm).elim
    · intro he
      have hh := M.outerActor_rank ht2 htL ht
      rw [he] at hr
      omega
  · have hr2 : 2 ≤ rank A := by omega
    have hratio := M.localOuter_noncyclic_actionRatio h ht2 htL ht hreal hAX hout hr2
    refine ⟨?_, ?_⟩
    · rw [hratio]
      exact ENNReal.div_le_div_left (by exact_mod_cast hb) _
    · constructor
      · intro he
        rw [hratio] at he
        have hz : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
        have hc := (ENNReal.div_eq_div_iff (by positivity : (s + 1 : ℝ≥0∞) ≠ 0)
          (by simp) hz (by simp)).mp he
        have hcN : (s + 1) * (2 * s) = rank A * (2 * s) := by exact_mod_cast hc
        have hre : rank A = s + 1 := by nlinarith
        apply Subgroup.eq_of_le_of_card_ge hAX
        rw [hAE.card_eq_two_pow_rank, hX.card_eq_two_pow_rank,
          M.outerActor_rank ht2 htL ht, hre]
      · intro he
        rw [he, hXratio]

/-- All local actor data on the original representation, including both rank cases. -/
theorem localOuter_calculation (hs : 1 < s) :
    IsElementaryTwo A ∧ IsQuadratic ρ A ∧ rank A ≤ s + 1 ∧
      (rank A = 1 → Module.finrank (fixedField s) (M.fixedModelSpace A) = 3 ∧
        fixedCodim ρ A = s ∧ actionRatio ρ A = s) ∧
      (2 ≤ rank A → Module.finrank (fixedField s) (M.fixedModelSpace A) = 2 ∧
        fixedCodim ρ A = 2 * s ∧ actionRatio ρ A = (2 * s : ℕ) / (rank A : ℝ≥0∞)) ∧
      ((IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
        rank A = s ∨ rank A = s + 1 ∨ (s = 2 ∧ rank A = 1)) ∧
      ((2 * s : ℕ) / (s + 1 : ℝ≥0∞) ≤ actionRatio ρ A ∧
        (actionRatio ρ A = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ↔ A = M.outerActor t)) := by
  refine ⟨M.localOuter_elementary ht2 htL ht hAX hout,
    M.localOuter_quadratic ht2 htL ht hreal hAX,
    M.localOuter_rank_le ht2 htL ht hAX, ?_, ?_,
    M.localOuter_threshold_iff h ht2 htL ht hreal hAX hout hs,
    M.localOuter_minimum h ht2 htL ht hreal hAX hout hs⟩
  · intro hr
    exact ⟨M.localOuter_rank_one_Kfinrank h ht2 htL ht hreal hAX hout hr,
      M.localOuter_rank_one_fixedCodim h ht2 htL ht hreal hAX hout hr,
      M.localOuter_rank_one_actionRatio h ht2 htL ht hreal hAX hout hr⟩
  · intro hr
    exact ⟨M.localOuter_noncyclic_Kfinrank h ht2 htL ht hreal hAX hout hr,
      M.localOuter_noncyclic_fixedCodim h ht2 htL ht hreal hAX hout hr,
      M.localOuter_noncyclic_actionRatio h ht2 htL ht hreal hAX hout hr⟩

omit hAX hout in
/-- Every fixed-field parameter gives an actual cyclic outer actor. In degree
s=2 its action ratio is exactly two, so it belongs to the threshold family. -/
theorem outerRoot_cyclic_calculation (u : fixedField s) :
    let B := zpowers (M.modelEmbedding (upper s u.val) * t)
    B ≤ M.outerActor t ∧ ¬ B ≤ L ∧ rank B = 1 ∧ IsQuadratic ρ B ∧
      M.fixedModelSpace B = outerRootFixedHyperplane s u ∧
      Module.finrank (fixedField s) (M.fixedModelSpace B) = 3 ∧
      fixedCodim ρ B = s ∧ actionRatio ρ B = s := by
  let g := M.modelEmbedding (upper s u.val) * t
  have hu : upper s u.val ∈ fixedRootGroup s := (mem_fixedRootGroup_iff s _).mpr ⟨u, rfl⟩
  have hroot : M.modelEmbedding (upper s u.val) ∈ M.modelImage (fixedRootGroup s) :=
    mem_map_of_mem _ hu
  have hgX : g ∈ M.outerActor t := (M.outerActor t).mul_mem
    (mem_sup_left hroot) (mem_sup_right (mem_zpowers t))
  have hgL : g ∉ L := by
    intro he
    have hh := L.mul_mem (L.inv_mem (M.modelImage_le_layer _ hroot)) he
    exact htL (by simpa [g] using hh)
  have hBX : zpowers g ≤ M.outerActor t := zpowers_le.mpr hgX
  have hBL : ¬ zpowers g ≤ L := fun hh => hgL (hh (mem_zpowers g))
  let : IsElementaryAbelian 2 (M.outerActor t) := (M.outerActor_elementary ht2 htL ht).2
  have hg2 : g ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian g hgX
  have hgo : orderOf g = 2 := orderOf_eq_prime hg2 (fun he => hgL (he ▸ L.one_mem))
  have hr : rank (zpowers g) = 1 := by rw [rank, Nat.card_zpowers, hgo]; decide
  have hP := M.fixedModelSpace_eq_of_mem_iff _ _ (M.outerRoot_cyclic_fixed_iff hreal u)
  refine ⟨hBX, hBL, hr, M.localOuter_quadratic ht2 htL ht hreal hBX, hP, ?_,
    M.localOuter_rank_one_fixedCodim h ht2 htL ht hreal hBX hBL hr,
    M.localOuter_rank_one_actionRatio h ht2 htL ht hreal hBX hBL hr⟩
  rw [hP, outerRootFixedHyperplane_finrank]

/-- Noncyclic outer actors fix precisely the original root centralizer's fixed space. -/
theorem localOuter_noncyclic_fixedSpace_eq_root (hr : 2 ≤ rank A) :
    fixedSpace ρ A = fixedSpace ρ (M.modelImage (fixedRootGroup s)) := by
  ext v
  rw [M.localOuter_noncyclic_fixed_iff h ht2 htL ht hreal hAX hout hr,
    M.mem_modelImage_fixedSpace_iff]
  rfl

end Subactors

end OrthogonalModel
/-- The conditional source application for K.3.1.2 on the original module.
The sole additional realization identity is supplied independently; no ambient
conjugacy or global minimization statement is assumed here. -/
theorem SourceHypotheses.orthogonal_outer_local_geometry [Finite G]
    (h : SourceHypotheses ρ L) (M : OrthogonalModel s ρ L) (hs : 1 < s)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : letI : L.Normal := h.layer_normal
      M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (hreal : ∀ v, M.coordinates (ρ t v) = conjugationLinear s (M.coordinates v)) :
    letI : L.Normal := h.layer_normal
    IsElementaryTwo (M.outerActor t) ∧ IsQuadratic ρ (M.outerActor t) ∧
      Module.finrank (fixedField s) (M.fixedModelSpace (M.outerActor t)) = 2 ∧
      fixedCodim ρ (M.outerActor t) = 2 * s ∧
      actionRatio ρ (M.outerActor t) = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
      ∀ A : Subgroup G, A ≤ M.outerActor t → ¬ A ≤ L →
        IsQuadratic ρ A ∧
        ((IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
          rank A = s ∨ rank A = s + 1 ∨ (s = 2 ∧ rank A = 1)) ∧
        ((2 * s : ℕ) / (s + 1 : ℝ≥0∞) ≤ actionRatio ρ A ∧
          (actionRatio ρ A = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ↔ A = M.outerActor t)) := by
  let : L.Normal := h.layer_normal
  refine ⟨M.outerActor_elementary ht2 htL ht, M.outerActor_quadratic ht2 htL ht hreal,
    M.outerActor_fixed_Kfinrank ht2 htL ht hreal, M.outerActor_fixedCodim ht2 htL ht hreal,
    M.outerActor_actionRatio ht2 htL ht hreal, ?_⟩
  intro A hAX hout
  exact ⟨M.localOuter_quadratic ht2 htL ht hreal hAX,
    M.localOuter_threshold_iff h ht2 htL ht hreal hAX hout hs,
    M.localOuter_minimum h ht2 htL ht hreal hAX hout hs⟩

end CFSG.Quasithin.ChapterK.RankOne
