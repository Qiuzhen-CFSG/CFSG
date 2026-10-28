module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorThompson
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActorsGeneral
public import Theory.Representation.BinaryOffender.SectionKernelBudget

/-!
# Small full actors and large higher-Thompson images in the original tensor branch

An elementary subgroup of the seed normalizer moving fewer than 2n binary
coordinates has rank at most one. The determinant coordinates first kill its
field action and turn the common fixed space into a quadratic hyperplane.
Its pointwise orthogonal stabilizer has at most two elements.

Passing from the seed to the original full module keeps the entire actor
kernel. The seed image and its pointwise kernel consume additive parts of the
full fixed-codimension budget. If the seed image moves, it consumes at least n;
any kernel element moving the full module would consume another n. Thus below
2n the seed image detects the full action. Every nontrivial full actor has an
M-conjugate moving the seed, and small displacement makes that conjugate
preserve it. This proves the rank-one bound for every original elementary
actor, without assuming seed stability under all of M or seed/full equality.

B.2.4 now forces a moving higher-Thompson actor with j+1<n to have full fixed
codimension at least 2n and image rank at least 2n-j. The literal Hall alternative
retains these bounds along with the original quotient kernel, both component
markings, determinant field action and ambient corank bounds. Excluding the
remaining large actors and completing the generation/Cartan argument are still
required for the unconditional central Hall conclusion.
Source: Aschbacher--Smith H.1.1 and 9.2.1--7, printed pp.378,730--732;
10.1.1--2 and 10.2.3, pp.741--742,745, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Small elementary seed images in the remaining natural tensor have rank at most one. -/
theorem original_even_seed_small_actor_rank
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup (linearNormalizer (originalSeedAction D)))
    [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (normalizerRepresentation (originalSeedAction D)) A < 2*n) :
    rank A ≤ 1 := by
  have hAelem : IsElementaryAbelian 2 A := inferInstance
  obtain ⟨q,hq,_,_,_,σ,_,hf,hσ,α,⟨b⟩⟩ :=
    original_even_seed_natural_tensor D c n hn e ht htn hsep
  let a := b.trans (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.binaryTensorEquiv α)
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext z
    constructor
    · rintro ⟨g,rfl⟩; exact ⟨q g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hF : 2 < Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact lt_of_lt_of_le (by norm_num : 2 < 2^3) (Nat.pow_le_pow_right (by decide) hn)
  have hbound : ∀ (C : Subgroup (linearNormalizer σ)), IsElementaryAbelian 2 C →
      fixedCodim (normalizerRepresentation σ) C < 2*n → rank C ≤ 1 := by
    intro C hC hsmall
    let := hC
    apply ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.rank_le_one_of_fixedCodim_lt_twice_degree
      hF σ hf (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.marking α)
      a.toLinearEquiv (fun g v => LinearMap.congr_fun (a.isIntertwining' g) v) C
    rwa [finrank_field _ (GaloisField.card 2 n (by omega))]
  unfold normalizerRepresentation linearNormalizer at hbound
  rw [←himage] at hbound
  exact hbound A hAelem hsmall

/-- The original actor on the seed, with its pointwise kernel retained. -/
@[expose] def originalPreservingSeedHom (A : Subgroup D.maximalLocal)
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G)) :
    A →* linearNormalizer (originalSeedAction D) :=
  (originalSeedAmbientNormalizerHom D).comp
    ((D.maximalLocal.subtype.comp A.subtype).codRestrict
      (D.maximalLocal ⊓ normalizer (D.seed : Set G))
      (fun a => ⟨a.val.property,hs (mem_map_of_mem _ a.property)⟩))

/-- Its literal kernel is the pointwise centralizer of the original seed. -/
theorem originalPreservingSeedHom_mem_ker (A : Subgroup D.maximalLocal)
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G)) (a : A) :
    a ∈ (originalPreservingSeedHom D A hs).ker ↔
      ((a : D.maximalLocal) : G) ∈ centralizer (D.seed : Set G) := by
  constructor
  · intro ha v hv
    have hh := congrArg (fun x : linearNormalizer (originalSeedAction D) =>
      x.val.val (Additive.ofMul (⟨v,hv⟩ : D.seed))) ha
    have he := congrArg (fun w : Additive D.seed => (w.toMul : G)) hh
    change (a.val:G)*v*(a.val:G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a.val:G)*(v.toMul:G)*(a.val:G)⁻¹ = (v.toMul:G)
    rw [←ha v.toMul v.toMul.property,mul_inv_cancel_right]

/-- Restriction to the preserved seed cannot increase common fixed codimension.
The full-module pointwise kernel and the seed kernel are kept separate. -/
theorem original_preserving_seed_fixedCodim_le (A : Subgroup D.maximalLocal)
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G)) :
    fixedCodim (normalizerRepresentation (originalSeedAction D))
      (originalPreservingSeedHom D A hs).range ≤
    fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  have hSF : D.seed ≤ D.fullModule := (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  let τ : Representation (ZMod 2) A (Additive D.seed) := (normalizerRepresentation (originalSeedAction D)).comp (originalPreservingSeedHom D A hs)
  let ρ : Representation (ZMod 2) A (Additive D.fullModule) := (originalFullAction D).comp A.subtype
  let i : τ.IntertwiningMap ρ := {
    toLinearMap := (inclusion hSF).toAdditive.toZModLinearMap 2
    isIntertwining' a := by apply LinearMap.ext; intro v; rfl }
  have hi : Function.Injective i.toLinearMap := by
    intro v w hvw
    exact Additive.toMul.injective (inclusion_injective hSF hvw)
  let E := LinearEquiv.ofInjective i.toLinearMap hi
  have he := fixedCodim_map_equivariant τ i.range.toRepresentation (MonoidHom.id A) E
    (fun a v => by apply Subtype.ext; rfl) ⊤
  rw [Subgroup.map_id] at he
  have hb := fixedCodim_subrepresentation_le ρ i.range ⊤
  rw [←he] at hb
  have hτ : fixedCodim τ ⊤ = fixedCodim (normalizerRepresentation (originalSeedAction D))
      (originalPreservingSeedHom D A hs).range := by
    rw [fixedCodim,fixedSpace_comp_map,←MonoidHom.range_eq_map]
    rfl
  have hρ : fixedCodim ρ ⊤ =
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) := by
    have he : ρ = (automizerRepresentation D.fullModule).comp
        ((originalFullAutomizerHom D).comp A.subtype) := rfl
    rw [he,fixedCodim,fixedSpace_comp_map,←MonoidHom.range_eq_map,MonoidHom.range_comp,Subgroup.range_subtype]
    rfl
  rwa [hτ,hρ] at hb

/-- The actual seed image of a low-budget Thompson actor has rank at most one.
No faithfulness of the seed restriction is inferred. -/
theorem original_even_thompson_seed_image_rank
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥)
    (hsmall : rank (A.map (originalFullAutomizerHom D)) + j < 2*n) :
    ∃ hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G),
      rank (originalPreservingSeedHom D A hs).range ≤ 1 := by
  have hs := original_even_thompson_actor_preserves_seed D c n hn e ht htn hsep
    j A hA hne (by omega)
  refine ⟨hs,?_⟩
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (originalPreservingSeedHom D A hs).range :=
    IsElementaryAbelian.of_surjective _ (originalPreservingSeedHom D A hs).rangeRestrict_surjective
  apply original_even_seed_small_actor_rank D c n hn e ht htn hsep
  exact (original_preserving_seed_fixedCodim_le D A hs).trans_lt
    ((original_full_thompson_fixedCodim_bound D j A hA hne).trans_lt hsmall)


/-- The literal seed kernel and seed image share the original full-module budget. -/
theorem original_preserving_seed_kernel_budget (A : Subgroup D.maximalLocal)
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G)) :
    fixedCodim ((originalFullAction D).comp A.subtype) (originalPreservingSeedHom D A hs).ker +
      fixedCodim (normalizerRepresentation (originalSeedAction D))
        (originalPreservingSeedHom D A hs).range ≤
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  have hSF : D.seed ≤ D.fullModule := (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  let τ : Representation (ZMod 2) A (Additive D.seed) :=
    (normalizerRepresentation (originalSeedAction D)).comp (originalPreservingSeedHom D A hs)
  let ρ : Representation (ZMod 2) A (Additive D.fullModule) := (originalFullAction D).comp A.subtype
  let i : τ.IntertwiningMap ρ := {
    toLinearMap := (inclusion hSF).toAdditive.toZModLinearMap 2
    isIntertwining' a := by apply LinearMap.ext; intro v; rfl }
  have hi : Function.Injective i.toLinearMap := by
    intro v w hvw
    exact Additive.toMul.injective (inclusion_injective hSF hvw)
  have hb := fixedCodim_kernel_add_of_injective_intertwiner ρ τ i hi
  have hk : τ.ker = (originalPreservingSeedHom D A hs).ker := by
    ext a
    constructor
    · intro ha
      apply Subtype.ext
      exact Units.ext ha
    · intro ha
      change normalizerRepresentation (originalSeedAction D) (originalPreservingSeedHom D A hs a) = 1
      rw [show originalPreservingSeedHom D A hs a = 1 from ha,map_one]
  have hτ : fixedCodim τ ⊤ = fixedCodim (normalizerRepresentation (originalSeedAction D))
      (originalPreservingSeedHom D A hs).range := by
    rw [fixedCodim,fixedSpace_comp_map,←MonoidHom.range_eq_map]
    rfl
  have hρ : fixedCodim ρ ⊤ =
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) := by
    have he : ρ = (automizerRepresentation D.fullModule).comp
        ((originalFullAutomizerHom D).comp A.subtype) := rfl
    rw [he,fixedCodim,fixedSpace_comp_map,←MonoidHom.range_eq_map,MonoidHom.range_comp,Subgroup.range_subtype]
    rfl
  rwa [hk,hτ,hρ] at hb

/-- If the seed image moves and the full codimension is below 2n, its kernel
already acts trivially on the full module. This discharges faithfulness rather
than assuming a faithful restriction to either component. -/
theorem original_even_small_preserving_seed_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup D.maximalLocal)
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G))
    (hmove : (originalPreservingSeedHom D A hs).range ≠ ⊥)
    (hsmall : fixedCodim (automizerRepresentation D.fullModule)
      (A.map (originalFullAutomizerHom D)) < 2*n) :
    (originalPreservingSeedHom D A hs).ker ≤
      ((originalFullAutomizerHom D).comp A.subtype).ker := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  let f := originalPreservingSeedHom D A hs
  have hseed : n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) f.range := by
    obtain ⟨a,ha,hane⟩ := f.range.bot_or_exists_ne_one.resolve_left hmove
    exact (original_even_seed_normalizer_displacement_ge D c n hn e ht htn hsep a hane).trans
      (operatorFixedCodim_le_fixedCodim _ f.range ha)
  intro a ha
  by_contra hnot
  have hnfull : originalFullAction D a.val ≠ 1 := by
    intro hz
    apply hnot
    change originalFullAutomizerHom D a.val = 1
    apply automizerRepresentation_injective D.fullModule
    exact hz.trans (map_one _).symm
  have hlow := original_even_full_displacement_ge D c n hn e ht htn hsep a.val hnfull
  have hb := operatorFixedCodim_le_fixedCodim ((originalFullAction D).comp A.subtype) f.ker ha
  have hk := original_preserving_seed_kernel_budget D A hs
  change operatorFixedCodim (originalFullAction D a.val) ≤ _ at hb
  change _ + fixedCodim (normalizerRepresentation (originalSeedAction D)) f.range ≤ _ at hk
  dsimp only [f] at hb hseed hk
  omega

/-- A small elementary actor that moves the seed has full image rank at most one;
its entire pointwise seed kernel has been proved trivial on the full module. -/
theorem original_even_small_preserving_full_rank
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup D.maximalLocal) [IsElementaryAbelian 2 A]
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G))
    (hmove : (originalPreservingSeedHom D A hs).range ≠ ⊥)
    (hsmall : fixedCodim (automizerRepresentation D.fullModule)
      (A.map (originalFullAutomizerHom D)) < 2*n) :
    rank (A.map (originalFullAutomizerHom D)) ≤ 1 := by
  let f := originalPreservingSeedHom D A hs
  let g := (originalFullAutomizerHom D).comp A.subtype
  have hk := original_even_small_preserving_seed_kernel D c n hn e ht htn hsep A hs hmove hsmall
  have hc : Nat.card g.range ≤ Nat.card f.range := by
    rw [←Subgroup.index_ker,←Subgroup.index_ker]
    exact Subgroup.index_antitone hk
  have hr := Nat.log_mono_right (b := 2) hc
  have hgr : g.range = A.map (originalFullAutomizerHom D) := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  rw [hgr] at hr
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective _ f.rangeRestrict_surjective
  exact hr.trans (original_even_seed_small_actor_rank D c n hn e ht htn hsep f.range
    ((original_preserving_seed_fixedCodim_le D A hs).trans_lt hsmall))


/-- The same common fixed codimension on M and on its literal full automizer image. -/
theorem original_full_fixedCodim_map (A : Subgroup D.maximalLocal) :
    fixedCodim (originalFullAction D) A =
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) := by
  have he : originalFullAction D = (automizerRepresentation D.fullModule).comp
      (originalFullAutomizerHom D) := rfl
  rw [he,fixedCodim,fixedSpace_comp_map]
  rfl

/-- A nontrivial full action has an M-conjugate moving the original seed. -/
theorem original_exists_conjugate_moving_seed (A : Subgroup D.maximalLocal)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥) :
    ∃ m : D.maximalLocal,
      ¬ (A.map (MulAut.conj m).toMonoidHom).map D.maximalLocal.subtype ≤
        centralizer (D.seed : Set G) := by
  by_contra! hall
  apply hne
  apply (Subgroup.map_eq_bot_iff A).mpr
  intro a ha
  have hfix (k : D.maximalLocal) :
      ((k⁻¹*a*k : D.maximalLocal) : G) ∈ centralizer (D.seed : Set G) := by
    apply hall k⁻¹
    have hh := mem_map_of_mem D.maximalLocal.subtype
      (mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom ha)
    change ((k⁻¹ * a * (k⁻¹)⁻¹ : D.maximalLocal) : G) ∈ _ at hh
    simpa only [inv_inv] using hh
  have hc : D.fullModule ≤ centralizer ({(a:G)} : Set G) := by
    rw [D.fullModule_eq_seed_orbit]
    apply iSup_le
    intro k
    rintro _ ⟨v,hv,rfl⟩ b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    have hh := hfix k v hv
    change v*((k:G)⁻¹*(a:G)*(k:G)) = ((k:G)⁻¹*(a:G)*(k:G))*v at hh
    change (a:G)*((k:G)*v*(k:G)⁻¹) = ((k:G)*v*(k:G)⁻¹)*(a:G)
    calc
      _ = (k:G)*(((k:G)⁻¹*(a:G)*(k:G))*v)*(k:G)⁻¹ := by group
      _ = (k:G)*(v*((k:G)⁻¹*(a:G)*(k:G)))*(k:G)⁻¹ := by rw [hh]
      _ = _ := by group
  change originalFullAutomizerHom D a = 1
  apply automizerRepresentation_injective D.fullModule
  rw [map_one]
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  change (a:G)*(v.toMul:G)*(a:G)⁻¹ = (v.toMul:G)
  rw [hc v.toMul.property a rfl,mul_inv_cancel_right]

/-- Every original elementary actor of full fixed codimension below 2n has
full image rank at most one, without a seed-movement or seed-faithfulness premise. -/
theorem original_even_small_full_actor_rank
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup D.maximalLocal) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (automizerRepresentation D.fullModule)
      (A.map (originalFullAutomizerHom D)) < 2*n) :
    rank (A.map (originalFullAutomizerHom D)) ≤ 1 := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  by_cases hne : A.map (originalFullAutomizerHom D) = ⊥
  · simp [hne,rank]
  obtain ⟨m,hm⟩ := original_exists_conjugate_moving_seed D A hne
  let C := A.map (MulAut.conj m).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hc : fixedCodim (automizerRepresentation D.fullModule)
      (C.map (originalFullAutomizerHom D)) < 2*n := by
    rw [←original_full_fixedCodim_map D,show C = A.map (MulAut.conj m).toMonoidHom from rfl,
      fixedCodim_map_conj,original_full_fixedCodim_map D]
    exact hsmall
  have hs : C.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G) := by
    rintro _ ⟨a,ha,rfl⟩
    apply original_seed_stable_of_full_displacement_lt D c a
    have hh := operatorFixedCodim_le_fixedCodim (originalFullAction D) C ha
    rw [original_full_fixedCodim_map D] at hh
    rw [original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep]
    omega
  have hmove : (originalPreservingSeedHom D C hs).range ≠ ⊥ := by
    intro hz
    apply hm
    rintro _ ⟨a,ha,rfl⟩
    apply (originalPreservingSeedHom_mem_ker D C hs ⟨a,ha⟩).mp
    have hmem : originalPreservingSeedHom D C hs ⟨a,ha⟩ ∈
        (originalPreservingSeedHom D C hs).range := ⟨⟨a,ha⟩,rfl⟩
    rw [hz] at hmem
    exact mem_bot.mp hmem
  have hr := original_even_small_preserving_full_rank D c n hn e ht htn hsep C hs hmove hc
  have he : C.map (originalFullAutomizerHom D) =
      (A.map (originalFullAutomizerHom D)).map
        (MulAut.conj (originalFullAutomizerHom D m)).toMonoidHom := by
    rw [show C = A.map (MulAut.conj m).toMonoidHom from rfl,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change originalFullAutomizerHom D (m*a*m⁻¹) =
      originalFullAutomizerHom D m * originalFullAutomizerHom D a *
        (originalFullAutomizerHom D m)⁻¹
    rw [map_mul,map_mul,map_inv]
  rwa [he,rank_map_conj] at hr

/-- Below j = n-1, every moving higher-Thompson actor must have full fixed
codimension at least 2n and image rank at least 2n-j. -/
theorem original_even_thompson_actor_large
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (hj : j+1 < n) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥) :
    2*n ≤ fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ∧
      2*n-j ≤ rank (A.map (originalFullAutomizerHom D)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map (originalFullAutomizerHom D)) := IsElementaryAbelian.map _
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  have hb := original_full_thompson_fixedCodim_bound D j A hA hne
  have hl := (original_even_full_localM_ge D c n hn e ht htn hsep).trans
    (moduleM_le_fixedCodim (automizerRepresentation D.fullModule) ⟨hne,inferInstance⟩)
  have hlarge : 2*n ≤ fixedCodim (automizerRepresentation D.fullModule)
      (A.map (originalFullAutomizerHom D)) := by
    by_contra! hsmall
    have hr := original_even_small_full_actor_rank D c n hn e ht htn hsep A hsmall
    omega
  exact ⟨hlarge,by omega⟩

/-- The original H-star alternative now forces a large moving Thompson image
whenever its generation parameter is below n-1. -/
@[expose] def OriginalEvenLargeThompsonAnalysis (H : Subgroup G) (n : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j+1 < n → generationParameter H ≤ j →
    ∃ A : Subgroup D.maximalLocal,
      A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j ∧
      IsElementaryTwo (A.map (originalFullAutomizerHom D)) ∧
      2*n ≤ fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ∧
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ≤
        rank (A.map (originalFullAutomizerHom D)) + j ∧
      2*n-j ≤ rank (A.map (originalFullAutomizerHom D))

/-- The large-image alternative for the literal original H-star group. -/
theorem original_even_large_thompson_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenLargeThompsonAnalysis D H n := by
  intro j hj hjn hgen
  obtain ⟨A,hA,he,_hl,hb,_hr⟩ :=
    original_even_exists_thompson_actor D c n hn e ht htn hsep j hj (by omega) hgen
  obtain ⟨hl,hr⟩ := original_even_thompson_actor_large D c n hn e ht htn hsep j hjn A hA he.1
  exact ⟨A,hA,he,hl,hb,hr⟩

/-- The literal central Hall alternative retains all quotient and field markings,
now with the full-actor rank-one exclusion and the resulting large Thompson images.
The remaining large-image, generation and Cartan exclusion is still required. -/
theorem original_hall_conclusion_or_natural_tensor_large_thompson
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          n ≤ moduleM (normalizerRepresentation (originalSeedAction D)) ∧
          (∀ a : linearNormalizer (originalSeedAction D), a ≠ 1 →
            n ≤ operatorFixedCodim (normalizerRepresentation (originalSeedAction D) a)) ∧
          (∀ a : Automizer D.fullModule, a ≠ 1 →
            n ≤ operatorFixedCodim (automizerRepresentation D.fullModule a)) ∧
          n ≤ localM D.fullModule ∧
          (n : ℕ∞) ≤ globalR D.fullModule ∧
          (∀ U : Subgroup G, U ≤ D.fullModule → subgroupCorank D.fullModule U < n →
            centralizer (U : Set G) ≤ D.maximalLocal) ∧
          OriginalEvenThompsonAnalysis D H ht n e ∧
          (∀ A : Subgroup D.maximalLocal, IsElementaryAbelian 2 A →
            fixedCodim (automizerRepresentation D.fullModule)
              (A.map (originalFullAutomizerHom D)) < 2*n →
            rank (A.map (originalFullAutomizerHom D)) ≤ 1) ∧
          OriginalEvenLargeThompsonAnalysis D H n := by
  rcases original_hall_conclusion_or_natural_tensor_thompson D c with hh |
    ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hm,hdisp,hfull,hl,hr,hcent,hth⟩
  · exact Or.inl hh
  · refine Or.inr ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hm,hdisp,hfull,hl,hr,hcent,hth,?_,
      original_even_large_thompson_analysis D c n hn e ht htn hs⟩
    intro A hA hsmall
    let := hA
    exact original_even_small_full_actor_rank D c n hn e ht htn hs A hsmall

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
