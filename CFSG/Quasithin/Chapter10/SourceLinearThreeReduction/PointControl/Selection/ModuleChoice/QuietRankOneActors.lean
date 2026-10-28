module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietRankOneLocal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietSeedActors
public import Theory.SpecificGroups.FFLinearPrimeCore
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorGeometry
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy

/-!
# Full-action actors on the original quiet rank-one tensor

Faithfulness on the original normal component square bounds every starred
actor's rank by twice the field degree, so its cubic budget bounds fixed
codimension by the actual tensor-seed degree. Equality would force the
individual and common fixed spaces to coincide; the tensor normalizer's
rank gap excludes this for actors preserving the seed. Conjugacy into the
original Sylow image then gives strict displacement and seed preservation
for every starred actor, with the full action kernel retained throughout.

This is the actor-preservation step toward recognizing the original full
module. Source: Aschbacher--Smith D.3.21 and 3.2.6, printed pp.205--207,581,
with the automorphism-rank estimate of G.9.3, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every original starred actor has rank at most twice the field degree and
moves at most the degree of the original tensor seed. -/
theorem quiet_rankOne_starred_rank_and_codimension
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn3 : 3 ≤ n)
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ, rank A ≤ 2*n ∧ fixedCodim ρ A ≤ 4*n := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨p,hp,hpk,_,_⟩ := original_component_product_quotient D hn ht htn
  obtain ⟨i,hi,_,hdiagram⟩ := original_component_product_embedding D hn p hp hpk
  have hrange : i.range = X := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := hp a
      rw [hdiagram]
      exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p ⟨x,hx⟩,hdiagram ⟨x,hx⟩⟩
  let e := (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hi).symm
  let S := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv cL
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr cL.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  intro A hA
  have hAC := quiet_full_actor_starred_faithful D hmany hmin hn hJ hd A hA
  let f : A →* MulAut X := (MulAut.conjNormal : _ →* MulAut X).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    refine ⟨a.property,?_⟩
    change (a : ChapterB.InternalThompsonAction.ActionQuotient U) ∈
      (MulAut.conjNormal : _ →* MulAut X).ker at ha
    rwa [MulAut.conjNormal_ker_eq_centralizer] at ha
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hfactor : primeRank 2 (MulAut S) ≤ n :=
    Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le (by omega)
      (GaloisField.card 2 n (by omega))
  have hpos : 0 < primeRank 2 (MulAut S) := by
    have hh := Theory.PSL2.root_two_rank_ge (GaloisField 2 n)
      (GaloisField.card 2 n (by omega))
    have he : primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) ≤
        primeRank 2 (MulAut S) := by
      rw [←primeRank_equiv 2 (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n))]
      exact Theory.GroupTheory.primeRank_le_of_injective 2 (MulAut.conj : S →* MulAut S)
        ((MonoidHom.ker_eq_bot_iff _).mp (by
          rw [Theory.GroupTheory.DoubleCoverCentralizer.conj_kernel,Theory.PSL2.sl2_center_eq_bot]))
    omega
  have hrAut : primeRank 2 (MulAut X) ≤ 2*n := by
    rw [primeRank_equiv 2 (MulAut.congr (e.trans (cL.prodCongr cL)))]
    exact (AutomorphismSquare.rank_bound (Theory.PSL2.sl2_center_eq_bot _) hpos).trans
      (Nat.mul_le_mul_left 2 hfactor)
  have hr : rank A ≤ 2*n := by
    have hcard := (primeRank_le_iff_elementary_card_le _).mp
      ((Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans hrAut) ⊤
      (IsElementaryAbelian.of_injective (p := 2) (⊤ : Subgroup A).subtype Subtype.val_injective)
    rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv,
      hA.1.2.1.card_eq_two_pow_rank] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  exact ⟨hr,hb.trans (by omega)⟩



local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

/-- If an element of the full preimage fails to preserve the original seed,
both actor bounds are equalities. Its individual fixed space is exactly the
common fixed space of the whole starred actor, on the original full module. -/
theorem quiet_rankOne_moving_seed_saturation
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ, ∀ m : D.maximalLocal, q m ∈ A →
      (m : G) ∉ normalizer (D.seed : Set G) →
      rank A = 2*n ∧ fixedCodim ρ A = 4*n ∧
        NaturalTensor.operatorFixedCodim (ρ (q m)) = 4*n ∧
        fixedSpace ρ A = LinearMap.ker (ρ (q m)-1) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let a : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  let E : Additive U ≃ₗ[ZMod 2] Additive D.fullModule :=
    a.toAdditive.toLinearEquiv (fun c v => ZMod.map_smul a.toAdditive.toAddMonoidHom c v)
  intro A hA m hmem hmove
  have hb := quiet_rankOne_starred_rank_and_codimension D hmany hmin hnon hJ n hn e A hA
  have hbudget := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  have he : NaturalTensor.operatorFixedCodim (ρ (q m)) =
      NaturalTensor.operatorFixedCodim (originalFullAction D m) := by
    apply NaturalTensor.operatorFixedCodim_eq_of_equiv _ _ E
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G)) (ChapterB.InternalThompsonAction.action_apply U m v)
  change rank A ≤ 2*n ∧ fixedCodim ρ A ≤ 4*n at hb
  change q m ∈ A at hmem
  have hl : 4*n ≤ NaturalTensor.operatorFixedCodim (ρ (q m)) := by
    by_contra! hlt
    apply hmove
    apply quiet_seed_stable_of_full_displacement_lt D hmany hJ m
    rw [quiet_rankOne_seed_finrank D hn hm,←he]
    exact hlt
  have hu := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A hmem
  change NaturalTensor.operatorFixedCodim (ρ (q m)) ≤ fixedCodim ρ A at hu
  have hr : rank A = 2*n := by omega
  have hc : fixedCodim ρ A = 4*n := by omega
  have ho : NaturalTensor.operatorFixedCodim (ρ (q m)) = 4*n := by omega
  refine ⟨hr,hc,ho,?_⟩
  change fixedSpace ρ A = LinearMap.ker (ρ (q m)-1)
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv
    exact sub_eq_zero.mpr (hv ⟨q m,hmem⟩)
  · have h₁ := fixedCodim_add_finrank ρ A
    have h₂ := NaturalTensor.operatorFixedCodim_add_finrank (ρ (q m))
    omega

/-- Every original starred actor preserves the same seed unless it saturates
both sharp bounds. The exceptional alternative names a genuine element of
the full preimage, its displacement and its literal full-module fixed space. -/
theorem quiet_rankOne_starred_stable_or_saturated
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ,
      rank A ≤ 2*n ∧ fixedCodim ρ A ≤ 4*n ∧
      ((∀ m : D.maximalLocal, q m ∈ A → (m : G) ∈ normalizer (D.seed : Set G)) ∨
        (rank A = 2*n ∧ fixedCodim ρ A = 4*n ∧
          ∃ m : D.maximalLocal, q m ∈ A ∧ (m : G) ∉ normalizer (D.seed : Set G) ∧
            NaturalTensor.operatorFixedCodim (ρ (q m)) = 4*n ∧
            fixedSpace ρ A = LinearMap.ker (ρ (q m)-1))) := by
  dsimp only
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  intro A hA
  obtain ⟨hr,hc⟩ := quiet_rankOne_starred_rank_and_codimension D hmany hmin hnon hJ n hn e A hA
  refine ⟨hr,hc,?_⟩
  by_cases hs : ∀ m : D.maximalLocal,
      ChapterB.InternalThompsonAction.actionMk (D.fullModule.subgroupOf D.maximalLocal) m ∈ A →
        (m : G) ∈ normalizer (D.seed : Set G)
  · exact Or.inl hs
  · push Not at hs
    obtain ⟨m,hmem,hmove⟩ := hs
    obtain ⟨hr,hc,ho,hfix⟩ := quiet_rankOne_moving_seed_saturation
      D hmany hmin hnon hJ n hn e hm A hA m hmem hmove
    exact Or.inr ⟨hr,hc,m,hmem,hmove,ho,hfix⟩

private theorem full_sylow_preimage_preserves_seed
    (hlocal : D.moduleSubgroup = D.seed) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := ChapterB.InternalThompsonAction.actionMk U
    ∀ m : D.maximalLocal, q m ∈ ((T : Subgroup G).subgroupOf D.maximalLocal).map q →
      (m : G) ∈ normalizer (D.seed : Set G) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := ChapterB.InternalThompsonAction.actionMk U
  intro m hm
  obtain ⟨s,hs,he⟩ := hm
  have hsN : (s : G) ∈ normalizer (D.seed : Set G) := by
    rw [←hlocal]
    exact D.sylow_normalizes_module hs
  have hk : s⁻¹*m ∈ centralizer (U : Set M) := by
    rw [←QuotientGroup.ker_mk' (centralizer (U : Set M))]
    change q (s⁻¹*m) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hSF : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have hkN : ((s⁻¹*m : M) : G) ∈ normalizer (D.seed : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro v hv
    exact congrArg (fun x : M => (x : G)) (hk ⟨v,hFM (hSF hv)⟩ (hSF hv))
  have hmn := (normalizer (D.seed : Set G)).mul_mem hsN hkN
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hmn

/-- Choose the actual starred actor inside the image of the original Sylow.
Local seed equality makes its entire full-action preimage preserve that seed;
no elementary lift across the full centralizer kernel is assumed. -/
theorem quiet_rankOne_exists_sylow_starred_actor
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hlocal : D.moduleSubgroup = D.seed) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∃ A ∈ ChapterD.QhatStar ρ,
      A ≤ ((T : Subgroup G).subgroupOf D.maximalLocal).map q ∧
      rank A ≤ 2*n ∧ fixedCodim ρ A ≤ 4*n ∧
      ∀ m : D.maximalLocal, q m ∈ A → (m : G) ∈ normalizer (D.seed : Set G) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  let S := (T.subtype hTM).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨B,hB⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr
    (source_full_module_cubic_bound_of_many D hmany)
  let : IsElementaryAbelian 2 B := hB.1.2.1.2
  obtain ⟨P,hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ChapterB.InternalThompsonAction.ActionQuotient U) P S
  let A := B.map (MulAut.conj g).toMonoidHom
  have hA : A ∈ ChapterD.QhatStar ρ := ChapterD.QhatStar.map_conj ρ hB g
  have hAS : A ≤ (S : Subgroup _) := (congrArg Sylow.toSubgroup hg) ▸ map_mono hBP
  obtain ⟨hr,hc⟩ := quiet_rankOne_starred_rank_and_codimension D hmany hmin hnon hJ n hn e A hA
  refine ⟨A,hA,hAS,hr,hc,?_⟩
  intro m hm
  exact full_sylow_preimage_preserves_seed D hlocal m (hAS hm)

/-- The original starred actor has no pointwise kernel on the seed, even
before seed stability is known. The exact seed and full-action kernels
identify the commutator with the original normal component square. -/
theorem quiet_rankOne_starred_seed_faithful
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (_hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ, ∀ m : D.maximalLocal, q m ∈ A →
      (m : G) ∈ centralizer (D.seed : Set G) → q m = 1 := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let X := (R.subgroupOf M).map q
  obtain ⟨_,_,_,_,_,_,_,_,_,hkernel,_⟩ := hm
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  intro A hA m hmem hc
  have hAC := quiet_full_actor_starred_faithful D hmany hmin hnon hJ hd A hA
  apply mem_bot.mp
  rw [←hAC]
  refine ⟨hmem,?_⟩
  rintro _ ⟨l,hl,rfl⟩
  let l' : R := ⟨l,hl⟩
  let r : R := ⟨(m:G)*(l:G)*(m:G)⁻¹*(l:G)⁻¹,
    R.mul_mem ((mem_normalizer_iff.mp m.property (l:G)).mp hl) (R.inv_mem hl)⟩
  let N := normalizer (D.seed : Set G)
  let τ := originalSeedNormalizerAction D
  let m' : N := ⟨m,Subgroup.centralizer_le_normalizer _ hc⟩
  let lN : N := ⟨l,D.orbit_normalizes_seed hl⟩
  have hmone : τ m' = 1 := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (m:G)*(v.toMul:G)*(m:G)⁻¹ = (v.toMul:G)
    rw [←hc v.toMul v.toMul.property,mul_assoc,mul_inv_cancel,mul_one]
  have hrseed : r ∈ (originalSeedAction D).ker := by
    change originalSeedAction D r = 1
    change τ (m'*lN*m'⁻¹*lN⁻¹) = 1
    have hmone' : τ.asGroupHom m' = 1 := Units.ext hmone
    have hh : τ.asGroupHom (m'*lN*m'⁻¹*lN⁻¹) = 1 := by
      simp only [map_mul,map_inv,hmone',one_mul,inv_one,mul_one,mul_inv_cancel]
    exact congrArg Units.val hh
  have hrcore : r ∈ pCore 2 R := hkernel ▸ hrseed
  have hrq : q (inclusion R.le_normalizer r) = 1 := by
    have hh := full_actor_restriction_kernel D hnon
    rw [←hh] at hrcore
    exact hrcore
  have he : q m*q l*(q m)⁻¹*(q l)⁻¹ = 1 := by
    rw [←map_inv,←map_inv,←map_mul,←map_mul,←map_mul]
    exact hrq
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm

/-- Restrict a seed-preserving starred actor through the full action quotient.
The resulting map into the full seed normalizer is injective. Its H.1.1
bounds therefore use the rank of the original full actor, without losing a
pointwise seed kernel. -/
theorem quiet_rankOne_starred_seed_normalizer
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ,
      ∀ hs : ∀ m : D.maximalLocal, q m ∈ A → (m : G) ∈ normalizer (D.seed : Set G),
      ∃ j : A →* linearNormalizer (originalSeedAction D), Function.Injective j ∧
        (∀ (m : D.maximalLocal) (ha : q m ∈ A),
          j ⟨q m,ha⟩ = originalSeedAmbientNormalizerHom D ⟨m,m.property,hs m ha⟩) ∧
        rank j.range = rank A ∧
        rank A+n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) j.range+1 ∧
        (n+1 < rank A →
          3*n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) j.range) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  intro A hA hs
  let P := A.comap q
  let κ : P →* A := q.restrict (fun _ hx => hx)
  have hκ : Function.Surjective κ := by
    intro a
    obtain ⟨m,hm⟩ := (QuotientGroup.mk'_surjective (centralizer (U : Set M))) a.val
    exact ⟨⟨m,(show q m ∈ A from hm.symm ▸ a.property)⟩,Subtype.ext hm⟩
  let f : P →* linearNormalizer (originalSeedAction D) :=
    (originalSeedAmbientNormalizerHom D).comp
      ((M.subtype.comp P.subtype).codRestrict
        (M ⊓ normalizer (D.seed : Set G))
        (fun m => ⟨m.val.property,hs m.val m.property⟩))
  have hfker (m : P) : f m = 1 ↔ (m.val : G) ∈ centralizer (D.seed : Set G) := by
    constructor
    · intro he v hv
      have hh := congrArg (fun a : linearNormalizer (originalSeedAction D) =>
        ((a.val.val (Additive.ofMul ⟨v,hv⟩)).toMul : G)) he
      change (m.val:G)*v*(m.val:G)⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hc
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      change (m.val:G)*(v.toMul:G)*(m.val:G)⁻¹ = (v.toMul:G)
      rw [←hc v.toMul v.toMul.property,mul_assoc,mul_inv_cancel,mul_one]
  have hker : κ.ker ≤ f.ker := by
    intro m hmκ
    apply (hfker m).mpr
    have hmzero : q m.val = 1 := congrArg Subtype.val hmκ
    have hmcent : m.val ∈ centralizer (U : Set M) := by
      rwa [←QuotientGroup.ker_mk' (centralizer (U : Set M))]
    have hSF : D.seed ≤ D.fullModule :=
      (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
    have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
    intro v hv
    exact congrArg (fun z : M => (z : G)) (hmcent ⟨v,hFM (hSF hv)⟩ (hSF hv))
  let j := κ.liftOfSurjective hκ ⟨f,hker⟩
  have hjκ (m : P) : j (κ m) = f m := κ.liftOfRightInverse_comp_apply _ _ _ m
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply bot_unique
    intro a ha
    obtain ⟨m,rfl⟩ := hκ a
    have hmone : f m = 1 := (hjκ m).symm.trans ha
    have hh := quiet_rankOne_starred_seed_faithful D hmany hmin hnon hJ n hn e hm
      A hA m.val m.property ((hfker m).mp hmone)
    exact Subtype.ext hh
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective
    j.rangeRestrict j.rangeRestrict_surjective
  have hr : rank j.range = rank A :=
    congrArg (Nat.log 2) (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hne : j.range ≠ ⊥ := by
    intro he
    have hp := hA.1.2.1.rank_pos
    rw [he,BinaryOffender.rank_bot] at hr
    omega
  have hb := quiet_rankOne_seed_normalizer_rank_gap D hnon hn hm j.range ⟨hne,inferInstance⟩
  refine ⟨j,hj,?_,hr,?_,?_⟩
  · intro m ha
    exact hjκ ⟨m,ha⟩
  · simpa only [hr] using hb.2.1
  · simpa only [hr] using hb.2.2

private theorem twice_displacement_le_dimension
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) H W) (a : H) (ha : a^2=1) :
    2 * NaturalTensor.operatorFixedCodim (τ a) ≤ Module.finrank (ZMod 2) W := by
  have hle : LinearMap.range (τ a-1) ≤ LinearMap.ker (τ a-1) := by
    rintro _ ⟨v,rfl⟩
    have hh : τ a (τ a v) = v := by
      rw [←Module.End.mul_apply,←map_mul,←pow_two,ha,map_one,Module.End.one_apply]
    change τ a (τ a v-v)-(τ a v-v)=0
    apply sub_eq_zero.mpr
    rw [map_sub,hh]
    simp only [sub_eq_add_neg,ZModModule.neg_eq_self,add_comm]
  have hh := Submodule.finrank_mono hle
  have hd := NaturalTensor.operatorFixedCodim_add_finrank (τ a)
  change NaturalTensor.operatorFixedCodim (τ a) ≤ _ at hh
  omega

/-- For a seed-preserving starred actor, even the maximal-rank boundary has
strict individual displacement. H.1.1 gives at least3n moved dimensions on
the seed for the whole actor, whereas an involution moves at most2n. -/
theorem quiet_rankOne_preserving_starred_individual_displacement
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ,
      (∀ m : D.maximalLocal, q m ∈ A → (m : G) ∈ normalizer (D.seed : Set G)) →
      ∀ m : D.maximalLocal, q m ∈ A → NaturalTensor.operatorFixedCodim (ρ (q m)) < 4*n := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  intro A hA hs m hmem
  obtain ⟨j,hj,hjval,hr,hgap,hlarge⟩ := quiet_rankOne_starred_seed_normalizer
    D hmany hmin hnon hJ n hn e hm A hA hs
  have hbounds := quiet_rankOne_starred_rank_and_codimension D hmany hmin hnon hJ n hn e A hA
  change rank A ≤ 2*n ∧ fixedCodim ρ A ≤ 4*n at hbounds
  change q m ∈ A at hmem
  let a : A := ⟨q m,hmem⟩
  let μ := normalizerRepresentation (originalSeedAction D)
  have hSF : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let E : D.seed →* U := {
    toFun v := ⟨⟨v,hFM (hSF v.property)⟩,hSF v.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f : Additive D.seed →ₗ[ZMod 2] Additive U := E.toAdditive.toZModLinearMap 2
  have hf : Function.Injective f := by
    intro v w hvw
    exact Additive.toMul.injective (Subtype.ext
      (congrArg (fun z : Additive U => ((z.toMul : M) : G)) hvw))
  have hcompat (b : A) (v : Additive D.seed) : f (μ (j b) v) = ρ b.val (f v) := by
    obtain ⟨k,hk⟩ := (QuotientGroup.mk'_surjective (centralizer (U : Set M))) b.val
    have hkmem : q k ∈ A := hk.symm ▸ b.property
    have hb : (⟨q k,hkmem⟩ : A) = b := Subtype.ext hk
    rw [←hb,hjval]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun z : M => (z : G))
      (ChapterB.InternalThompsonAction.action_apply U k (f v))).symm
  by_contra! hbad
  have hbudget := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  have hop := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A hmem
  change NaturalTensor.operatorFixedCodim (ρ (q m)) ≤ fixedCodim ρ A at hop
  change 4*n ≤ NaturalTensor.operatorFixedCodim (ρ (q m)) at hbad
  have hrA : rank A = 2*n := by omega
  have hc : fixedCodim ρ A = NaturalTensor.operatorFixedCodim (ρ (q m)) := by omega
  have hfixed : fixedSpace ρ A = LinearMap.ker (ρ (q m)-1) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · intro v hv
      exact sub_eq_zero.mpr (hv a)
    · have h₁ := fixedCodim_add_finrank ρ A
      have h₂ := NaturalTensor.operatorFixedCodim_add_finrank (ρ (q m))
      omega
  have hseed : fixedSpace μ j.range = LinearMap.ker (μ (j a)-1) := by
    apply le_antisymm
    · intro v hv
      exact sub_eq_zero.mpr (hv ⟨j a,⟨a,rfl⟩⟩)
    · intro v hv
      have hav : μ (j a) v = v := sub_eq_zero.mp hv
      have hfull : f v ∈ fixedSpace ρ A := by
        rw [hfixed]
        exact sub_eq_zero.mpr ((hcompat a v).symm.trans (congrArg f hav))
      rintro ⟨_,b,rfl⟩
      apply hf
      exact (hcompat b v).trans (hfull b)
  have hcodim : fixedCodim μ j.range = NaturalTensor.operatorFixedCodim (μ (j a)) := by
    have h₁ := fixedCodim_add_finrank μ j.range
    have h₂ := NaturalTensor.operatorFixedCodim_add_finrank (μ (j a))
    rw [hseed] at h₁
    omega
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have haA : a^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  have ha : (j a)^2=1 := by rw [←map_pow,haA,map_one]
  have hhalf := twice_displacement_le_dimension μ (j a) ha
  rw [quiet_rankOne_seed_finrank D hn hm] at hhalf
  have hl := hlarge (by omega)
  change 3*n ≤ fixedCodim μ j.range at hl
  omega

/-- The strict individual bound holds for every starred actor. Sylow
conjugacy is performed in the original full action image, and the entire
preimage preserves the original seed. -/
theorem quiet_rankOne_starred_preserves_seed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht)
    (hlocal : D.moduleSubgroup = D.seed) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ, ∀ m : D.maximalLocal, q m ∈ A →
      NaturalTensor.operatorFixedCodim (ρ (q m)) < 4*n ∧
        (m : G) ∈ normalizer (D.seed : Set G) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  let S := (T.subtype hTM).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  intro A hA m hmem
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ChapterB.InternalThompsonAction.ActionQuotient U) P S
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : B ∈ ChapterD.QhatStar ρ := ChapterD.QhatStar.map_conj ρ hA g
  have hBS : B ≤ (S : Subgroup _) := (congrArg Sylow.toSubgroup hg) ▸ map_mono hAP
  have hs : ∀ k : M, q k ∈ B → (k : G) ∈ normalizer (D.seed : Set G) := by
    intro k hk
    exact full_sylow_preimage_preserves_seed D hlocal k (hBS hk)
  obtain ⟨k,hk⟩ := (QuotientGroup.mk'_surjective (centralizer (U : Set M)))
    (g*q m*g⁻¹)
  have hkB : q k ∈ B := hk.symm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hmem
  have hb := quiet_rankOne_preserving_starred_individual_displacement
    D hmany hmin hnon hJ n hn e hm B hB hs k hkB
  change NaturalTensor.operatorFixedCodim (ρ (q k)) < 4*n at hb
  have he : NaturalTensor.operatorFixedCodim (ρ (q k)) =
      NaturalTensor.operatorFixedCodim (ρ (q m)) := by
    rw [show q k = g*q m*g⁻¹ from hk]
    change Module.finrank (ZMod 2) (ρ (g*q m*g⁻¹)-LinearMap.id).range =
      Module.finrank (ZMod 2) (ρ (q m)-LinearMap.id).range
    rw [←fixedCodim_zpowers_eq_displacement_rank,←fixedCodim_zpowers_eq_displacement_rank]
    exact fixedCodim_zpowers_conj ρ (q m) g
  have hb' : NaturalTensor.operatorFixedCodim (ρ (q m)) < 4*n := he ▸ hb
  refine ⟨hb',?_⟩
  have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let a : U ≃* D.fullModule := subgroupOfEquivOfLe hFM
  let E : Additive U ≃ₗ[ZMod 2] Additive D.fullModule :=
    a.toAdditive.toLinearEquiv (fun c v => ZMod.map_smul a.toAdditive.toAddMonoidHom c v)
  have hcompat : NaturalTensor.operatorFixedCodim (ρ (q m)) =
      NaturalTensor.operatorFixedCodim (originalFullAction D m) := by
    apply NaturalTensor.operatorFixedCodim_eq_of_equiv _ _ E
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G)) (ChapterB.InternalThompsonAction.action_apply U m v)
  apply quiet_seed_stable_of_full_displacement_lt D hmany hJ m
  rw [quiet_rankOne_seed_finrank D hn hm,←hcompat]
  exact hb'

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
