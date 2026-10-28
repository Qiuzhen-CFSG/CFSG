module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietRankOneFull
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorInverseField
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietBinaryThreeGeneration

/-!
# The original quiet rank-one H-star Cartan

The constructed tensor marking gives the entire seed normalizer's displacement
and rank gap. B.2.4 therefore centralizes the actual higher Thompson subgroups.
The Fundamental Setup supplies E.6.1 for the unchanged local seed. E.6.3 and
E.6.26 then bound the generation parameter of every original H-star group,
without assuming a Hall subgroup or its faithfulness in order to get the bound.
The original source consumer constructs a central faithful Hall context and
its cyclic Cartan of exact order 2^n-1. A compatible Sylow exchanger acts on
this same Hall carrier by inverse field action, incompatible with ordinary
field action under every multiplicative marking. The original H-model must
still supply that ordinary action before the tensor exclusion is complete.
Source: Aschbacher--Smith 9.2.1--7, printed pp.730--732, using H.1.1 and B.2.4;
original 10.1.1, p.741, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE CentralHall.Nonlinear.Modules
open Representation.BinaryOffender.NaturalTensor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- Every nonidentity element of the full seed normalizer moves at least the field degree. -/
theorem quiet_rankOne_seed_normalizer_displacement_ge
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    ∀ a : linearNormalizer (originalSeedAction D), a ≠ 1 →
      n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
        (normalizerRepresentation (originalSeedAction D) a) := by
  obtain ⟨q,hq,_,_,_,σ,_,hf,hσ,_,α,⟨b⟩⟩ := hm
  let a := b.trans (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.binaryTensorEquiv α)
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext z
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨q g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hb : ∀ x : linearNormalizer σ, x ≠ 1 →
      n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
        (normalizerRepresentation σ x) := by
    intro x hx
    have hh := ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.normalizer_displacement_ge σ hf (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.marking α)
      a.toLinearEquiv (fun g v => LinearMap.congr_fun (a.isIntertwining' g) v) x hx
    rwa [Representation.BinaryOffender.NaturalTensor.finrank_field _
      (GaloisField.card 2 n (by omega))] at hh
  unfold normalizerRepresentation linearNormalizer at hb ⊢
  rwa [himage]

private def seedSylowHom (hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G)) :
    T →* linearNormalizer (originalSeedAction D) :=
  (originalSeedAmbientNormalizerHom D).comp ((T : Subgroup G).subtype.codRestrict
    (D.maximalLocal ⊓ normalizer (D.seed : Set G))
    (fun a => ⟨le_normalizer_componentOrbit L T a.property,hs a.property⟩))

private theorem seedSylowHom_ker
    (hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G))
    (hST : D.seed ≤ (T : Subgroup G)) :
    (seedSylowHom D hs).ker = centralizer (D.seed.subgroupOf T : Set T) := by
  ext a
  constructor
  · intro ha v hv
    have hh := congrArg (fun x : linearNormalizer (originalSeedAction D) =>
      x.val.val (Additive.ofMul (⟨v,hv⟩ : D.seed))) ha
    have he := congrArg (fun w : Additive D.seed => (w.toMul : G)) hh
    change (a:G)*(v:G)*(a:G)⁻¹ = (v:G) at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    have he := congrArg Subtype.val (ha ⟨v.toMul,hST v.toMul.property⟩ v.toMul.property)
    change (v.toMul:G)*(a:G) = (a:G)*(v.toMul:G) at he
    change (a:G)*(v.toMul:G)*(a:G)⁻¹ = (v.toMul:G)
    rw [←he,mul_inv_cancel_right]

private theorem seedSylowHom_thompson_bound
    (hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G))
    (hST : D.seed ≤ (T : Subgroup G))
    (j : ℕ) (A : Subgroup T) (hA : A ∈ ChapterB.thompsonFamily ⊤ j)
    (hne : A.map (seedSylowHom D hs) ≠ ⊥) :
    fixedCodim (normalizerRepresentation (originalSeedAction D))
        (A.map (seedSylowHom D hs)) ≤ rank (A.map (seedSylowHom D hs)) + j := by
  let U := D.seed.subgroupOf (T : Subgroup G)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hs
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hST
  let : IsElementaryAbelian 2 A := hA.2.1
  let e := subgroupOfEquivOfLe hST
  let E : Additive U ≃ₗ[ZMod 2] Additive D.seed :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let ρ := NoncentralChiefRefinement.normalRepresentation U
  have hE (a : T) (v : Additive U) : E (ρ a v) =
      normalizerRepresentation (originalSeedAction D) (seedSylowHom D hs a) (E v) := rfl
  have hb := ChapterB.lemma_B_2_4_1 (⊤ : Subgroup T) U A le_top le_top j
    (by rw [hA.2.2.2,Nat.log_pow (by decide : 1 < 2)]; rfl)
    (seedSylowHom D hs) (seedSylowHom_ker D hs hST) hne
  rw [←NoncentralChiefRefinement.normalRepresentation_fixedCodim_eq_rank_difference U A] at hb
  have he := fixedCodim_map_equivariant ρ (normalizerRepresentation (originalSeedAction D))
    (seedSylowHom D hs) E hE A
  change fixedCodim ρ A - j ≤ rank (A.map (seedSylowHom D hs)) at hb
  rw [he] at hb
  omega

/-- The higher Thompson subgroup centralizes the literal local tensor module.
No assertion about the full M-orbit is required. -/
theorem quiet_rankOne_local_thompson_centralizes
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht)
    (hlocal : D.moduleSubgroup = D.seed)
    (j : ℕ) (hj : j+1 < n) :
    ChapterB.thompsonJ (T : Subgroup G) j ≤ centralizer (D.moduleSubgroup : Set G) := by
  have heq := hlocal
  have hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G) := heq ▸ D.sylow_normalizes_module
  have hST : D.seed ≤ (T : Subgroup G) := heq ▸ D.module_le_sylow
  rw [heq]
  have htop : (⊤ : Subgroup T).map (T : Subgroup G).subtype = (T : Subgroup G) := by
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  rw [←htop,ChapterB.thompsonJ_map_injective _ (T : Subgroup G).subtype_injective]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1
  have hz : A.map (seedSylowHom D hs) = ⊥ := by
    by_contra hne
    let : IsElementaryAbelian 2 (A.map (seedSylowHom D hs)) := IsElementaryAbelian.map _
    have hl := (quiet_rankOne_seed_normalizer_rank_gap D hnon hn hm
      (A.map (seedSylowHom D hs)) ⟨hne,inferInstance⟩).2.1
    have hu := seedSylowHom_thompson_bound D hs hST j A hA hne
    omega
  intro a ha v hv
  have hak : a ∈ (seedSylowHom D hs).ker := (Subgroup.map_eq_bot_iff A).mp hz ha
  rw [seedSylowHom_ker D hs hST] at hak
  exact congrArg Subtype.val (hak ⟨v,hST hv⟩ hv)


section Bounds
variable (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht)
    (hlocal : D.moduleSubgroup = D.seed)

include hmany hJ hlocal in
/-- E.6.1 on the original seed as a TI subgroup normal in T. -/
theorem quiet_rankOne_seed_hypothesisE61 :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.seed := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  have heq := hlocal
  have hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G) := heq ▸ D.sylow_normalizes_module
  have hST : D.seed ≤ (T : Subgroup G) := heq ▸ D.module_le_sylow
  have hjoin : localJoin T L ≤ normalizer (D.seed : Set G) := heq ▸ D.join_normalizes_module
  have hc : D.seed ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
    apply bot_unique
    intro v hv
    have hvF : v ∈ D.fullModule :=
      ((le_componentOrbit D.seed T).trans (le_componentOrbit _ _)) hv.1
    have hmem : (⟨v,hvF⟩ : D.fullModule) ∈ D.fullCentralizer := hv.2
    have hfc : D.fullCentralizer = ⊥ := by
      apply bot_unique
      intro x hx
      apply mem_bot.mpr
      apply Subtype.ext
      exact mem_bot.mp ((source_fullModule_fixed_eq_bot_of_many D hmany hJ).le
        ⟨x.property,hx⟩)
    rw [hfc] at hmem
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hmem))
  refine ⟨D.simpleQTKE,hu.1,le_sup_right.trans hu.2.1,D.seed_ne_bot,inferInstance,hST,
    normal_subgroupOf_of_le_normalizer hs,?_,?_⟩
  · intro g hg
    exact D.seed_ti_under_maximalLocal (source_module_nonsolvable_uniqueness D) hc ⟨g,hg⟩
  · intro N hN hle
    apply hu.2.2 N hN
    apply le_trans _ hle
    refine le_inf (le_inf hu.2.1 hjoin) ?_
    change localJoin T L ≤ normalizer (((T : Subgroup G) ⊓ centralizer (D.seed : Set G) : Subgroup G) : Set G)
    rw [←heq,D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D)]
    exact (localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (localJoin T L) (pCore 2 (localJoin T L)))

include hmany hJ hn hm hlocal in
/-- The actual ambient seed automizer has minimum involution displacement at least n. -/
theorem quiet_rankOne_seed_localM_ge : n ≤ ChapterE.localM D.seed := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  have hnormal := (quiet_rankOne_seed_hypothesisE61 D hmany hJ hlocal).normalizer_le
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro k (rfl | ⟨a,ha,rfl⟩)
  · have hd := quiet_rankOne_seed_finrank D hn hm
    omega
  · obtain ⟨m,hma⟩ := D.seed.normalizerMonoidHom.rangeRestrict_surjective a
    have he : originalSeedNormalizerAction D m = automizerRepresentation D.seed a := by
      rw [←hma]
      rfl
    have hmove : originalSeedNormalizerAction D m ≠ 1 := by
      rw [he]
      intro hz
      have hane : a ≠ 1 := by intro he; simp [he] at ha
      apply hane
      apply automizerRepresentation_injective D.seed
      simpa only [map_one] using hz
    let b : linearNormalizer (originalSeedAction D) :=
      ⟨(originalSeedNormalizerAction D).asGroupHom m,
        original_seed_ambient_action_mem_normalizer D m (hnormal m.property) m.property⟩
    have hane : b ≠ 1 := by
      intro ha
      apply hmove
      exact congrArg (fun z : linearNormalizer (originalSeedAction D) => z.val.val) ha
    have hd := quiet_rankOne_seed_normalizer_displacement_ge D hn hm b hane
    change n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
      (originalSeedNormalizerAction D m) at hd
    rw [he] at hd
    exact hd.trans (operatorFixedCodim_le_fixedCodim (automizerRepresentation D.seed)
      (zpowers a) (mem_zpowers a))

include hmany hJ hn hm hlocal in
/-- E.6.3 supplies the ambient corank bound for the local tensor seed. -/
theorem quiet_rankOne_seed_globalR_ge :
    (n : ℕ∞) ≤ ChapterE.globalR D.seed := by
  have hm := quiet_rankOne_seed_localM_ge D hmany hJ hn hm hlocal
  have hh := ChapterE.Section06.FrobeniusReduction.lower_bound_knownSimple
    (quiet_rankOne_seed_hypothesisE61 D hmany hJ hlocal) (by omega)
  exact (ENat.natCast_le_natCast.mpr hm).trans hh.1

include hmany hJ hnon hn hm hlocal in
/-- Source 9.2.4(1) for every H-star in the original quiet tensor branch.
E.6.26 is applied to the TI local module, with all its premises discharged. -/
theorem quiet_rankOne_hstar_generation_ge
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) : n-1 ≤ generationParameter H := by
  by_contra! hgen
  have hjpos : 0 < n-2 := by omega
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hs : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le hTH
  have hr : ((n-2 : ℕ) : ℕ∞) < globalR D.seed :=
    (ENat.natCast_lt_natCast.mpr (by omega : n-2 < n)).trans_le
      (quiet_rankOne_seed_globalR_ge D hmany hJ hn hm hlocal)
  have hth := quiet_rankOne_local_thompson_centralizes D hnon hn hm hlocal (n-2) (by omega)
  rw [hlocal] at hth
  have hh := ChapterE.Section06.FixedPointBounds.SylowThompson.source_E_6_26_knownSimple
    (quiet_rankOne_seed_hypothesisE61 D hmany hJ hlocal) hjpos H (T.subtype hTH)
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (by omega : generationParameter H ≤ n-2)
    (by rw [hs]; exact inf_le_left) (by rw [hs]) hr (by rw [hs]; exact hth)
  exact hH.1.2 hh.1


end Bounds

/-- The faithful tensor marking moves both literal original component factors. -/
theorem quiet_rankOne_seed_not_separated
    {n : ℕ}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) := by
  let := D.quasisimple
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    IsQuasisimple.of_mulEquiv e
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (QuotientGroup.mk'_surjective (center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))).nontrivial
  obtain ⟨q,_,_,hl,hr,σ,_,hf,hσ,_,_,_⟩ := hm
  obtain ⟨a,ha⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
  obtain ⟨l,he⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) a
  change e (QuotientGroup.mk' (pCore 2 L) l) = a at he
  have hact (x : localOrbit T L) (v : Additive D.seed) :
      σ (q x) v = originalSeedAction D x v :=
    LinearMap.congr_fun (DFunLike.congr_fun hσ x) v
  rintro (hR | hL)
  · have hfix : σ (1,a) = 1 := by
      apply LinearMap.ext
      intro v
      have hh := hact (originalConjugateOrbitInclusion ht l) v
      rw [hr,he] at hh
      rw [hh]
      apply Additive.toMul.injective
      apply Subtype.ext
      have hc := hR v.toMul.property (t*(l:G)*t⁻¹) (mem_map_of_mem _ l.property)
      change (t*(l:G)*t⁻¹)*(v.toMul:G)*(t*(l:G)*t⁻¹)⁻¹ = (v.toMul:G)
      rw [hc,mul_inv_cancel_right]
    exact ha (congrArg Prod.snd (hf (hfix.trans σ.map_one.symm)))
  · have hfix : σ (a,1) = 1 := by
      apply LinearMap.ext
      intro v
      have hh := hact ⟨l,le_componentOrbit L T l.property⟩ v
      rw [hl,he] at hh
      rw [hh]
      apply Additive.toMul.injective
      apply Subtype.ext
      have hc := hL v.toMul.property l l.property
      change (l:G)*(v.toMul:G)*(l:G)⁻¹ = (v.toMul:G)
      rw [hc,mul_inv_cancel_right]
    exact ha (congrArg Prod.fst (hf (hfix.trans σ.map_one.symm)))

/-- The actual H-star supplies a central faithful Hall context: its large
parameter follows from the tensor, and no Hall premise is added. -/
theorem quiet_rankOne_hstar_context
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht)
    (hlocal : D.moduleSubgroup = D.seed)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ∃ B : Subgroup H, CentralHall.Context D H B := by
  have hlo := quiet_rankOne_hstar_generation_ge D hmany hJ hnon hn hm hlocal hH
  have hlarge : 1 < generationParameter H := by omega
  obtain ⟨_,_,_,_,d,he,hperm,_⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  have hBM := he ▸ d.hall_le
  have hHall := he ▸ d.hall
  have hfaith := source_nonnormalHallFaithful hmany L D hmin hnon hna H hH hlarge
    d.witness.abelianGroup hBM hHall d.witness.abelian hperm
  have hcentral : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G),H⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (quiet_hstar_centralizes_omega D hJ hH)
  exact ⟨d.witness.abelianGroup,
    ⟨hmany,hmin,hnon,hna,hH,hlarge,hcentral,hBM,hHall,d.witness.abelian,hperm,hfaith⟩⟩

/-- Every original H-star has a cyclic Hall subgroup of exact order 2^n-1
inside the original component orbit. The same field degree bounds its actual
generation parameter; no equality is transported through a solvable kernel. -/
theorem quiet_rankOne_hstar_cyclic_cartan
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (htn : t ∉ normalizer (L : Set G))
    (hm : QuietRankOneSeedMarking D e ht) (hlocal : D.moduleSubgroup = D.seed)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    n-1 ≤ generationParameter H ∧ generationParameter H ≤ n ∧
      ∃ B : Subgroup H, CentralHall.Context D H B ∧
        B.map H.subtype ≤ localOrbit T L ∧ IsCyclic B ∧
        Nat.card B = 2^n-1 ∧ Monoid.exponent B = 2^n-1 := by
  obtain ⟨B,c⟩ := quiet_rankOne_hstar_context D hmany hmin hnon hna hJ hn hm hlocal hH
  have hsep := quiet_rankOne_seed_not_separated D hm
  exact ⟨quiet_rankOne_hstar_generation_ge D hmany hJ hnon hn hm hlocal hH,
    (original_even_hall_cartan_degree D c n hn e ht htn hsep).2,
    B,c,original_even_hall_le_orbit D c n hn e ht htn hsep,
    original_even_hall_isCyclic D c n hn e ht htn hsep,
    original_even_hall_card D c n hn e ht htn hsep,
    original_even_hall_exponent_eq_sub_one D c n hn e ht htn hsep⟩

/-- Literal Cartan and exchanger data constructed in the quiet rank-one
branch. The Hall carrier, quotient marking, ambient conjugation and both
field-action conventions are retained. -/
@[expose] def QuietRankOneInverseFieldData (n : ℕ) (H : Subgroup G) : Prop :=
    ∃ B : Subgroup H, CentralHall.Context D H B ∧
      B.map H.subtype ≤ localOrbit T L ∧ IsCyclic B ∧ Nat.card B = 2^n-1 ∧
      ∃ (s : G) (hs : s ∈ (T : Subgroup G)), s ∉ normalizer (L : Set G) ∧
      ∃ (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L),
        B.map H.subtype ≤ C ∧
        IsHallSubgroup OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
        ∃ (_hsC : s ∈ normalizer (C : Set G)), s ∈ normalizer (B.map H.subtype : Set G) ∧
        ∃ _k : OriginalTensorCartanMarking D hs n C
          ((hC.trans (map_subtype_le _)).trans inf_le_left),
        ∃ (χ : B ≃* (GaloisField 2 n)ˣ) (β : MulAut B) (σ : GaloisField 2 n ≃+* GaloisField 2 n),
          β ≠ 1 ∧ (∃ a : ℕ, β^(2^a) = 1) ∧
          (∀ b : B, (β b:G) = s*(b:G)*s⁻¹) ∧
          (∀ b : B, χ (β b) = (Units.map σ.toMonoidHom (χ b))⁻¹) ∧
          C ⊓ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) =
            B.map H.subtype ∧
          (∀ b : B, Commute s (b:G) ↔ Units.map σ.toMonoidHom (χ b) * χ b = 1) ∧
          ∀ (ψ : B ≃* (GaloisField 2 n)ˣ) (τ : GaloisField 2 n ≃+* GaloisField 2 n),
            ¬ ∀ b : B, ψ (β b) = Units.map τ.toMonoidHom (ψ b)

/-- The quiet tensor forces an actual H-star Hall subgroup and a Sylow
exchanger acting by inverse field automorphism on it. This same conjugation
cannot be ordinary field action in any multiplicative marking of the Hall
carrier. The remaining ambient exclusion must construct that ordinary action
from the original H-model. -/
theorem quiet_rankOne_hstar_inverse_field
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (htn : t ∉ normalizer (L : Set G))
    (hm : QuietRankOneSeedMarking D e ht) (hlocal : D.moduleSubgroup = D.seed)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    QuietRankOneInverseFieldData D n H := by
  obtain ⟨_,_,B,c,hBR,hcyc,hcard,_⟩ :=
    quiet_rankOne_hstar_cyclic_cartan D hmany hmin hnon hna hJ hn htn hm hlocal hH
  have hsep := quiet_rankOne_seed_not_separated D hm
  obtain ⟨C,hC,hHall,hBC,_,_,d,hd,_⟩ :=
    original_even_hall_cartan_coordinates D c n hn e ht htn hsep
  let f := MulEquiv.ofBijective d hd
  let : IsMulCommutative C := ⟨⟨fun x y => f.injective (by simp [mul_comm])⟩⟩
  obtain ⟨s,hs,hsn,hsC⟩ :=
    CentralHall.Nonlinear.HallGeometry.original_cartan_exchanger D e hnon C hC hHall
  have hsB := CentralHall.Nonlinear.HallGeometry.original_hall_normalized_by_cartan_normalizer
    D c C hBC ⟨hs,hsC⟩
  have hst : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
    (source_nonnormal_maximal_pair D hnon ht htn s
      (le_normalizer_componentOrbit L T hs)).resolve_left
        (fun h => hsn (mem_normalizer_iff_map_conj_eq.mpr h))
  have hsepS : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj s).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) := by rwa [hst]
  have hodd : Odd (Nat.card C) := by
    have hh := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv] at hh
  obtain ⟨k⟩ := original_even_same_cartan_coordinates D c n hn e hs hsn hsepS C hC
    hodd (Nat.card_congr f.toEquiv)
  obtain ⟨χ,β,σ,hne,hpow,hno,hβ,hact,_,_,hcentral,hfixed,_⟩ :=
    original_even_same_cartan_exchanger_action D c n hn e hs hsn hsepS C _ hBC hsC hsB k
  exact ⟨B,c,hBR,hcyc,hcard,s,hs,hsn,C,hC,hBC,hHall,hsC,hsB,k,
    χ,β,σ,hne,hpow,hβ,hact,hcentral,hfixed,hno⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
