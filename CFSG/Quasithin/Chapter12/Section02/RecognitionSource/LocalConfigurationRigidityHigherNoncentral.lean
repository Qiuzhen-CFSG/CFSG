module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSevenCovers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.NoncentralOddCore
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSmallImage

/-!
# Closing the nonquasisimple maximal-component branch

The genuine noncentral-Fitting theorem provides a prime-field SL₂ quotient
of the maximal two-core quotient. Restricting its actual solvable-kernel map
to the contained local component and applying perfect-subgroup recognition
gives a surjection onto SL₂(p) (including the possible SL₂(5) subgroup).

Project to PSL₂(p). The two-group kernel of K → KR/R maps trivially to this
simple group, so the original projection descends to KR/R. The proved
quasisimplicity of that actual image makes the new kernel central. Its
embedded residual has order divisible by seven; the prime-field local
subgroup theorem allows only A₅ as a proper image, so it must be full.
Perfection and local-component minimality lift equality back to Y=K.

Together with the binary and marked A₇ rows, this proves N_G(R)≤N_G(Y)
and supplies the existing higher rigidity and actual parabolic complement.
Only the authorized earlier Structural1222 and seven-module inputs remain.
Source: Aschbacher–Smith A.1.29, A.3.6, A.3.12 and original 12.2.25–26,
printed pp.27,43–48,805–806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Every solvable-kernel image of the original residual retains its seven part. -/
theorem seven_dvd_residual_image_of_solvable_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {Q : Type*} [Group Q]
    (f : rigidityHyperplaneResidual L U V →* Q) [Group.IsSolvable f.ker] :
    7 ∣ Nat.card f.range := by
  let Y := rigidityHyperplaneResidual L U V
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let := Chapter1.mem_L_isPerfect (residual_mem_local_family D A C hd
    (((structural G T L h).2.2 V D).1))
  let := (hyperplaneAut_simple_perfect C hd).1
  let : IsSimpleGroup (Y ⧸ pCore 2 Y) := (residualQuotientAutEquiv D A C hd).isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    apply pCore_isPGroup.to_le
    rw [← radical_eq_core_of_perfect_simple_core_quotient]
    exact le_solvableRadical _ inferInstance inferInstance
  let e := f.rangeRestrict.pCoreQuotientEquiv (p := 2) f.rangeRestrict_surjective (by
    show IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hk)
  have hc : Nat.card (f.range ⧸ pCore 2 f.range) = if d = 4 then 168 else 20160 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr (residualQuotientAutEquiv D A C hd).toEquiv]
    exact hyperplaneAut_card D A C hd
  have hdv : 7 ∣ Nat.card (f.range ⧸ pCore 2 f.range) := by
    rw [hc]
    split <;> decide
  exact hdv.trans (card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _))

/-- A prime-field PSL₂ central cover cannot properly enlarge this residual:
the only proper nonsolvable local image is A₅, which has no seven part. -/
theorem residual_eq_containing_of_prime_linear_central_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {Q : Type*} [Group Q] [Finite Q]
    (f : ThreeRigidity.image T U K →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (ThreeRigidity.image T U K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSL Q 2 p) :
    rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (R.subgroupOf N) :=
    ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let Kb := ThreeRigidity.image T U K
  have hKb : Kb.IsCComponent := hK.map_quotient (R.subgroupOf N)
  have hle : Yb ≤ Kb := map_mono (comap_mono hYK)
  obtain ⟨SK,_,hlocal⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    S (residual_image_local h D structural A C B hd) hle hKb.subnormal
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun x y =>
    Subtype.ext (mem_center_iff.mp (hk y.property) x.val))
  have hJ := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  have htop : (⊤ : Subgroup Kb).IsCComponent := by
    simpa only [subgroupOf_self] using hKb.subgroupOf le_rfl
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective f hf] using cComponent_map_of_solvable_ker htop f hf
  let j := f.comp (inclusion hle)
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hle).subgroupComap f.ker)
    (fun x y he => Subtype.ext ((inclusion_injective hle) (congrArg Subtype.val he)))
  let q := containingImageMap B.residual_normalizes
  let : Group.IsNilpotent q.ker := (containingImageMap_ker_isPGroup B.residual_normalizes).isNilpotent
  let : Group.IsSolvable (j.comp q).ker := isSolvable_comap_of_solvable_ker q j.ker
  have hseven : 7 ∣ Nat.card ((Yb.subgroupOf Kb).map f) := by
    have hh := seven_dvd_residual_image_of_solvable_kernel h D structural A C hd (j.comp q)
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (containingImageMap_surjective B.residual_normalizes),← MonoidHom.range_eq_map,
      MonoidHom.range_comp,inclusion_range] at hh
    exact hh
  have heq : (Yb.subgroupOf Kb).map f = ⊤ := by
    by_contra hne
    obtain ⟨_,⟨e⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
      (SK.mapSurjective hf) hJ hQ le_top hne hp ho (hmodel.of_mulEquiv topEquiv)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hseven
    norm_num at hseven
  let := hKb.perfect
  have ht : Yb.subgroupOf Kb = ⊤ := top_unique
    (perfect_le_of_map_le_of_central_kernel f hk (⊤ : Subgroup Kb) (Yb.subgroupOf Kb)
      (by rw [heq]; exact le_top))
  exact residual_eq_containing_of_image_eq h D structural A C B hd hKN hK hYK
    (le_antisymm hle (subgroupOf_eq_top.mp ht))
private theorem local_sqtk
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G)) :
    IsSQTK KnownSimple.IsKnownSimple K₀ := by
  let J := K₀ ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let N := normalizer (Q : Set G)
  have hJN : J ≤ N := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hKN : K₀ ≤ N := le_sup_left.trans hJN
  have hN : IsSQTK KnownSimple.IsKnownSimple N :=
    h.simpleQTKE.twoLocal_sqtk ⟨Q,hK₀.2.2,isPGroup_pCoreIn 2 J,rfl⟩
  have hsub := hN.subgroup (K₀.subgroupOf N)
  let e := (subgroupOfEquivOfLe hKN).symm
  exact ⟨hsub.stronglyQuasithin.of_injective e.toMonoidHom e.injective,
    hsub.isKGroup.of_injective e.toMonoidHom e.injective⟩

/-- In a nonquasisimple maximal row, every contained original local component
has an actual solvable-kernel projection onto a prime-field SL₂. -/
theorem nonquasisimple_containing_prime_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {K K₀ : Subgroup G}
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ∃ f : K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
        Function.Surjective f ∧ Group.IsSolvable f.ker := by
  let Q₀ := K₀ ⧸ pCore 2 K₀
  have h₀ := local_sqtk h hK₀
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q₀ := by
    refine ⟨?_,h₀.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h₀.stronglyQuasithin p hp ho)
  have htop₀ : (⊤ : Subgroup K₀).IsCComponent := by
    simpa only [subgroupOf_self] using hK₀.1.subgroupOf_of_le
      (le_refl K₀) (show K₀ ≤ K₀ ⊔ (T : Subgroup G) from le_sup_left)
  let : Group.IsNilpotent (pCore 2 K₀) := pCore_isNilpotent
  have htop : (⊤ : Subgroup Q₀).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop₀.map_quotient (pCore 2 K₀)
  have hnc : ¬ fittingSubgroup (⊤ : Subgroup Q₀) ≤ center (⊤ : Subgroup Q₀) := by
    intro hc
    have hr : solvableRadical (⊤ : Subgroup Q₀) = center (⊤ : Subgroup Q₀) :=
      le_antisymm (solvableRadical_le_center_of_fitting_le_center hc)
        (le_solvableRadical _ inferInstance (Group.isSolvable_of_comm
          (fun x y => Subtype.ext (mem_center_iff.mp y.property x))))
    let := htop.perfect
    let := htop.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple (⊤ : Subgroup Q₀) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨p,hp,hp3,⟨e⟩⟩ := ChapterA.Section03.NoncentralFitting.primeSL2FittingQuotient_of_noncentral
    ChapterA.RankActions.primeSL2CoverRigidity hQ (pCore_quotient_pCore_eq_bot 2) htop hnc
  let : Fact p.Prime := ⟨hp⟩
  let q := (QuotientGroup.mk' (pCore 2 K₀)).comp (inclusion hKK₀)
  let : Group.IsNilpotent q.ker := by
    change Group.IsNilpotent ((QuotientGroup.mk' (pCore 2 K₀)).ker.comap (inclusion hKK₀))
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.comap_of_injective (inclusion hKK₀) (inclusion_injective hKK₀)).isNilpotent
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup (⊤ : Subgroup Q₀)))
  let : Group.IsSolvable a.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    infer_instance
  let b := a.comp (topEquiv : (⊤ : Subgroup Q₀) ≃* Q₀).symm.toMonoidHom
  let : Group.IsSolvable b.ker := Group.isSolvable_of_isSolvable_injective
    (f := (topEquiv : (⊤ : Subgroup Q₀) ≃* Q₀).symm.toMonoidHom.subgroupComap a.ker)
    (fun x y hh => Subtype.ext (topEquiv.symm.injective (congrArg Subtype.val hh)))
  let F := b.comp q
  let : Group.IsSolvable F.ker := isSolvable_comap_of_solvable_ker q b.ker
  let := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect F.range := Group.IsPerfect.range F
  let : Nontrivial F.range := by
    apply (nontrivial_iff_ne_bot _).mpr
    intro he
    have hk : F.ker = ⊤ := F.ker_eq_top_iff.mpr (MonoidHom.range_eq_bot_iff.mp he)
    let : Group.IsSolvable (⊤ : Subgroup K) := hk ▸ (inferInstance : Group.IsSolvable F.ker)
    exact Chapter1.mem_L_not_isSolvable hlocal
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom)
        topEquiv.surjective)
  have finish {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
      (j : F.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
      ∃ r : ℕ, r.Prime ∧ 3 < r ∧
        ∃ f : K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r),
          Function.Surjective f ∧ Group.IsSolvable f.ker := by
    refine ⟨r,hr,hr3,j.toMonoidHom.comp F.rangeRestrict,j.surjective.comp F.rangeRestrict_surjective,?_⟩
    rw [MonoidHom.ker_comp_of_injective _ _ j.injective,MonoidHom.ker_rangeRestrict]
    infer_instance
  rcases ChapterA.RankActions.primePerfectSL2Recognition p hp3 F.range inferInstance inferInstance
    with hfull | hsmall
  · obtain ⟨j⟩ := hfull
    exact finish hp hp3 j
  · obtain ⟨j⟩ := hsmall.2
    exact finish (by decide : Nat.Prime 5) (by decide) j
/-- The original prime-field projection descends through the literal image
map, and quasisimplicity makes its remaining kernel central. -/
theorem residual_eq_containing_of_prime_linear_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (F : K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hF : Function.Surjective F) :
    rigidityHyperplaneResidual L U V = K := by
  let : Fact p.Prime := ⟨hp⟩
  let Q := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)
  let r := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let f₀ := r.comp F
  have hf₀ : Function.Surjective f₀ :=
    (GorensteinWalter.sl2ProjectiveProjection_surjective (ZMod p)).comp hF
  let : IsSimpleGroup Q := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  let : Group.IsPerfect Q := GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp3)
  let q := containingImageMap hKN
  have hqs := containingImageMap_surjective hKN
  let J := q.ker.map f₀
  let : J.Normal := (inferInstance : q.ker.Normal).map f₀ hf₀
  have hJ : IsPGroup 2 J := (containingImageMap_ker_isPGroup hKN).map f₀
  have hJb : J = ⊥ := by
    apply (inferInstance : J.Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    have hpQ : IsPGroup 2 Q := hJ.of_equiv ((MulEquiv.subgroupCongr ht).trans topEquiv)
    exact Group.IsPerfect.not_isNilpotent Q hpQ.isNilpotent
  have hk : q.ker ≤ f₀.ker := (map_eq_bot_iff q.ker).mp hJb
  let f : ThreeRigidity.image T U K →* Q := q.liftOfSurjective hqs ⟨f₀,hk⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k,rfl⟩ := hf₀ x
    exact ⟨q k,by simp [f]⟩
  let : IsQuasisimple (ThreeRigidity.image T U K) :=
    containing_image_quasisimple h D structural A C hnone hd hK hYK
  have hfc : f.ker ≤ center (ThreeRigidity.image T U K) := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    have hz : f = 1 := f.ker_eq_top_iff.mp ht
    obtain ⟨x,hx⟩ := exists_ne (1 : Q)
    obtain ⟨k,rfl⟩ := hf x
    exact hx (DFunLike.congr_fun hz k)
  exact residual_eq_containing_of_prime_linear_central_cover h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone) hd hKN hK hYK f hf hfc
    hp (hp.odd_of_ne_two (by omega))
    ⟨ZMod p,inferInstance,inferInstance,Nat.card_zmod p,⟨MulEquiv.refl _⟩⟩

/-- The last nonquasisimple maximal row also forces equality of the actual
residual and its containing component. -/
theorem residual_eq_of_nonquasisimple_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K K₀ : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) : rigidityHyperplaneResidual L U V = K := by
  obtain ⟨p,hp,hp3,F,hF,_⟩ := nonquasisimple_containing_prime_projection h hlocal hKK₀ hK₀ hn
  exact residual_eq_containing_of_prime_linear_projection h D structural A C hnone hd
    hKN hK hYK hp hp3 F hF

/-- Residual normality in the original ambient normalizer, with every
containing-component alternative discharged. -/
theorem source_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) := by
  rcases source_rigidity_or_nonquasisimple_maximal h D structural modules A C hnone hd with hc | hc
  · exact hc.1
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,_,hnot⟩ := hc
    have he := residual_eq_of_nonquasisimple_maximal h D structural A C hnone hd
      hKN hK hYK.le hlocal hKK₀ hK₀.1.1 hnot
    simpa only [he] using hn

/-- The higher-dimensional source rigidity and actual parabolic complement,
with no remaining normality or model-recognition premise. -/
theorem source_higher_rigidity_step
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U :=
  source_rigidity_step_of_residual_normal h D structural A C hnone hd
    (source_residual_normal h D structural modules A C hnone hd)
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
