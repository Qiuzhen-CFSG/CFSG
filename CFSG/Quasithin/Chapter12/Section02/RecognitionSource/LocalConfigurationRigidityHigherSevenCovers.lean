module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSevenCatalogue
public import Theory.SpecificGroups.AlternatingSeven.CentralCoverFixer

/-!
# Discharging the marked A₇ maximal-component rows

The actual A₇ projection of a proper containing component is surjective.
Local-component minimality lifts equality through its central and two-core
kernels, identifying that component with its maximal overcomponent. Its
literal image in N_G(R)/R is then quasisimple and carries the descended
perfect central cover of A₇, with a representative equation and the original
order-168 residual image retained.

The A₇ pointwise-fixer calculation lifts across this central cover. Hence V
centralizes the containing image, and the original displacement map makes
U∩V invariant. The full natural action would give a surjection from A₇ onto
GL₃(2) or GL₄(2), which is impossible. This closes both marked A₇ rows,
including their possible odd central kernels, and connects the result to
the existing rigidity and actual parabolic-complement consumer.

The source dispatcher retains only the nonquasisimple maximal two-core
quotient. HigherNoncentral discharges that case; RigidityComplete assembles
the full original 12.2.25–26 conclusions on the original source inputs.
Source: Aschbacher–Smith, original 12.2.2(3), A.3.12 and 12.2.25,
printed pp.795,47–48,805.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The chosen-module action centralizes the containing A₇ image pointwise. -/
theorem chosen_centralizes_seven_central_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)))
    (hcard : Nat.card (((ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)).subgroupOf
      (ThreeRigidity.image T U K)).map f.toMonoidHom) = 168)
    (v : V) :
    quotient (sectionRadical T U) ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩ ∈
      centralizer (ThreeRigidity.image T U K : Set (NormalizerQuotient (sectionRadical T U))) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let Kb := ThreeRigidity.image T U K
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let vN : N := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  let : (K.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  let : Kb.Normal := Subgroup.Normal.map inferInstance (quotient R) (QuotientGroup.mk'_surjective _)
  let := residual_image_quasisimple h D structural A C B hd
  let YK := Yb.subgroupOf Kb
  let : IsQuasisimple YK := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show Yb ≤ Kb from map_mono (comap_mono hYK))).symm
  change Nat.card (YK.map f.toMonoidHom) = 168 at hcard
  let : Group.IsPerfect (YK.map f.toMonoidHom) := Group.IsPerfect.map _
  let : Nontrivial (YK.map f.toMonoidHom) := by
    apply (nontrivial_iff_ne_bot _).mpr
    intro he
    have hh : Nat.card (YK.map f.toMonoidHom) = 1 := by rw [he]; simp
    omega
  apply AlternatingSeven.SevenFixer.central_cover_centralizes_of_centralizes_subgroup Kb Yb
    (map_mono (comap_mono hYK)) f (Group.IsPerfect.not_isSolvable _)
    (by rw [hcard]; decide)
    (quotient R vN) (by exact (normalizer_eq_top Kb).symm ▸ mem_top _)
  rintro yb ⟨y,hy,rfl⟩
  have hc := chosen_residual_actions_commute D A C B v ⟨y,hy⟩
  apply (action_injective R (sectionRadical_selfCentralizing h A C B))
  rw [map_mul,map_mul]
  change R.normalizerMonoidHom y * R.normalizerMonoidHom vN =
    R.normalizerMonoidHom vN * R.normalizerMonoidHom y
  exact hc.eq.symm

/-- The original displacement space is invariant under the containing image,
using the actual commutator map, not its dimension or an abstract module tag. -/
theorem containing_normalizes_hyperplane_of_seven_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)))
    (hcard : Nat.card (((ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)).subgroupOf
      (ThreeRigidity.image T U K)).map f.toMonoidHom) = 168) :
    K ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  let R := sectionRadical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let := D.elementary
  obtain ⟨v,δ,hv,hδ,hδval,_,_⟩ := exists_radical_displacement D A C B
    (((structural G T L h).2.2 V D).1)
  let vN : normalizer (R : Set G) := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  have hvc := chosen_centralizes_seven_central_cover h D structural A C B hd hYK hn f hcard v
  apply le_normalizer_iff.mpr
  intro k hk w hw
  obtain ⟨r,hr⟩ := hδ ⟨w,hw⟩
  let kN : normalizer (R : Set G) := ⟨k,hKN hk⟩
  have hc : Commute (R.normalizerMonoidHom vN) (R.normalizerMonoidHom kN) := by
    have hh := congrArg (action R (by exact (sectionRadical_selfCentralizing h A C B).symm.le))
      (hvc (quotient R kN) (mem_map_of_mem (quotient R) hk))
    rw [map_mul,map_mul] at hh
    change R.normalizerMonoidHom kN * R.normalizerMonoidHom vN =
      R.normalizerMonoidHom vN * R.normalizerMonoidHom kN at hh
    exact hh.symm
  have he := congrArg (fun r : R => (r : G)) (ConjugationDisplacement.equivariant R vN kN hc r)
  have he' : (δ (R.normalizerMonoidHom kN r) : G) = k * w * k⁻¹ := by
    rw [hδval]
    rw [← ConjugationDisplacement.hom_apply R vN (R.normalizerMonoidHom kN r)]
    rw [he]
    change k * (ConjugationDisplacement.hom R vN r : G) * k⁻¹ = _
    rw [ConjugationDisplacement.hom_apply,← hδval r,hr]
  exact he' ▸ (δ (R.normalizerMonoidHom kN r)).property

/-- Even a central cover of the marked A₇ quotient is incompatible with the
literal hyperplane displacement action. -/
theorem no_seven_central_cover_containing_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)))
    (hcard : Nat.card (((ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)).subgroupOf
      (ThreeRigidity.image T U K)).map f.toMonoidHom) = 168) : False := by
  let R := sectionRadical T U
  let W := U ⊓ V
  let Kb := ThreeRigidity.image T U K
  have hKW := containing_normalizes_hyperplane_of_seven_cover h D structural A C B hd hKN hYK hn f hcard
  let a : K →* MulAut W := W.normalizerMonoidHom.comp (inclusion hKW)
  have ha : Function.Surjective a := by
    intro b
    obtain ⟨y,hy⟩ := residualHyperplaneAction_surjective D A C hd b
    exact ⟨⟨y,hYK y.property⟩,hy⟩
  let q := containingImageMap hKN
  have hq := containingImageMap_surjective hKN
  have hka : q.ker ≤ a.ker := by
    intro k hk
    have hkR : (k : G) ∈ R :=
      (QuotientGroup.eq_one_iff (⟨k,hKN k.property⟩ : normalizer (R : Set G))).mp
        (congrArg Subtype.val hk)
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hkR.2 w w.property.1).symm
  let g : Kb →* MulAut W := q.liftOfSurjective hq ⟨a,hka⟩
  have hgq (k : K) : g (q k) = a k := by simp [g]
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨k,rfl⟩ := ha b
    exact ⟨q k,hgq k⟩
  let := (hyperplaneAut_simple_perfect C hd).1
  let := (hyperplaneAut_simple_perfect C hd).2
  have hz : center (MulAut W) = ⊥ := by
    rcases (inferInstance : (center (MulAut W)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  have hfg : f.toMonoidHom.ker ≤ g.ker := by
    intro x hx
    have hc : g x ∈ center (MulAut W) := mem_center_iff.mpr (fun y => by
      obtain ⟨y,rfl⟩ := hg y
      exact (map_mul g y x).symm.trans
        ((congrArg g (mem_center_iff.mp (f.ker_le_center hx) y)).trans (map_mul g x y)))
    change g x = 1
    exact mem_bot.mp (hz ▸ hc)
  let b : alternatingGroup (Fin 7) →* MulAut W :=
    f.toMonoidHom.liftOfSurjective f.surjective ⟨g,hfg⟩
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨x,rfl⟩ := hg y
    exact ⟨f.toMonoidHom x,by simp [b]⟩
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hAut : Nat.card (MulAut W) = if d = 4 then 168 else 20160 := hyperplaneAut_card D A C hd
  rcases (inferInstance : b.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff _).mp hk
    have he := Nat.card_congr (Equiv.ofBijective b ⟨hi,hb⟩)
    rw [nat_card_alternatingGroup,hAut] at he
    split at he <;> norm_num at he
  · have htriv : ∀ y : MulAut W, y = 1 := by
      intro y
      obtain ⟨x,rfl⟩ := hb y
      exact MonoidHom.mem_ker.mp (hk ▸ mem_top x)
    let : Unique (MulAut W) := ⟨⟨1⟩,htriv⟩
    have he : Nat.card (MulAut W) = 1 := Nat.card_unique
    rw [hAut] at he
    split at he <;> norm_num at he
private theorem seven_core_projection_central {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    letI := E.actionCentralizer_normal
    (e.toMonoidHom.comp E.coreToFaithful).ker ≤ center (K₀ ⧸ pCore 2 K₀) := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
  intro ht
  have hz : f = 1 := f.ker_eq_top_iff.mp ht
  obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 7))
  obtain ⟨y,rfl⟩ := hf x
  exact hx (DFunLike.congr_fun hz y)

/-- Surjectivity of the marked A₇ projection identifies the actual containing
component with its maximal overcomponent; equality is lifted through both cores. -/
theorem containing_eq_maximal_of_seven_projection
    {K K₀ W : Subgroup G}
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7))
    (hs : Function.Surjective ((chosenSevenProjection E e).comp (inclusion hKK₀))) : K = K₀ := by
  let := E.actionCentralizer_normal
  obtain ⟨S,hS,hKS⟩ := ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_in_local_overgroup
    T hlocal.1 hK₀.1 hKK₀
  have htop : (⊤ : Subgroup K₀) ∈ ChapterA.Section03.localCComponents S := by
    rw [hS]
    simpa only [subgroupOf_self] using
      ChapterA.Section03.SourceEmbeddings.local_restrict hK₀.1 (le_refl K₀)
  have hm : (K.subgroupOf K₀).map (chosenSevenProjection E e) = ⊤ := by
    have hh := MonoidHom.range_eq_top.mpr hs
    rwa [MonoidHom.range_comp,inclusion_range] at hh
  have he : K.subgroupOf K₀ = ⊤ :=
    ChapterA.Section03.SourceEmbeddings.local_eq_of_central_twoCore_map_eq S hKS htop le_top
      (e.toMonoidHom.comp E.coreToFaithful) (seven_core_projection_central E hq e) (by
        change (K.subgroupOf K₀).map (chosenSevenProjection E e) =
          (⊤ : Subgroup K₀).map (chosenSevenProjection E e)
        rw [hm,map_top_of_surjective _ (e.surjective.comp (QuotientGroup.mk'_surjective _))])
  exact le_antisymm hKK₀ (subgroupOf_eq_top.mp he)

/-- Transport the actual seven-point projection to KR/R, including its
representative equation and central kernel. -/
theorem exists_seven_image_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K W : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K W) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : letI := E.actionCentralizer_normal
      (K ⧸ (centralizer (W : Set G)).subgroupOf K) ≃* alternatingGroup (Fin 7)) :
    ∃ f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)),
      ∀ k : K, f.toMonoidHom (containingImageMap hKN k) = chosenSevenProjection E e k := by
  let := E.actionCentralizer_normal
  let := Chapter1.mem_L_isPerfect hlocal
  let F := chosenSevenProjection E e
  have hF : Function.Surjective F := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 7)) := Group.IsPerfect.ofSurjective hF
  let q := containingImageMap hKN
  have hqs := containingImageMap_surjective hKN
  let J := q.ker.map F
  let : J.Normal := (inferInstance : q.ker.Normal).map F hF
  have hJ : IsPGroup 2 J := (containingImageMap_ker_isPGroup hKN).map F
  have hJb : J = ⊥ := by
    apply (inferInstance : J.Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let : Group.IsNilpotent J := hJ.isNilpotent
    let a : J ≃* alternatingGroup (Fin 7) := (MulEquiv.subgroupCongr ht).trans topEquiv
    exact Group.IsPerfect.not_isSolvable _
      (Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective)
  have hk : q.ker ≤ F.ker := (map_eq_bot_iff q.ker).mp hJb
  let f : ThreeRigidity.image T U K →* alternatingGroup (Fin 7) :=
    q.liftOfSurjective hqs ⟨F,hk⟩
  have he (k : K) : f (q k) = F k := by simp [f]
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k,rfl⟩ := hF x
    exact ⟨q k,he k⟩
  let Kb := ThreeRigidity.image T U K
  let : Group.IsPerfect Kb := Group.IsPerfect.ofSurjective hqs
  let : IsQuasisimple (Kb ⧸ pCore 2 Kb) :=
    IsQuasisimple.of_mulEquiv (containingImageTwoCoreEquiv hKN)
  let : IsQuasisimple Kb :=
    (show PerfectCentralCovering.Cover Kb (Kb ⧸ pCore 2 Kb) from
      { toMonoidHom := QuotientGroup.mk' _, surjective := QuotientGroup.mk'_surjective _,
        isPerfect := inferInstance, ker_le_center := by
          rw [QuotientGroup.ker_mk']
          exact containing_image_twoCore_central h D structural A C B hd hK hYK }).isQuasisimple
  have hfc : f.ker ≤ center Kb := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    have hz : f = 1 := f.ker_eq_top_iff.mp ht
    obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 7))
    obtain ⟨k,rfl⟩ := hf x
    exact hx (DFunLike.congr_fun hz k)
  exact ⟨{ toMonoidHom := f, surjective := hf, isPerfect := inferInstance, ker_le_center := hfc },he⟩
omit [Finite G] in
/-- The subgroup image equation retains the same ambient quotient on every
subgroup of the containing component. -/
theorem containingImageMap_subgroup_map {J K : Subgroup G}
    (hKN : K ≤ normalizer (sectionRadical T U : Set G)) (hJK : J ≤ K) :
    (J.subgroupOf K).map (containingImageMap hKN) =
      (ThreeRigidity.image T U J).subgroupOf (ThreeRigidity.image T U K) := by
  ext b
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact mem_map_of_mem (quotient (sectionRadical T U))
      (show inclusion hKN k ∈ J.subgroupOf (normalizer (sectionRadical T U : Set G)) from hk)
  · rintro ⟨y,hy,hey⟩
    exact ⟨⟨y,hJK hy⟩,hy,Subtype.ext hey⟩

/-- Both marked A₇ rows of the actual maximal overcomponent are impossible.
The original projection descends to KR/R and the hyperplane displacement
exclusion applies with its order-168 embedded residual image. -/
theorem no_proper_containing_seven_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K K₀ W : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V < K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨_,hcard,hs⟩ := proper_containing_seven_projection h D structural A C hd hYK
    hlocal hKK₀ hK₀ E hq e
  have heq := containing_eq_maximal_of_seven_projection hlocal hKK₀ hK₀ E hq e hs
  subst K₀
  obtain ⟨f,hf⟩ := exists_seven_image_cover h D structural A C B hd hKN hK hYK.le hlocal E hq e
  apply no_seven_central_cover_containing_image h D structural A C B hd hKN hYK.le hn f
  rw [← containingImageMap_subgroup_map hKN hYK.le,map_map]
  have he : f.toMonoidHom.comp (containingImageMap hKN) = chosenSevenProjection E e :=
    MonoidHom.ext hf
  rw [he]
  exact hcard

/-- All quasisimple maximal-containing rows of original 12.2.2 now close
rigidity and the actual parabolic splitting. Only the nonquasisimple maximal
two-core quotient remains in the exhaustive source reduction. -/
theorem source_rigidity_or_nonquasisimple_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀) := by
  rcases source_rigidity_or_marked_seven_projection h D structural modules A C hnone hd with hc | hc
  · exact Or.inl hc
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,_,hrows⟩ := hc
    rcases hrows with hnot | ⟨hq,W,E,_,e,_,_,_⟩
    · exact Or.inr ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hnot⟩
    · exact (no_proper_containing_seven_projection h D structural A C
        (RigidityKernel.source_centralizers h D structural A C hnone) hd hKN hK hYK hn
        hlocal hKK₀ hK₀.1.1 E hq e).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
