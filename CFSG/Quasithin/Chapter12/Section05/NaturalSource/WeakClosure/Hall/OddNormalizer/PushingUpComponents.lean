module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.LocalModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Reduction
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Source
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrained

public import Theory.Representation.SL5ExteriorSquare.SixDimensionalExclusion
public import Theory.Representation.IrreducibleFixedPoints
public import Theory.SpecificGroups.Janko4.PerfectCoverActions

/-!
# The ordinary J₄ component in exterior pushing up

Failure of uniqueness for the original odd-actor residual gives the full
maximal pushing-up witness. If the preimage of F*(H/O₂(H)) stayed inside M,
the reciprocal argument would make the original L a component with index-two
normalizer. Its marked PSL₅(2) quotient has cubic rank two and trivial center,
forcing relative normality and contradicting that index.

For the resulting escaping component, the actual constrained action has
solvable kernel. The C.2.7 catalogue is excluded using the original residual's
PSL₅(2) quotient. In the matching PSL₅(2) row, equality of orders forces this
action onto the full simple quotient, which cannot normalize the nontrivial
two-subgroup supplied by the literal radical intersection.

The surviving ordinary component contains both the intersection residual
and the full source module. The original exterior module has no fixed points
and embeds into the component's central quotient with two-rank ten. The
residual retains cubic rank two and a factor of 31, so the proved local-model
exclusions leave J₄. Innerness gives the relative central-product factorization
while retaining the full central cover. The full module still has order at
least 1024, and the quotient marking comes from the original inclusion.

OddNormalizer applies this to its literal Hall counterexample. The final
p.612 cubic-centralizer contradiction and the separate p.623 odd-local
identification/generation argument remain to be proved.
Source: Aschbacher--Smith, 4.2.5--13, printed pp.609--612; C.2.7--8,
C.3.2--4 and C.4.4--8, printed pp.145--154; 4.4.6, printed p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem normal_of_binaryFive_core_quotient
    {B : Subgroup G} (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hB : B.IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* Representation.SL5TenDimensional.Group) : B.Normal := by
  let Q := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Q := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Q := Atlas.sl_perfect 5 (by decide)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    rcases (inferInstance : (center (B ⧸ pCore 2 B)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsPerfect (B ⧸ pCore 2 B) :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (B ⧸ pCore 2 B) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hr : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
    rw [primeRank_congr 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  exact hB.normal_of_coprime_core_center_primeRank (by decide : Odd 3)
    (by rw [hz]; simp) hr (hG.stronglyQuasithin 3 (by decide) (by decide))

/-- The original residual forces the generalized-Fitting preimage to escape M. -/
theorem exterior_pushingUp_escape (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M) :
    EscapeCase L V A := by
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_case_of_not_unique h.toHypothesis1221 D
    (exterior_component_sylow_unique s h) A hAM
    (s.marking.centralizing_actor_commutator hAM hAV) ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hF,hcomp,hnorm,hi,hrest⟩ := hr hf
  have hLH : L ≤ H := hF ▸
    ((map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_right)
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let q := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans s.marking.quotientEquiv
  let : (L.subgroupOf H).Normal := normal_of_binaryFive_core_quotient
    hw.2.2.2.2.2.2.1.sqtk hcomp q
  rw [normalizer_eq_top] at hnorm
  rw [←hnorm,index_top] at hi
  norm_num at hi


private abbrev Five := Representation.SL5TenDimensional.Group
private instance five_simple : IsSimpleGroup Five := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  exact Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
private instance five_perfect : Group.IsPerfect Five := Atlas.sl_perfect 5 (by decide)

private theorem five_card : Nat.card Five = 9999360 := by
  rw [Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  calc
    _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
      simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hc
    _ = 9999360 := by decide

private theorem five_center : center Five = ⊥ := by
  rcases (inferInstance : (center Five).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative Five (center_eq_top_iff.mp ht)).elim

private theorem five_two_exponent :
    ¬ ∀ P : Subgroup Five, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  let b : SL(3,ZMod 2) := ⟨!![1,1,0;0,1,1;0,0,1], by decide⟩
  have hb : b ^ 4 = 1 := by decide
  have hb2 : b ^ 2 ≠ 1 := by decide
  let f := Representation.SL5TenDimensional.projectiveEquiv.symm.toMonoidHom.comp
    ((Matrix.SpecialLinearGroup.LinearFundamental.projectiveReindex
      (F := ZMod 2) (finSumFinEquiv (m := 3) (n := 2))).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.LinearFundamental.projectLeft
        (m := Fin 3) (n := Fin 2) (F := ZMod 2)))
  have hi : Function.Injective f :=
    Representation.SL5TenDimensional.projectiveEquiv.symm.injective.comp
      ((Matrix.SpecialLinearGroup.LinearFundamental.projectiveReindex
        (F := ZMod 2) (finSumFinEquiv (m := 3) (n := 2))).injective.comp
          Matrix.SpecialLinearGroup.LinearFundamental.projectLeft_injective)
  have hp : IsPGroup 2 (zpowers b) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hb
  intro he
  have hh := congrArg Subtype.val (he ((zpowers b).map f) (hp.map f)
    ⟨f b,mem_map_of_mem f (mem_zpowers b)⟩)
  apply hb2
  apply hi
  change f b ^ 2 = 1 at hh
  simpa only [map_pow,map_one] using hh

open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.Section04Constrained

omit [Finite G] in
private theorem intrinsic_intersection_ne_bot
    {H R : Subgroup G} (K : Subgroup H)
    (hn : coreCentralIntersectionImage (K.map H.subtype) R ≠ ⊥) :
    coreCentralIntersectionImage K (R.subgroupOf H) ≠ ⊥ := by
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let ec := coreCentralQuotientCongr eK
  have he : (coreCentralIntersectionImage K (R.subgroupOf H)).map ec.toMonoidHom =
      coreCentralIntersectionImage (K.map H.subtype) R := by
    ext x
    constructor
    · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨eK k,hk,(coreCentralQuotientCongr_apply eK k).symm⟩
    · rintro ⟨k,hk,rfl⟩
      refine ⟨coreCentralProjection K (eK.symm k),⟨eK.symm k,?_,rfl⟩,?_⟩
      · change ((eK.symm k : K) : H).val ∈ R
        have hh := congrArg (fun a : K.map H.subtype => (a : G)) (eK.apply_symm_apply k)
        change ((eK.symm k : K) : H).val = (k : G) at hh
        rwa [hh]
      · change coreCentralQuotientCongr eK (coreCentralProjection K (eK.symm k)) = _
        rw [coreCentralQuotientCongr_apply,eK.apply_symm_apply]
  intro hb
  apply hn
  rw [←he,hb,Subgroup.map_bot]

private theorem no_constrained_five_star
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (π : F →* Five) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Five) : False := by
  let hs := h.constrained_source_input K hK hq hout hfK
  let Kg := K.map H.subtype
  let : (Kg.subgroupOf (Kg ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Kg.le_normalizer hs.normalizes)
  have hlarge : 40320 < Nat.card (starImage Kg R Kg) := by
    rw [Nat.card_congr e.toEquiv,five_card]
    decide
  have hne := (ChapterC.C27Source.star_intersection_placement_from_source_of_large_order hs hlarge).1.1
  rw [←ChapterC.C27Source.component_intersection_star_eq_of_normal_input
    (ChapterC.C27Source.source_join_input hs)] at hne
  have hne' : coreCentralIntersectionImage Kg R ≠ ⊥ := by
    intro hb
    have hm := source_simple_equiv_map_intersection hs e five_center
    rw [hb,Subgroup.map_bot] at hm
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hm.symm)
  let I := coreCentralIntersectionImage K (R.subgroupOf H)
  have hIne : I ≠ ⊥ := intrinsic_intersection_ne_bot K hne'
  let ec := (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
    (source_simple_equiv hs e five_center)
  let : IsSimpleGroup (coreCentralQuotient K) := ec.isSimpleGroup
  have hcard : Nat.card (coreCentralQuotient K) = Nat.card Five := Nat.card_congr ec.toEquiv
  obtain ⟨r,hker,hr⟩ := constrained_normalized_inner_representation h hn K hK hq hout
  let := hker
  let : Group.IsSolvable r.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hd := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable Five) π hπ r.rangeRestrict
  have htop : r.range = ⊤ := r.range.eq_top_of_card_eq
    (le_antisymm (card_le_card_group _) (hcard ▸ Nat.le_of_dvd Nat.card_pos hd))
  have hnI : I.Normal := normalizer_eq_top_iff.mp (top_unique (htop ▸ hr))
  rcases hnI.eq_bot_or_eq_top with hb | ht
  · exact hIne hb
  · have hp : IsPGroup 2 I := coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup
    let : Group.IsNilpotent (coreCentralQuotient K) :=
      (hp.of_equiv ((MulEquiv.subgroupCongr ht).trans topEquiv)).isNilpotent
    exact Group.IsPerfect.not_isSolvable Five
      (Group.isSolvable_of_surjective (f := ec.toMonoidHom) ec.surjective)

/-- The marked PSL₅(2) residual excludes every constrained C.2.7 star row. -/
theorem exterior_no_constrained_pushingUp
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  let π := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hπ : Function.Surjective π := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hS : ¬ Group.IsSolvable Five := Group.IsPerfect.not_isSolvable Five
  have hsize : 20160 < Nat.card Five := by rw [five_card]; decide
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  cases hm with
  | linearTwo E e => exact h.no_constrained_component_star_linear_two K hK hq hout hfK E e
  | linearThree E e =>
    by_cases hE : 1 < E.degree
    · exact no_constrained_normalized_linear_three h hn hS five_two_exponent π hπ K hK hq hout hfK E hE e
    · have hdeg : E.degree = 1 := by have := E.degree_pos; omega
      apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
      rw [Nat.card_congr e.toEquiv]
      have hc := (center SL(3,E.Carrier)).index_mul_card
      rw [Atlas.ExceptionalSupport.card_sl_center] at hc
      change Nat.card PSL(3,E.Carrier) * Nat.gcd 3 (Nat.card E.Carrier - 1) = _ at hc
      rw [←hc,Matrix.PSL3.LinearThree.card_projective_mul_scalar,E.card_eq,hdeg]
      norm_num
  | symplectic E hE e =>
    apply no_constrained_normalized_symplectic h hn hS five_two_exponent π hπ K hK hq hout hfK e
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  | g2 E hE e =>
    apply no_constrained_normalized_g2 h hn hS five_two_exponent π hπ K hK hq hout hfK e
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  | g2DerivedTwo e =>
    apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    norm_num
  | alternating n hdegree e =>
    apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
    rw [Nat.card_congr e.toEquiv]
    rcases hdegree with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num
  | linearFiveTwo e => exact no_constrained_five_star h hn π hπ K hK hq hout hfK e
  | tripleSix ez eq =>
    apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
    let C := starImage (K.map H.subtype) R (K.map H.subtype)
    have hc := (center C).index_mul_card
    change Nat.card (C ⧸ center C) * Nat.card (center C) = Nat.card C at hc
    rw [Nat.card_congr eq.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hc
    norm_num at hc
    rw [←hc]
    norm_num

omit [Finite G] in
/-- No nonidentity vector of the original exterior module is fixed by L. -/
theorem ExteriorMarking.fixed_eq_bot (a : ExteriorMarking D) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  let := Representation.SL5ExteriorSquare.exteriorSquare_isIrreducible
  have hf := Representation.OneCohomology.fixed_eq_bot_of_irreducible_finrank
    (Representation.SL5TenDimensional.exteriorAction 2)
    (by rw [Representation.SL5TenDimensional.finrank_exteriorModule_two]; decide)
  apply bot_unique
  rintro v ⟨hv,hc⟩
  let w : V := ⟨v,hv⟩
  have hw : (a.coordinates w).toAdd ∈ Representation.OneCohomology.fixed
      (Representation.SL5TenDimensional.exteriorAction 2) := by
    intro g
    obtain ⟨l,hl⟩ := a.quotientEquiv.surjective g
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) l
    have he := a.equivariant x w
    have hconj : (⟨(x : G) * w * (x : G)⁻¹,
        (mem_normalizer_iff.mp (D.normalizes x.property) w).mp w.property⟩ : V) = w :=
      Subtype.ext (mul_inv_eq_of_eq_mul (hc x x.property))
    rw [hconj,hl] at he
    exact congrArg Multiplicative.toAdd he.symm
  rw [hf] at hw
  have hw1 : a.coordinates w = 1 := by
    exact congrArg Multiplicative.ofAdd (show (a.coordinates w).toAdd = 0 from hw)
  exact congrArg Subtype.val (a.coordinates.injective (hw1.trans (map_one a.coordinates).symm))

omit [Finite G] in
private theorem residual_module_quotient_injective
    (s : SylowExteriorMarking D)
    {F K : Subgroup G} (hVK : V ≤ K) (hFK : F ≤ K)
    (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G)) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp (inclusion hVK)) := by
  let f := (QuotientGroup.mk' (center K)).comp (inclusion hVK)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro x hx
  have hz : inclusion hVK x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hxc : (x : G) ∈ centralizer (F : Set G) := by
    intro y hy
    exact congrArg K.subtype (mem_center_iff.mp hz (inclusion hFK ⟨y,hy⟩))
  have hxl : (x : G) ∈ centralizer (L : Set G) := by
    intro y hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hcover ▸ (show y ∈ (L : Set G) from hy)
    calc
      (a * b) * (x : G) = a * (b * x) := mul_assoc _ _ _
      _ = a * (x * b) := congrArg (a * ·) ((hcore hb) x x.property).symm
      _ = x * (a * b) := by rw [←mul_assoc,hxc a ha,mul_assoc]
  apply Subtype.ext
  exact (show (x : G) ∈ (⊥ : Subgroup G) from s.marking.fixed_eq_bot ▸ ⟨x.property,hxl⟩)

private theorem central_kernel_le_twoCore
    {F K : Type*} [Group F] [Finite F] [Group K]
    (e : (F ⧸ pCore 2 F) ≃* Five)
    (j : F →* K) (hj : Function.Injective j) :
    ((QuotientGroup.mk' (center K)).comp j).ker ≤ pCore 2 F := by
  let π : F →* Five := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcx : x ∈ center F := mem_center_iff.mpr (fun y => hj (by
    simpa only [map_mul] using mem_center_iff.mp hc (j y)))
  have hcπ : π x ∈ center Five := mem_center_iff.mpr (by
    intro y
    obtain ⟨z,rfl⟩ := hs y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hcx z))
  have he : π x = 1 := by simpa only [five_center,mem_bot] using hcπ
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.injective (he.trans (map_one e).symm)

/-- The intersection residual retains its cubic rank and factor 31 in the
central quotient of the ordinary pushing-up component. -/
theorem exterior_pushingUp_placed_local
    (_s : SylowExteriorMarking D)
    {F K : Subgroup G} [Group.IsPerfect F]
    (hFK : F ≤ K) (hVF : V ≤ F) (hFL : F ≤ L)
    (hm : V = ⁅V,F⁆)
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) :
    ExteriorComponentLocalData (K ⧸ center K) := by
  let j := inclusion hFK
  let f := (QuotientGroup.mk' (center K)).comp j
  let W := V.subgroupOf F
  have hFW : F ≤ normalizer (V : Set G) := hFL.trans D.normalizes
  have hn : (⊤ : Subgroup F) ≤ normalizer (W : Set F) := by
    intro x _ y
    exact hFW x.property (y : G)
  let := D.elementary
  have hP : IsPGroup 2 (W.map f) := (IsElementaryAbelian.isPGroup 2 V).comap_subtype.map f
  have hne : W.map f ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff W).mp hb
    have hc : V ≤ centralizer (F : Set G) := by
      intro v hv y hy
      have hz : j (⟨v,hVF hv⟩ : F) ∈ center K :=
        (QuotientGroup.eq_one_iff _).mp (hk hv)
      have he : (⟨y,hy⟩ : F) * ⟨v,hVF hv⟩ = ⟨v,hVF hv⟩ * (⟨y,hy⟩ : F) :=
        (inclusion_injective hFK) (by
          simpa only [map_mul] using mem_center_iff.mp hz (j ⟨y,hy⟩))
      exact congrArg Subtype.val he
    exact D.ne_bot (hm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le
    (central_kernel_le_twoCore e j (inclusion_injective hFK))
  have hr : 2 ≤ primeRank 3 F := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 F) pCore_isPGroup,
      primeRank_equiv 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  have hr' : primeRank 3 f.range = primeRank 3 F := by
    rw [MonoidHom.range_eq_map f]
    exact (ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk
      (⊤ : Subgroup F)).trans (primeRank_equiv 3 Subgroup.topEquiv)
  have h31F : 31 ∣ Nat.card F := by
    have hd : 31 ∣ Nat.card (F ⧸ pCore 2 F) := by
      rw [Nat.card_congr e.toEquiv,five_card]
      decide
    exact hd.trans (card_quotient_dvd_card _)
  have h31 : 31 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card F := by
      rw [←index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    have hc : Nat.Coprime 31 (Nat.card f.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 31 2).pow_right n
    exact hc.dvd_of_dvd_mul_left (hcount.symm ▸ h31F)
  refine ⟨f.range,W.map f,Group.IsPerfect.range f,hr' ▸ hr,hP,hne,?_,map_le_range f W,h31⟩
  simpa only [←MonoidHom.range_eq_map] using
    (map_mono (f := f) hn).trans (W.le_normalizer_map f)

/-- Every ordinary component in the actual exterior pushing-up configuration
has the genuine J₄ central quotient, retaining its full covering group. -/
theorem exterior_pushingUp_ordinary_janko
    (s : SylowExteriorMarking D)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Kg := K.map H.subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVK : V ≤ Kg := hVF.trans hFK
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : IsQuasisimple K := hK.2
  let q : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := centerQuotientCongr q
  have hkg := hc.sqtk.subgroup K
  have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    hkg.stronglyQuasithin.quasithin hkg.isKGroup
  have hr : 10 ≤ primeRank 2 (K ⧸ center K) := by
    have hi := residual_module_quotient_injective s hVK hFK hcover
    let := D.elementary
    let : IsElementaryAbelian 2 (⊤ : Subgroup V) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup V).subtype (⊤ : Subgroup V).subtype_injective
    have hv : 10 ≤ primeRank 2 V :=
      IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup V)
        (by simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv]
          using (show Nat.card V = 2 ^ 10 from s.marking.card_module))
    have hh := hv.trans (Theory.GroupTheory.primeRank_le_of_injective 2 _ hi)
    rwa [primeRank_congr 2 z] at hh
  have hlocal := (exterior_pushingUp_placed_local s hFK hVF hFL hmove
    (e.trans s.marking.quotientEquiv)).of_mulEquiv z
  rcases hmodel.remaining_of_twoRank_ge_eight (by omega) with ho | hb | htwo | hs | hj
  · exact (ChapterA.Section02.no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact (hlocal.not_bender hb).elim
  · obtain ⟨n,hn⟩ := htwo
    exact (hlocal.not_rank_two n hn).elim
  · obtain ⟨E,_,_,hE,⟨f⟩⟩ := hs
    have hu : primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp E) ≤ 9 := by
      apply primeRank_le_of_prime_pow_not_dvd
      intro hd
      have hh := hd.trans (card_quotient_dvd_card
        (center (Theory.SpecificGroups.SymplecticSix.Sp E)))
      rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hE] at hh
      norm_num at hh
    rw [primeRank_equiv 2 f] at hr
    change 10 ≤ primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp E) at hr
    exact (by omega : False).elim
  · exact hj


/-- The p.612 branch now has an ordinary J₄ component. All C.2.8 data,
the original exterior module, its literal cover and the full module survive. -/
@[expose] def ExteriorPushingUpJankoCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G))

/-- Construct the ordinary J₄ pushing-up component from failure of residual
uniqueness; neither generalized-Fitting escape nor model exclusion is assumed. -/
theorem exterior_pushingUp_janko (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M) :
    ExteriorPushingUpJankoCase s A := by
  obtain ⟨J,H,W,hw,hf⟩ := exterior_pushingUp_escape s h A hAM ho hAV hnot
  have hw0 := hw
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,
    ⟨e,he⟩,hodd,hR,hSyl,hFit,hS,hsize,hmark⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hn : H ⊓ s.marking.M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hN
  have hf' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ s.marking.M).subgroupOf H :=
    fun hh => hf (hh.trans (comap_mono inf_le_right))
  obtain ⟨K,hK,hq,hout,hFK,hcases⟩ := hc.ordinary_or_constrained_escape hf'
  have hoK : IsComponent H K := by
    rcases hcases with hoK | hcon
    · exact hoK
    · exact (exterior_no_constrained_pushingUp hc hn (e.trans s.marking.quotientEquiv)
        K hK hq hout hcon).elim
  have hFK' := hc.ordinary_component_contains_original K hoK
  have hV : V ≤ K.map H.subtype := by
    apply hVF.trans
    have hh := map_mono (f := H.subtype) hFK'
    rwa [map_subgroupOf_eq_of_le (hc.component_le.trans hc.local_le)] at hh
  obtain ⟨ej⟩ := exterior_pushingUp_ordinary_janko s hw0 K hoK
  let := hoK.2
  let := hc.ordinary_component_normal K hoK
  let Kg := K.map H.subtype
  let k : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let : Group.IsPerfect Kg := Group.IsPerfect.ofSurjective
    (f := k.symm.toMonoidHom) k.symm.surjective
  have hsplit : H = Kg ⊔ (H ⊓ centralizer (Kg : Set G)) := by
    apply Janko4.perfect_cover_overgroup Kg H
      ((centerQuotientCongr k).trans ej) (map_subtype_le K)
    intro x hx
    exact K.le_normalizer_map H.subtype
      (mem_map_of_mem H.subtype (show (⟨x,hx⟩ : H) ∈ normalizer (K : Set H) by
        rw [normalizer_eq_top]; trivial))
  refine ⟨J,H,W,hw0,hf,?_,⟨e.trans s.marking.quotientEquiv⟩,K,hoK,
    hc.ordinary_component_normal K hoK,hout,hFK',
    (hc.ordinary_module_placement K hoK).1.trans inf_le_right,hV,
    ⟨ej⟩,hsplit⟩
  rwa [s.marking.card_module] at hsize

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
