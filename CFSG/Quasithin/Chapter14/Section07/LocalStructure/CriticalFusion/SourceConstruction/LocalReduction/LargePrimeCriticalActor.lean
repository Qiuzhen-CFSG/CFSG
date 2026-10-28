module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCritical

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointCentralizer
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.LinearAction
public import Theory.SpecificGroups.GL2.OddCharacteristicTwoRank
public import Theory.Representation.CubicSixSpaceNilpotence

/-!
# The actual critical actor in the minimal five-core obstruction

F.9 places the endpoint module in an edge two-core. Local transitivity
conjugates that edge to the original L₁T, so the literal actor centralizes
the normal cubic L₁ image and acts faithfully on the normal five-core.

The latter has order five or twenty-five, bounding the elementary actor's
rank by two. The fixed-point-free cubic makes every displacement even;
the selected denominator bounds it by three. Thus each nonidentity actor
has displacement two and, by D.2.13, an order-five commutator with
four-dimensional support. A faithful four-group on a five-plane contains
inversion of the whole plane, contradicting that commutator order. The
actor therefore has order two. Its denominator has codimension one, and
the genuine reciprocal endpoint retains both rank-one equalities.

LargePrimeCriticalFactor applies this family to the same original minimal
local group, normal lift, action and canonical supports.
Source: Aschbacher–Smith, 14.7.5(4) and 14.7.6, printed pp.1044–1045;
F.9.13,16–17 and D.2.13, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.SolvableExclusion.Three
open Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem endpoint_edge_conjugate
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    ∃ x : D.H, (i.conjugate D.UH).map (MulAut.conj (x : G)).toMonoidHom ≤
      (D.LT ⊓ D.H).pCoreIn 2 := by
  open Subgroup.CosetGeometry.RankTwo in
  open Subgroup.CosetGeometry (stabilizer_base incident_base) in
  open ChapterF.Section09.Setup.Hypothesis in
  obtain ⟨w,_,hw,hcore⟩ := i.edge_core hb
  open Subgroup.CosetGeometry.RankTwo in
  open Subgroup.CosetGeometry (stabilizer_base incident_base) in
  open ChapterF.Section09.Setup.Hypothesis in
  obtain ⟨x,hx,hxw⟩ := locally_transitive (family (D := D)) hw
    (show (graph (family (D := D))).Adj (base (family (D := D)) true)
      (base (family (D := D)) false) from
      ⟨(by change true ≠ false; decide),incident_base _ _ _⟩)
  open Subgroup.CosetGeometry.RankTwo in
  open Subgroup.CosetGeometry (stabilizer_base incident_base) in
  open ChapterF.Section09.Setup.Hypothesis in
  have hxt : x ∈ family (D := D) true := by simpa only [stabilizer_base] using hx
  have hxH : (x : G) ∈ D.H := hxt
  refine ⟨⟨x,hxH⟩,?_⟩
  have hsmall : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hh := map_mono (f := (MulAut.conj (x : G)).toMonoidHom)
    ((map_mono hsmall).trans hcore)
  rw [←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj (x : G)).injective] at hh
  apply hh.trans_eq
  congr 1
  open Subgroup.CosetGeometry.RankTwo in
  open Subgroup.CosetGeometry (stabilizer_base incident_base) in
  open ChapterF.Section09.Setup.Hypothesis in
  have he : ((stabilizer (family (D := D)) (base (family (D := D)) true) ⊓
      stabilizer (family (D := D)) w).map (MulAut.conj x).toMonoidHom) =
      family (D := D) true ⊓ family (D := D) false := by
    rw [map_inf _ _ _ (MulAut.conj x).injective,←stabilizer_translate,
      ←stabilizer_translate,hxw,show x • base (family (D := D)) true =
        base (family (D := D)) true from hx]
    exact congrArg₂ (· ⊓ ·) (stabilizer_base _ true) (stabilizer_base _ false)
  open ChapterF.Section09.Setup.Hypothesis in
  have he' := congrArg (map (D.LT ⊔ D.H).subtype) he
  rw [ChapterF.Section09.Setup.Hypothesis.conjugate_map_ambient] at he'
  apply he'.trans
  change (D.H.subgroupOf (D.LT ⊔ D.H) ⊓ D.LT.subgroupOf (D.LT ⊔ D.H)).map
    (D.LT ⊔ D.H).subtype = D.LT ⊓ D.H
  rw [map_inf _ _ _ (D.LT ⊔ D.H).subtype_injective,
    map_subgroupOf_eq_of_le le_sup_right,map_subgroupOf_eq_of_le le_sup_left,inf_comm]


variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

local instance (I : Subgroup G) [hU : IsElementaryAbelian 2 (F.UH I)] :
    IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU

/-- The actual critical actor is conjugate into the original edge two-core. -/
theorem local_critical_endpoint_edge
    (I : Subgroup G)
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (i : hf.CriticalEndpoint) (hb : 3 ≤ hf.b) :
    ∃ x : I, (i.conjugate (F.UH I)).map (MulAut.conj (x : G)).toMonoidHom ≤
      F.Ri L 1 := by
  have hres : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).L₁ =
      F.Li L 1 := hf.g2_L₁.symm.trans (F.localKernel_L₁ L I)
  have hedge : (L ⊔ (T : Subgroup G)) ⊓ I = F.Li L 1 ⊔ (T : Subgroup G) := by
    have he := hf.LT_inf_H_eq
    change (L ⊔ (T : Subgroup G)) ⊓ I =
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).L₁ ⊔ (T : Subgroup G) at he
    rwa [hres] at he
  obtain ⟨x,hx⟩ := endpoint_edge_conjugate hf i hb
  refine ⟨x,?_⟩
  change (i.conjugate (F.UH I)).map _ ≤ ((L ⊔ (T : Subgroup G)) ⊓ I).pCoreIn 2 at hx
  rwa [hedge] at hx

/-- The selected endpoint centralizes the original cubic and acts faithfully
on the normal supplement, with the same quotient map throughout. -/
theorem local_critical_actor_control
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (i : hf.CriticalEndpoint) (hb : 3 ≤ hf.b)
    (X : Subgroup (HStar I)) [X.Normal]
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    actorImage I (i.conjugate (F.UH I)) ≤
      centralizer (((F.Li L 1).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) ∧
    actorImage I (i.conjugate (F.UH I)) ⊓ centralizer (X : Set (HStar I)) = ⊥ := by
  let := hn
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  let earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u} :=
    ⟨structural,uniqueness,previous⟩
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := ((F.Li L 1).subgroupOf I).map q
  let R := ((F.Ri L 1).subgroupOf I).map q
  let B := ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q
  let : P.Normal := Normal.map hn q (QuotientGroup.mk'_surjective _)
  have hRP : R ≤ centralizer (P : Set (HStar I)) :=
    Chapter12.Section09.NaturalSource.normal_local_edge_core_commuting_images h earlier F hI
  have hBR : B ≤ normalizer (R : Set (HStar I)) := by
    apply (map_mono ?_).trans (le_normalizer_map q)
    apply le_normalizer_iff.mpr
    intro b hb r hr
    exact le_normalizer_iff.mp (le_normalizer_pCoreIn 2 (F.Li L 1 ⊔ (T : Subgroup G)))
      b hb r hr
  have hRX : R ⊓ centralizer (X : Set (HStar I)) = ⊥ :=
    centralizer_inf_eq_bot_of_supplement X B R hgen
      ((isPGroup_pCoreIn 2 (F.Li L 1 ⊔ (T : Subgroup G))).comap_subtype.map q)
      hBR (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨x,hx⟩ := local_critical_endpoint_edge I hf i hb
  have hconj (v : I) (hv : v ∈ (i.conjugate (F.UH I)).subgroupOf I) :
      q x * q v * (q x)⁻¹ ∈ R := by
    refine mem_map.mpr ⟨x * v * x⁻¹, hx (mem_map_of_mem _ hv), ?_⟩
    rw [map_mul,map_mul,map_inv]
  constructor
  · rintro t ⟨v,hv,rfl⟩
    have hc := hRP (hconj v hv)
    have hh := (inferInstance : (centralizer (P : Set (HStar I))).Normal).conj_mem
      _ hc (q x)⁻¹
    simpa only [mul_assoc,inv_mul_cancel_left,inv_inv,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
  · apply bot_unique
    rintro t ⟨⟨v,hv,rfl⟩,hc⟩
    have ht := (inferInstance : (centralizer (X : Set (HStar I))).Normal).conj_mem
      _ hc (q x)
    have he : q x * q v * (q x)⁻¹ = 1 := hRX.le ⟨hconj v hv,ht⟩
    exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q x)).symm))

private theorem five_core_conjugation_injective
    {D : Type*} [Group D] (X A : Subgroup D) [X.Normal]
    (hfaith : A ⊓ centralizer (X : Set D) = ⊥) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut X).comp A.subtype) := by
  let φ : A →* MulAut X := (MulAut.conjNormal : D →* MulAut X).comp A.subtype
  apply (MonoidHom.ker_eq_bot_iff φ).mp
  apply φ.ker.eq_bot_iff_forall.mpr
  intro a ha
  apply Subtype.ext
  apply hfaith.le
  refine ⟨a.property,?_⟩
  intro x hx
  have hh := congrArg (fun f : MulAut X => (f ⟨x,hx⟩ : D)) ha
  change (a : D) * x * (a : D)⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem five_core_actor_rank_le_two
    {D : Type*} [Group D] [Finite D]
    (X A : Subgroup D) [X.Normal] [IsElementaryAbelian 5 X]
    (hc : Nat.card X = 5 ∨ Nat.card X = 25)
    (hA : IsElementaryTwo A) (hfaith : A ⊓ centralizer (X : Set D) = ⊥) :
    rank A ≤ 2 := by
  let := hA.2
  let φ : A →* MulAut X := (MulAut.conjNormal : D →* MulAut X).comp A.subtype
  have hi : Function.Injective φ := five_core_conjugation_injective X A hfaith
  have hcard : Nat.card A ≤ 4 := by
    rcases hc with hc | hc
    · let : IsCyclic X := isCyclic_of_prime_card hc
      have haut : Nat.card (MulAut X) = 4 := by rw [IsCyclic.card_mulAut,hc]; decide
      exact (Nat.card_le_card_of_injective φ hi).trans haut.le
    · have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 φ hi).trans
        (IsElementaryAbelian.automorphism_twoRank_le_two_of_odd_plane (p := 5)
          (by decide) hc)
      have hh := (primeRank_le_iff_elementary_card_le A).mp hr ⊤
        (IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype (⊤ : Subgroup A).subtype_injective)
      simpa only [card_top,show 2 ^ 2 = 4 from rfl] using hh
  change Nat.log 2 (Nat.card A) ≤ 2
  exact (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 4 ≤ 2)

private theorem even_displacement_of_cubic_centralizer
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (P : Subgroup D)
    (hP : Nat.card P = 3) (hfix : fixedSpace ρ P = ⊥)
    (t : D) (ht : t ∈ centralizer (P : Set D)) :
    Even (fixedCodim ρ (zpowers t)) := by
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  have htotal := even_ker_finrank_of_commuting_three_group ρ P hp hfix 0
    (fun _ => Commute.zero_right _)
  rw [LinearMap.ker_zero,finrank_top] at htotal
  have hker := even_ker_finrank_of_commuting_three_group ρ P hp hfix
    (ρ t - LinearMap.id) (fun z =>
      ((show Commute (z : D) t from (ht z z.property)).map ρ).sub_right (Commute.one_right _))
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have hdim := LinearMap.finrank_range_add_finrank_ker (ρ t - LinearMap.id)
  obtain ⟨n,hn⟩ := htotal
  obtain ⟨m,hm⟩ := hker
  refine ⟨n-m,?_⟩
  omega

/-- Each nonidentity element of the actual selected actor is a quintic
reflection on a four-space, with its precise fixed complement. -/
theorem local_five_critical_reflections
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (X : Subgroup (HStar I)) [X.Normal] [IsElementaryAbelian 5 X]
    (hX : Nat.card X = 5 ∨ Nat.card X = 25)
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    rank (actorImage I (c.endpoint.conjugate (F.UH I))) ≤ 2 ∧
    ∀ t ∈ actorImage I (c.endpoint.conjugate (F.UH I)), t ≠ 1 →
      orderOf t = 2 ∧ fixedCodim a.representation (zpowers t) = 2 ∧
      Nat.card (⁅X,zpowers t⁆ : Subgroup (HStar I)) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,zpowers t⁆) = 4 ∧
      IsCompl (subspaceCommutator a.representation ⊤ ⁅X,zpowers t⁆)
        (fixedSpace a.representation (⁅X,zpowers t⁆ ⊔ zpowers t)) := by
  let A := actorImage I (c.endpoint.conjugate (F.UH I))
  obtain ⟨hAP,hfaith⟩ := local_critical_actor_control h structural previous I hI hn hf
    c.endpoint hb X hgen
  have hA : IsElementaryTwo A := c.quadratic.1
  have hr : rank A ≤ 2 := five_core_actor_rank_le_two X A hX hA hfaith
  refine ⟨hr,?_⟩
  intro t ht ht1
  let := hA.2
  have ht2 : t ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨t,ht⟩ : A))
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdisp := c.displacement_rank_le hb ht
  have hcomp := c.comparison
  have heven := even_displacement_of_cubic_centralizer a.representation
    (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)))
    (local_point_star_card_of_normal h structural I (F.Li_one_le_of_mem_Hz hI) hn)
    (local_point_fixedSpace_eq_bot h structural I (F.Li_one_le_of_mem_Hz hI) hn a)
    t (hAP ht)
  have hd : fixedCodim a.representation (zpowers t) = 2 := by
    have hpos : fixedCodim a.representation (zpowers t) ≠ 0 := by
      intro hz
      rw [fixedCodim_zpowers_eq_displacement_rank] at hz
      have he := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
      have ht0 : a.representation t = a.representation 1 := by
        rw [map_one]
        exact sub_eq_zero.mp he
      exact ht1 (a.faithful ht0)
    rw [←fixedCodim_zpowers_eq_displacement_rank] at hdisp
    change Nat.log 2 _ ≤ rank A at hcomp
    have hbound : fixedCodim a.representation (zpowers t) ≤ 3 :=
      hdisp.trans ((Nat.add_le_add_right (hcomp.trans hr) 1).trans (by decide))
    have small_even (m : ℕ) (hm : m ≠ 0) (h3 : m ≤ 3) (he : Even m) : m = 2 := by
      obtain ⟨n,hn⟩ := he
      omega
    exact small_even _ hpos hbound heven
  obtain ⟨htE,hrt,htq,_⟩ := involution_actor_rank_and_fixedCodim a.representation t ho
  have htfaith : zpowers t ⊓ centralizer (X : Set (HStar I)) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (zpowers_le.mpr ht)).trans hfaith.le)
  obtain ⟨_,_,_,_,hcomm,hmove,hcompl⟩ := prime_five_small_actor a.representation a.faithful
    (by decide : 3 < 5) X (zpowers t) (IsElementaryAbelian.isPGroup 5 X)
    htE htfaith (isCubic_of_isQuadratic htq) (by rw [hd,hrt])
  exact ⟨ho,hd,hcomm,hmove,hcompl⟩

private theorem five_core_actor_rank_one
    {D : Type*} [Group D] [Finite D]
    (X A : Subgroup D) [X.Normal] [IsElementaryAbelian 5 X]
    (hc : Nat.card X = 5 ∨ Nat.card X = 25)
    (hA : IsElementaryTwo A) (hfaith : A ⊓ centralizer (X : Set D) = ⊥)
    (hcomm : ∀ t ∈ A, t ≠ 1 → Nat.card (⁅X,zpowers t⁆ : Subgroup D) = 5) :
    rank A = 1 := by
  let := hA.2
  have hr := five_core_actor_rank_le_two X A hc hA hfaith
  have hp := hA.rank_pos
  by_contra hn
  have hr2 : rank A = 2 := by omega
  have hAc : Nat.card A = 4 := by rw [hA.card_eq_two_pow_rank,hr2]; rfl
  let φ : A →* MulAut X := (MulAut.conjNormal : D →* MulAut X).comp A.subtype
  have hi : Function.Injective φ := five_core_conjugation_injective X A hfaith
  rcases hc with hc | hc
  · let : Fact (Nat.Prime (Nat.card X)) := ⟨hc ▸ (by decide : Nat.Prime 5)⟩
    let : IsCyclic X := isCyclic_of_prime_card hc
    let : IsCyclic (MulAut X) := (IsCyclic.mulAutMulEquiv X).isCyclic.mpr inferInstance
    let : IsCyclic A := isCyclic_of_injective φ hi
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hAc inferInstance
  · obtain ⟨t,ht,hinv⟩ := IsElementaryAbelian.exists_inverting_of_four_group (p := 5)
      (by decide) hc hAc φ hi
    have ht1 : (t : D) ≠ 1 := fun he => ht (Subtype.ext he)
    have hfull : ⁅X,zpowers (t : D)⁆ = X := by
      apply le_antisymm (commutator_le_left _ _)
      intro x hx
      have h5 : x ^ 5 = 1 := congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 5 X) (⟨x,hx⟩ : X))
      have hinv2 : (x ^ 2)⁻¹ = x ^ 3 := by
        apply inv_eq_of_mul_eq_one_left
        rw [←pow_add]
        exact h5
      have hti : (t : D) * x^2 * (t : D)⁻¹ = (x^2)⁻¹ :=
        congrArg Subtype.val (hinv ⟨x^2,X.pow_mem hx 2⟩)
      have he : (t : D) * x^2 * (t : D)⁻¹ * (x^2)⁻¹ = x := by
        rw [hti,hinv2,←pow_add]
        change x^(5+1) = x
        rw [pow_add,h5,pow_one,one_mul]
      rw [commutator_comm]
      exact he ▸ commutator_mem_commutator (mem_zpowers (t : D)) (X.pow_mem hx 2)
    have hh := hcomm t t.property ht1
    rw [hfull,hc] at hh
    omega

/-- The selected actor is a single reflection, and both literal denominators
have the source rank-one equality under reciprocal endpoint reversal. -/
theorem local_five_critical_rank_one
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (X : Subgroup (HStar I)) [X.Normal] [IsElementaryAbelian 5 X]
    (hX : Nat.card X = 5 ∨ Nat.card X = 25)
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    let A := actorImage I (c.endpoint.conjugate (F.UH I))
    rank A = 1 ∧ Nat.card A = 2 ∧ fixedCodim a.representation A = 2 ∧
    Nat.card (⁅X,A⁆ : Subgroup (HStar I)) = 5 ∧
    Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,A⁆) = 4 ∧
    IsCompl (subspaceCommutator a.representation ⊤ ⁅X,A⁆)
      (fixedSpace a.representation (⁅X,A⁆ ⊔ A)) ∧
    Nat.log 2 ((commutatorPreimage (F.UH I) (c.endpoint.conjugate (F.UH I))
      (c.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 ∧
    ∃ r : SelectedQuadraticEndpoint hf a,
      (∀ D : Subgroup G, I ≤ normalizer (D : Set G) →
        r.endpoint.conjugate (c.endpoint.conjugate D) = D) ∧
      r.endpoint.representative * c.endpoint.representative ∈ I ∧
      rank (actorImage I (r.endpoint.conjugate (F.UH I))) = 1 ∧
      Nat.log 2 ((commutatorPreimage (F.UH I) (r.endpoint.conjugate (F.UH I))
        (r.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 := by
  let A := actorImage I (c.endpoint.conjugate (F.UH I))
  obtain ⟨_,hfaith⟩ := local_critical_actor_control h structural previous I hI hn hf c.endpoint hb X hgen
  obtain ⟨_,hall⟩ := local_five_critical_reflections h structural previous I hI hn a hf c hb X hX hgen
  have hA : IsElementaryTwo A := c.quadratic.1
  have hr : rank A = 1 := five_core_actor_rank_one X A hX hA hfaith
    (fun t ht ht1 => (hall t ht ht1).2.2.1)
  have hcard : Nat.card A = 2 := by rw [hA.card_eq_two_pow_rank,hr]; rfl
  let : IsCyclic A := isCyclic_of_prime_card hcard
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have htA : t ∈ A := ht ▸ mem_zpowers t
  have ht1 : t ≠ 1 := by intro he; rw [he,zpowers_one_eq_bot] at ht; exact hA.1 ht.symm
  obtain ⟨_,hd,hcomm,hmove,hcompl⟩ := hall t htA ht1
  rw [ht] at hd hcomm hmove hcompl
  have hden : Nat.log 2 ((commutatorPreimage (F.UH I) (c.endpoint.conjugate (F.UH I))
      (c.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 := by
    have hh := c.comparison
    have hp := c.denominator_rank_pos
    change _ ≤ rank A at hh
    rw [hr] at hh
    change Nat.log 2 ((commutatorPreimage (F.UH I) (c.endpoint.conjugate (F.UH I))
      (c.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) ≤ 1 at hh
    change 0 < Nat.log 2 ((commutatorPreimage (F.UH I) (c.endpoint.conjugate (F.UH I))
      (c.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) at hp
    omega
  exact ⟨hr,hcard,hd,hcomm,hmove,hcompl,hden,c.rank_one_reversal hb hr hden⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
