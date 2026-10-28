module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallFactorDisplacement
public import Theory.Representation.BinaryOffender.SubgroupMovedDimension
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.FrattiniAction
public import Theory.SpecificGroups.PSL2.ElevenInvolutionGeneration
public import Theory.SpecificGroups.PSL2.ThreeInvolutionGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.InnerSeeds

/-!
# Native degree obstruction for an actor in a simple-group square

Conjugating one coordinate of a pair retains a cyclic second projection.
Perfectness puts the first factor in the generated group, so its moved
space is bounded by the displacement of the original pair. Fixed layers
are retained; no identification of the pair with a factor is required.
Source application: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree

private theorem factor_le_conjugate_join {J : Type*} [Group J] [Group.IsPerfect J]
    (t u : J) {n : ℕ} (c : Fin n → J)
    (hg : closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤) :
    (⊤ : Subgroup J).prod ⊥ ≤
      ⨆ i, (zpowers (t,u)).map (MulAut.conj (c i,1)).toMonoidHom := by
  let H : Subgroup (J × J) :=
    ⨆ i, (zpowers (t,u)).map (MulAut.conj (c i,1)).toMonoidHom
  have hproj : H.map (MonoidHom.fst J J) = ⊤ := by
    apply top_unique
    rw [← hg]
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact mem_map_of_mem _ ((le_iSup (fun i =>
      (zpowers (t,u)).map (MulAut.conj (c i,1)).toMonoidHom) i)
        (mem_map_of_mem _ (mem_zpowers (t,u))))
  have hcyclic : H ≤ (⊤ : Subgroup J).prod (zpowers u) := by
    apply iSup_le
    intro i
    rw [MonoidHom.map_zpowers, zpowers_le]
    refine ⟨mem_top _,?_⟩
    change 1*u*1⁻¹ ∈ zpowers u
    simp
  have hderived : ⁅H,H⁆ ≤ (⊤ : Subgroup J).prod ⊥ := by
    have hh := commutator_mono hcyclic hcyclic
    rw [commutator_prod_prod,commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (zpowers u))] at hh
    exact hh.trans (prod_mono le_top le_rfl)
  have hsurj : (⁅H,H⁆).map (MonoidHom.fst J J) = ⊤ := by
    rw [map_commutator,hproj,← _root_.commutator_def,Group.IsPerfect.commutator_eq_top]
  rintro ⟨x,y⟩ hxy
  have hy : y = 1 := mem_bot.mp hxy.2
  subst y
  obtain ⟨z,hz,hzx⟩ := (show x ∈ (⁅H,H⁆).map (MonoidHom.fst J J) by rw [hsurj]; trivial)
  have hz1 : z.2 = 1 := mem_bot.mp (hderived hz).2
  have he : z = (x,1) := Prod.ext hzx hz1
  exact he ▸ (commutator_le_self H hz)

private def firstFactorEquiv (J : Type*) [Group J] :
    ((⊤ : Subgroup J).prod (⊥ : Subgroup J)) ≃* J where
  toFun x := x.1.1
  invFun x := ⟨(x,1),⟨mem_top _,one_mem _⟩⟩
  left_inv x := Subtype.ext (Prod.ext rfl (mem_bot.mp x.property.2).symm)
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A generating conjugate budget in one factor bounds the degree of a
faithful action by the displacement of the actual pair. -/
theorem prime_degree_le_conjugate_displacement
    {J V : Type*} [Group J] [Finite J] [IsSimpleGroup J] [Group.IsPerfect J]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (J × J) V) (hf : Function.Injective ρ)
    (t u : J) {n : ℕ} (c : Fin n → J)
    (hg : closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ∣ Nat.card J) :
    orderOf (2 : ZMod p) ≤ n * Module.finrank (ZMod 2) (ρ (t,u) - LinearMap.id).range := by
  let K : Subgroup (J × J) := (⊤ : Subgroup J).prod ⊥
  let e : K ≃* J := firstFactorEquiv J
  let : IsSimpleGroup K := e.isSimpleGroup
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let W := Representation.BinaryOffender.invariantSubspace ρ K
    (Representation.BinaryOffender.subspaceCommutator ρ ⊤ K)
    (Representation.BinaryOffender.subspaceCommutator_invariant ρ ⊤ K)
  have hi : Function.Injective W.toRepresentation :=
    Representation.BinaryOffender.faithful_on_moved_of_simple_perfect ρ K
      (hf.comp K.subtype_injective)
  have hd := Representation.BinaryPrimeDegree.orderOf_le_finrank W.toRepresentation hi hp hp2
    (show p ∣ Nat.card K by rw [Nat.card_congr e.toEquiv]; exact hdiv)
  exact hd.trans (Representation.BinaryOffender.moved_finrank_le_mul_displacement_of_conjugates
    ρ K (t,u) (fun i => (c i,1)) (factor_le_conjugate_join t u c hg))

private theorem binary_order_gt_eight {p : ℕ} (hp : p.Prime)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) : 8 < orderOf (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have ht : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    exact hp2 he
  have hpos := (isUnit_iff_ne_zero.mpr ht).isOfFinOrder.orderOf_pos
  by_contra hle
  have hb : orderOf (2 : ZMod p) ≤ 8 := by omega
  have hd : p ∣ 2 ^ orderOf (2 : ZMod p) - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (one_le_pow₀ (by decide : 1≤(2:ℕ))),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
      pow_orderOf_eq_one,sub_self]
  generalize orderOf (2 : ZMod p) = k at *
  have hd' : p ∣ 3*3*5*7*17*31*127 := hd.trans (by interval_cases k <;> norm_num)
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 127)] at hd'
  omega

private theorem four_conjugates_of_three {J : Type*} [Group J] (t : J)
    (h : ∃ c : Fin 3 → J, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤) :
    ∃ c : Fin 4 → J, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  obtain ⟨c,hc⟩ := h
  refine ⟨Fin.lastCases 1 c,top_unique ?_⟩
  rw [← hc]
  apply Subgroup.closure_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨i.castSucc,by simp⟩

private theorem four_involution_conjugates
    {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (t : PSL(2,F)) (ht : t ≠ 1) (ht2 : t^2=1) :
    ∃ c : Fin 4 → PSL(2,F), closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h11 : p = 11
  · exact four_conjugates_of_three t
      (Theory.PSL2.ElevenConjugateBudget.three_involution_conjugates_of_card
        (hF.trans h11) (MulEquiv.refl _) t (orderOf_eq_prime ht2 ht))
  by_cases h13 : p = 13
  · let : Fintype F := Fintype.ofFinite F
    let eF : ZMod p ≃+* F := FiniteField.ringEquivOfCardEq (by
      rw [ZMod.card,←Nat.card_eq_fintype_card,hF])
    let e := GorensteinWalter.psl2RingEquiv eF
    obtain ⟨v,hv,hv2,c,hc⟩ :=
      CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.innerSeeds
        p (Or.inl h13)
    obtain ⟨g,hg⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj (e v) t
      ((e.orderOf_eq v).trans (orderOf_eq_prime hv2 hv)) (orderOf_eq_prime ht2 ht))
    let a := e.trans (MulAut.conj g)
    have hv' : a v = t := hg
    refine ⟨fun i => a (c i),?_⟩
    have hh := congrArg (Subgroup.map a.toMonoidHom) hc
    simpa only [MonoidHom.map_closure,←Set.range_comp,Function.comp_def,
      MulEquiv.coe_toMonoidHom,map_mul,map_inv,hv',
      Subgroup.map_top_of_surjective a.toMonoidHom a.surjective] using hh
  · apply four_conjugates_of_three
    exact Theory.PSL2.exists_three_involution_conjugates ho (Or.inl rfl)
      (by simpa only [pow_one] using hF) (by simp only [pow_one]; omega) t ht ht2

private theorem prime_dvd_card_psl {F : Type} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    p ∣ Nat.card PSL(2,F) := by
  rw [GorensteinWalter.psl2_card_formula F ⟨p,1,hp,ho,by decide,by simpa only [pow_one] using hF⟩,hF]
  have he : 2 ∣ p^2-1 := by
    obtain ⟨k,hk⟩ := ho.pow (n := 2)
    exact ⟨k,by omega⟩
  rw [Nat.mul_div_assoc p he]
  exact dvd_mul_right p _

/-- Every nonidentity involution in the actual PSL₂ square has binary
displacement dimension greater than two in a faithful representation. -/
theorem involution_displacement_gt_two
    {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (hmod : p % 24 = 11 ∨ p % 24 = 13)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (PSL(2,F) × PSL(2,F)) V) (hf : Function.Injective ρ)
    (v : PSL(2,F) × PSL(2,F)) (hv : v ≠ 1) (hv2 : v^2=1) :
    2 < Module.finrank (ZMod 2) (ρ v - LinearMap.id).range := by
  have hlarge : 3 < Nat.card F := by omega
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Group.IsPerfect PSL(2,F) := GorensteinWalter.psl2_isPerfect_of_card_gt_three F hlarge
  have hbound (σ : Representation (ZMod 2) (PSL(2,F) × PSL(2,F)) V)
      (hi : Function.Injective σ) (t u : PSL(2,F)) (ht : t≠1) (ht2 : t^2=1) :
      2 < Module.finrank (ZMod 2) (σ (t,u) - LinearMap.id).range := by
    obtain ⟨c,hc⟩ := four_involution_conjugates hp ho hF hmod t ht ht2
    have hh := prime_degree_le_conjugate_displacement σ hi t u c hc hp
      (by omega : p≠2) (prime_dvd_card_psl hp ho hF)
    have hb := binary_order_gt_eight hp hmod
    omega
  by_cases hfst : v.1=1
  · have hsnd : v.2≠1 := fun he => hv (Prod.ext hfst he)
    let e : (PSL(2,F) × PSL(2,F)) ≃* (PSL(2,F) × PSL(2,F)) := MulEquiv.prodComm
    exact hbound (ρ.comp e.toMonoidHom) (hf.comp e.injective) v.2 v.1 hsnd
      (congrArg Prod.snd hv2)
  · exact hbound ρ hf v.1 v.2 hfst (congrArg Prod.fst hv2)

private theorem displacement_rank_le_two {B X : Type*} [Group B] [Group X] [Finite X]
    [IsElementaryAbelian 2 X] (b : B →* MulAut X) (v : B)
    (hc : Nat.card (commutatorAction (zpowers (b v)) X) ≤ 4) :
    Module.finrank (ZMod 2)
      (Representation.FrattiniAction.ofAutomorphismHom b v - LinearMap.id).range ≤ 2 := by
  let ρ := Representation.FrattiniAction.ofAutomorphismHom b
  let C := commutatorAction (zpowers (b v)) X
  let R : Submodule (ZMod 2) (Additive X) := (ρ v - LinearMap.id).range
  have hmem (x : R) : (x : Additive X).toMul ∈ C := by
    obtain ⟨w,hw⟩ := x.property
    rw [← hw]
    rw [LinearMap.sub_apply,LinearMap.id_apply,Representation.FrattiniAction.ofAutomorphismHom_apply]
    rw [toMul_sub,div_eq_mul_inv]
    change b v w.toMul * w.toMul⁻¹ ∈ C
    rw [mul_comm]
    dsimp only [C]
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨b v,mem_zpowers _⟩,w.toMul,rfl⟩
  let j : R → C := fun x => ⟨(x : Additive X).toMul,hmem x⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact Additive.toMul.injective (show (x : Additive X).toMul = (y : Additive X).toMul from
      congrArg (fun z : C => (z : X)) he)
  have hcard := (Nat.card_le_card_of_injective j hj).trans hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hcard

/-- The multiplicative form retains the original automorphism and its
literal displacement subgroup. -/
theorem involution_displacement_card_gt_four
    {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (hmod : p % 24 = 11 ∨ p % 24 = 13)
    {X : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    (b : (PSL(2,F) × PSL(2,F)) →* MulAut X) (hb : Function.Injective b)
    (v : PSL(2,F) × PSL(2,F)) (hv : v≠1) (hv2 : v^2=1) :
    4 < Nat.card (commutatorAction (zpowers (b v)) X) := by
  let ρ := Representation.FrattiniAction.ofAutomorphismHom b
  have hρ : Function.Injective ρ := by
    intro x y he
    apply hb
    ext w
    exact Additive.ofMul.injective (DFunLike.congr_fun he (Additive.ofMul w))
  have hh := involution_displacement_gt_two hp ho hF hmod ρ hρ v hv hv2
  by_contra hle
  have hl := displacement_rank_le_two b v (by omega)
  exact (not_lt_of_ge hl) hh

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The actual nontrivial Frattini-image branch is impossible: the original
first summand supplies displacement at most four, contradicting the native
degree bound on its faithful invariant span. The trivial image survives. -/
theorem Data.moduleFrattiniImage_eq_bot (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    moduleFrattiniImage D H = ⊥ := by
  by_contra hne
  let Q := (enlargedResidual T L H).pCoreIn 2
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
  let : IsElementaryAbelian 2 (CoreFrattiniSection T L H) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 (h.moduleCoreSpan hn) :=
    IsElementaryAbelian.of_injective (h.moduleCoreSpan hn).subtype (h.moduleCoreSpan hn).subtype_injective
  let : IsElementaryAbelian 2 (moduleFrattiniImage D H) :=
    h.moduleFrattiniImage_elementary s.full_eq_local
  obtain ⟨κ,hκ,_,he,_⟩ := h.exists_coreSpan_inner_embedding f hn hs hK hp ho hm hmod hP hc hne
  have hb := (h.coreSpanQuotientAction_faithful f hn hs hK hp ho hm hmod hP hc hne).2
  obtain ⟨a,ha,_,hsmall⟩ := h.exists_firstModule_small_actor f hn hs.toLocalInput hP hc hne
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let E := e.trans (eF.prodCongr eF)
  let b := (h.coreSpanQuotientAction hn).comp E.symm.toMonoidHom
  have hi : Function.Injective b := hb.comp E.symm.injective
  have hv : E (κ a) ≠ 1 := by
    intro hzero
    apply ha
    apply hκ
    apply E.injective
    simpa only [map_one] using hzero
  have hv2 : E (κ a)^2=1 := by
    have ha2 : a^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (moduleFrattiniImage D H)) a
    rw [←map_pow,←map_pow,ha2,map_one,map_one]
  have hlarge := OddSmallDegree.involution_displacement_card_gt_four hp ho hF hmod
    b hi (E (κ a)) hv hv2
  have hbval : b (E (κ a)) = h.coreSpanModuleAction s.full_eq_local hn a := by
    change h.coreSpanQuotientAction hn (E.symm (E (κ a))) = _
    rw [E.symm_apply_apply,he]
    rfl
  rw [hbval] at hlarge
  omega

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open BinaryThreeAction BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unchanged original enlargement source now has trivial original
module image on the containing core's Frattini quotient. -/
theorem SourceCubicNormalizerEnlargement.exists_trivial_moduleFrattiniImage
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ _h : Data D H,
      D.fullModule = D.moduleSubgroup ∧
      ¬ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      moduleFrattiniImage D H = ⊥ := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  exact ⟨H,P,h,s.full_eq_local,hn,hs.toLocalInput,
    h.moduleFrattiniImage_eq_bot f hn hs hK hp ho hm h24 hP hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
