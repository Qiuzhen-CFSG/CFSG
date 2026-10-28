module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.JankoCentralizers
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Residual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RadicalRankTwoSeed
public import Theory.Mathieu.M22.Properties.ThreeRank

/-!
# The full M22 residual in the Mathieu J4 configuration

Choose an involution in the original C_V(T) by the two-group fixed-point
argument. The actual odd-normalizer action identifies its full component
centralizer modulo the odd core with a native J4 involution centralizer.
The solvable-kernel correspondence identifies the simple radical quotient
of the full perfect residual with M22 and proves it is a C-component.

The original odd actor centralizes the full component through the actual
projection kernel. This places the same residual normally in
C_G(z) intersect C_G(A), with its literal inclusion into the covering
component. The ambient involution centralizer is SQTK. The radical-quotient
three-rank argument therefore puts the full residual in a unique normal
C-component of C_G(z), with quasisimple two-core quotient.

The literal Hall-obstruction application retains both original J4 branches
and every component, module, residual and action witness. The order-three
pushing-up uniqueness argument, the M24 block and fixed-line identification,
and the terminal K = <L_A,K_Z> comparison remain to be established.

Source: Aschbacher--Smith 4.4.3, printed p.623, used in 4.4.14, pp.624--625;
the distinct order-three argument is 4.2.13, pp.611--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Sporadic.Mathieu

private theorem lift_residual {C Q : Type*} [Group C] [Finite C] [Group Q] [Finite Q]
    (f : C →* Q) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hQ : (solvableResidual Q).IsCComponent)
    (eQ : (solvableResidual Q ⧸ solvableRadical (solvableResidual Q)) ≃* M22) :
    (solvableResidual C).IsCComponent ∧
      Nonempty ((solvableResidual C ⧸ solvableRadical (solvableResidual C)) ≃* M22) := by
  have hc := residual_isCComponent_of_surjective f hf hQ
  let e := MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)
  let g : solvableResidual C →* solvableResidual Q :=
    e.toMonoidHom.comp (f.subgroupMap (solvableResidual C))
  have hg : Function.Surjective g := e.surjective.comp (f.subgroupMap_surjective _)
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (e.toMonoidHom.comp (f.subgroupMap (solvableResidual C))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (solvableResidual C).subtype.subgroupComap f.ker)
      (fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : f.ker => (z : C)) h)))
  exact ⟨hc,⟨(solvableRadicalQuotientEquiv g hg).trans eQ⟩⟩

namespace JankoNormalizerAction
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
  (a : JankoNormalizerAction K)
include a

/-- The full component centralizer has an actual M22 C-component residual.
Only its solvable radical is removed in the displayed simple quotient. -/
theorem involution_residual (z : K) (hz : orderOf z = 2) :
    (solvableResidual (centralizer ({z} : Set K))).IsCComponent ∧
      Nonempty ((solvableResidual (centralizer ({z} : Set K)) ⧸
        solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃* M22) := by
  let C := centralizer ({z} : Set K)
  let N := pPrimeCore 2 C
  let : Group.IsSolvable N := odd_order_theorem N
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  rcases a.involution_centralizer_models z hz with he | he
  · obtain ⟨e⟩ := he
    let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
    let : Group.IsSolvable f.ker := by
      rw [show f = e.toMonoidHom.comp (QuotientGroup.mk' N) from rfl,
        MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
      infer_instance
    obtain ⟨hc,⟨q⟩⟩ := Janko4.InvolutionCentralizers.first_residual_component
    exact lift_residual f (e.surjective.comp (QuotientGroup.mk'_surjective N)) hc q
  · obtain ⟨e⟩ := he
    let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
    let : Group.IsSolvable f.ker := by
      rw [show f = e.toMonoidHom.comp (QuotientGroup.mk' N) from rfl,
        MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
      infer_instance
    obtain ⟨hc,⟨q⟩⟩ := Janko4.InvolutionCentralizers.second_residual_component
    exact lift_residual f (e.surjective.comp (QuotientGroup.mk'_surjective N)) hc q


/-- The same residual is a C-component in the centralizer inside the actual
odd normalizer. The displayed map keeps its embedding in the full component. -/
theorem involution_residual_placement [K.Normal] (z : K) (hz : orderOf z = 2) :
    ∃ R : Subgroup (centralizer ({(z : G)} : Set G)),
      R.IsCComponent ∧ R.Normal ∧
      Nonempty ((R ⧸ solvableRadical R) ≃* M22) ∧
      R.map (centralizer ({(z : G)} : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map K.subtype := by
  let C := centralizer ({(z : G)} : Set G)
  let D := centralizer ({z} : Set K)
  let f : D →* C := K.subtype.elementCentralizerMap z
  have hi : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun w : C => (w : G)) hxy))
  have hrange : f.range = K.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.val.property
    · intro hx
      refine ⟨⟨⟨x.val,hx⟩,?_⟩,Subtype.ext rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  let : f.range.Normal := hrange.symm ▸ (inferInstance : (K.subgroupOf C).Normal)
  let e : D ≃* f.range := MonoidHom.ofInjective hi
  let R := (solvableResidual D).map f
  obtain ⟨hc,⟨q⟩⟩ := a.involution_residual z hz
  have hcR : R.IsCComponent := by
    have hh := (hc.map_equiv e).map_subtype
      (inferInstance : f.range.Normal).isSubnormal
    have hfe : f.range.subtype.comp e.toMonoidHom = f := by
      apply MonoidHom.ext
      intro x
      exact MonoidHom.ofInjective_apply hi
    simpa only [map_map,hfe] using hh
  have hm : (solvableResidual f.range).map f.range.subtype = R := by
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,map_map]
    rfl
  have hn : R.Normal := by
    rw [←hm,←normalizer_eq_top_iff]
    apply top_unique
    simpa only [normalizer_eq_top] using
      normalizer_le_normalizer_characteristic_image f.range (solvableResidual f.range)
  let t : R ≃* solvableResidual D :=
    ((solvableResidual D).equivMapOfInjective f hi).symm
  let qR := QuotientGroup.congr _ _ t (map_solvableRadical_equiv t)
  refine ⟨R,hcR,hn,⟨qR.trans q⟩,?_⟩
  simp only [R,map_map]
  rfl

end JankoNormalizerAction


/-- The M22 residual is a genuine C-component of C_G(z) ∩ C_G(A).
The odd actor centralizes the full component, as follows from its actual
projection kernel. The full residual is embedded by the original inclusions. -/
theorem janko_actor_residual_placement {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {K : Subgroup (normalizer (A : Set G))} [K.Normal]
    (a : JankoNormalizerAction K)
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)))
    (hA : (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥)
    (z : K) (hz : orderOf z = 2) :
    ∃ R : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
        centralizer (A : Set G) : Subgroup G),
      R.IsCComponent ∧ R.Normal ∧ Nonempty ((R ⧸ solvableRadical R) ≃* M22) ∧
      R.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
        centralizer (A : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) := by
  let N := normalizer (A : Set G)
  let C := centralizer ({(z : N)} : Set N)
  let D := centralizer ({((z : N) : G)} : Set G) ⊓ centralizer (A : Set G)
  let U := (centralizer (A.subgroupOf N : Set N)).subgroupOf C
  have hAK : A.subgroupOf N ≤ centralizer (K : Set N) := by
    rw [hcent,←a.kernel]
    exact (Subgroup.map_eq_bot_iff _).mp hA
  have hKA : K ≤ centralizer (A.subgroupOf N : Set N) := le_centralizer_iff.mp hAK
  obtain ⟨R,hR,hn,⟨q⟩,hr⟩ := a.involution_residual_placement z hz
  have hRK : R.map C.subtype ≤ K := by
    rw [hr]
    exact (map_le_range K.subtype _).trans_eq K.range_subtype
  have hRU : R ≤ U := fun x hx => hKA (hRK (mem_map_of_mem C.subtype hx))
  let e : U ≃* D := {
    toFun x := ⟨x.val.val.val,⟨
      mem_centralizer_singleton_iff.mpr
        (congrArg N.subtype (mem_centralizer_singleton_iff.mp x.val.property)),
      fun b hb => congrArg N.subtype (x.property (⟨b,A.le_normalizer hb⟩ : N) hb)⟩⟩
    invFun x := ⟨⟨⟨x.val,(Subgroup.centralizer_le_normalizer _ x.property.2)⟩,
      mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.1))⟩,
      fun b hb => Subtype.ext (x.property.2 b hb)⟩
    left_inv x := by ext; rfl
    right_inv x := by ext; rfl
    map_mul' x y := rfl }
  let R0 := (R.subgroupOf U).map e.toMonoidHom
  let := hn
  have hn0 : R0.Normal := (inferInstance : (R.subgroupOf U).Normal).map
    e.toMonoidHom e.surjective
  let t : R0 ≃* R := ((e.subgroupMap (R.subgroupOf U)).symm).trans
    (subgroupOfEquivOfLe hRU)
  let qt := QuotientGroup.congr _ _ t (map_solvableRadical_equiv t)
  refine ⟨R0,(hR.subgroupOf hRU).map_equiv e,hn0,⟨qt.trans q⟩,?_⟩
  calc
    R0.map D.subtype = ((R.subgroupOf U).map U.subtype).map
        (N.subtype.comp C.subtype) := by rw [map_map,map_map]; rfl
    _ = R.map (N.subtype.comp C.subtype) := by rw [map_subgroupOf_eq_of_le hRU]
    _ = (R.map C.subtype).map N.subtype := (map_map _ _ _).symm
    _ = _ := by rw [hr,map_map]

/-- Promote the full M22 radical seed into the actual involution centralizer.
The rank argument uses the simple radical quotient, so a covering center
is retained throughout. Normality is relative to C_G(z). -/
theorem mathieu_residual_ambient_placement {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {z : G} (hz : orderOf z = 2)
    {D : Subgroup G} (hD : D ≤ centralizer ({z} : Set G))
    (P : Subgroup D) (hP : P.IsCComponent)
    (eP : (P ⧸ solvableRadical P) ≃* M22) :
    ∃! Q : Subgroup (centralizer ({z} : Set G)),
      Q.IsCComponent ∧ P.map (inclusion hD) ≤ Q ∧ Q.Normal ∧
        IsQuasisimple (Q ⧸ pCore 2 Q) := by
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz; omega
  have he : zpowers z ≠ ⊥ := by
    intro hb
    exact hz1 (mem_bot.mp (hb ▸ mem_zpowers z))
  have hC : IsSQTK KnownSimple.IsKnownSimple (centralizer ({z} : Set G)) := by
    apply hG.twoLocal_sqtk
    refine ⟨zpowers z,he,?_,(normalizer_zpowers_eq_centralizer_of_order_two z hz).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers z) = 2 ^ 1 by rw [Nat.card_zpowers,hz]; rfl)
  let i := inclusion hD
  let B := P.map i
  let e : P ≃* B := P.equivMapOfInjective i (inclusion_injective hD)
  let := hP.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hPt : (⊤ : Subgroup P).IsCComponent := by
    simpa only [subgroupOf_self] using hP.subgroupOf (le_refl P)
  have hBt : (⊤ : Subgroup B).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hPt.map_equiv e
  let q := (QuotientGroup.congr _ _ e.symm (map_solvableRadical_equiv e.symm)).trans eP
  have hr : 2 ≤ primeRank 3 (B ⧸ solvableRadical B) := by
    rw [primeRank_equiv 3 q,m22_primeRank_three]
  exact Chapter1.Section02.radical_rank_component_source hC B hBt hr

open Chapter4 Chapter4.Section04
/-- The source involution is chosen in the original T-fixed module. All
component and action witnesses are retained on that same full component. -/
@[expose] def MathieuJankoFixedResidualCase {G : Type*} [Group G]
    (T L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧
    (∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f) ∧
    ∃ a : JankoNormalizerAction K,
      Function.Injective (a.projection.comp (V.subgroupOf (normalizer (A : Set G))).subtype) ∧
      (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥ ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        (solvableResidual (centralizer ({z} : Set K))).IsCComponent ∧
        Nonempty ((solvableResidual (centralizer ({z} : Set K)) ⧸
          solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃* M22) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃! Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ P.map (inclusion inf_le_left) ≤ Q ∧ Q.Normal ∧
              IsQuasisimple (Q ⧸ pCore 2 Q)

/-- Choose the involution in C_V(T), then identify its genuine perfect
centralizer residual, retaining the original covering component. -/
theorem mathieu_janko_fixed_residual {G S : Type*} [Group G] [Finite G] [Group S]
    {T L V A : Subgroup G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hT : IsPGroup 2 T)
    (hTV : T ≤ normalizer (V : Set G)) (he : IsElementaryAbelian 2 V) (hne : V ≠ ⊥)
    (h : MathieuJankoActionCase L V A S) : MathieuJankoFixedResidualCase T L V A S := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hA⟩ := h
  let := he
  have hf := inf_centralizer_ne_bot_of_pGroups T V hT
    (IsElementaryAbelian.isPGroup 2 V) hTV hne
  obtain ⟨v,hv,hvne⟩ := (V ⊓ centralizer (T : Set G)).bot_or_exists_ne_one.resolve_left hf
  obtain ⟨k,hk,hkv⟩ := hV hv.1
  let z : K := ⟨k,hk⟩
  have hzv : ((z : normalizer (A : Set G)) : G) = v := hkv
  have hz : orderOf z = 2 := by
    rw [← orderOf_coe z,← orderOf_coe (z : normalizer (A : Set G)),hzv]
    exact orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian v hv.1,hvne⟩
  let := hn
  obtain ⟨hres,hq⟩ := a.involution_residual z hz
  obtain ⟨P,hP,hPn,⟨qP⟩,hPm⟩ := janko_actor_residual_placement a hcent hA z hz
  have hzG : orderOf (((z : normalizer (A : Set G)) : G)) = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hbig := mathieu_residual_ambient_placement hG hzG inf_le_left P hP qP
  refine ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hA,z,
    hzv.symm ▸ hv.1,hz,?_,hres,hq,P,hP,hPn,⟨qP⟩,hPm,hbig⟩
  intro t ht
  rw [hzv]
  exact mem_centralizer_singleton_iff.mpr (hv.2 t ht)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal nonfaithful Hall choice gives a T-central involution and its
actual M22 residual on the same full escaping component. The residual is
placed in C_G(z) ∩ C_G(A), then in a unique normal C-component of C_G(z). -/
theorem sourceOrbit_mathieu_hall_fixed_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (MathieuPushingUpJankoInnerCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoFixedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  rcases @sourceOrbit_mathieu_hall_janko_actions G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker with
    ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hcase⟩
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  rcases hcase with hpush | ⟨hu,hj⟩
  · exact .inl hpush
  · have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
      hV.symm ▸ D.sourceOrbit_weakClosure_setup.normalizes
    exact .inr ⟨hu,mathieu_janko_fixed_residual h.simpleQTKE T.isPGroup' hTV D.elementary D.ne_bot hj⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
