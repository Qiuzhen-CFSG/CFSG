module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPushingUp
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Constrained
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Mathieu.M22.Properties.ThreeRank

/-!
# Control of Mathieu point centralizers

A normal M22 residual excludes the contained-Fitting alternative of C.2.13.
In the quotient by the ambient two-core it is a centerless component of
three-rank two. Strong quasithinness makes that component normal, and lifting
normality contradicts the original span-normalizer condition. This argument
uses the original moved module without identifying it with a block module.

In characteristic two the escaping ordinary components are also impossible;
the existing normal-seed theorem excludes constrained components. For a
marked M23 cocode vector, its index-23 stabilizer supplies an ambient Sylow
two-subgroup in its centralizer. The original chosen-module applications in
NonFFSourceMathieuPointControl use even characteristic to complete this case
of source 8.1.1.

Source: Aschbacher--Smith, C.2.11--13, C.3.2--4, C.4.8 and 8.1.1,
printed pp.148--154 and712--713, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open Sporadic.Mathieu MathieuCode Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
variable {G : Type*} [Group G] [Finite G]

private theorem normal_m22_of_fitting_contained
    (B M : Subgroup G) (hBM : B ≤ M) (hn : M ≤ normalizer (B : Set G))
    (hB : (B.subgroupOf M).IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* M22)
    (hr : primeRank 3 (G ⧸ pCore 2 G) ≤ 2)
    (hf : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M) : B.Normal := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let P := B.map q
  let C := M.map q
  have hFC : generalizedFitting (G ⧸ pCore 2 G) ≤ C := by
    have hh := map_mono (f := q) hf
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hh
  have hC2 : pCore 2 C = ⊥ :=
    twoCore_eq_bot_of_generalizedFitting_le C hFC (pCore_quotient_pCore_eq_bot 2)
  have hPC : P ≤ C := map_mono hBM
  have hCP : C ≤ normalizer (P : Set (G ⧸ pCore 2 G)) :=
    (map_mono hn).trans (B.le_normalizer_map q)
  let A := P.subgroupOf C
  let : A.Normal := normal_subgroupOf_of_le_normalizer hCP
  let a : A ≃* P := subgroupOfEquivOfLe hPC
  have hA2 : pCore 2 A = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : A.Normal).isSubnormal,hC2]
    ext x
    change (x : C) = 1 ↔ x = 1
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  have hP2 : pCore 2 P = ⊥ := by
    have hh := pCore_map_iso 2 a
    rw [hA2,Subgroup.map_bot] at hh
    exact hh.symm
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let c : P ≃* M22 := ((q.subgroupMap B).pCoreQuotientEquiv
    (q.subgroupMap_surjective B) hk |>.trans
      ((QuotientGroup.quotientMulEquivOfEq hP2).trans QuotientGroup.quotientBot)).symm.trans e
  let := m22_isSimpleGroup
  let : IsQuasisimple M22 :=
    { toIsPerfect := pairResidual_m22_perfect
      simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv (a.trans c).symm
  have hcomp : IsComponent (G ⧸ pCore 2 G) P :=
    IsComponent.of_generalizedFitting_overgroup hPC
      ⟨(inferInstance : A.Normal).isSubnormal,inferInstance⟩ hFC
  have hz : center P = ⊥ := by
    have hh := FixedElementary.map_center c
    rw [m22_center_eq_bot] at hh
    exact (map_eq_bot_iff_of_injective _ c.injective).mp hh
  have hnormal : P.Normal := hcomp.normal_of_centerless_of_primeRank hz 3 (by
    rw [primeRank_congr 3 c,m22_primeRank_three]
    omega)
  have hQN : pCore 2 G ≤ M := by
    have hk : pCore 2 G ≤ (generalizedFitting (G ⧸ pCore 2 G)).comap q := by
      simpa only [q,QuotientGroup.ker_mk'] using
        MonoidHom.ker_le_comap q (generalizedFitting (G ⧸ pCore 2 G))
    exact hk.trans hf
  have hsup : (B ⊔ pCore 2 G).Normal := by
    have hh := hnormal.comap q
    simpa only [P,comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  let := hsup
  let : (B.subgroupOf (B ⊔ pCore 2 G)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer (hQN.trans hn))
  have hsub : B.IsSubnormal := IsSubnormal.trans le_sup_left
    (inferInstance : (B.subgroupOf (B ⊔ pCore 2 G)).Normal).isSubnormal hsup.isSubnormal
  have hself : (⊤ : Subgroup B).IsCComponent := by
    have hh := hB.subgroupOf_of_le (show B ≤ B from le_rfl) hBM
    simpa only [subgroupOf_self] using hh
  have hcompB : B.IsCComponent := by
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hself.map_subtype hsub
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  exact cComponent_normal_of_quotient_normal hcompB (pCore 2 G) hnormal

/-- A normal M22 source residual excludes the contained-Fitting alternative
of C.2.13, without identifying its full block module. -/
theorem m22_seed_not_fitting_contained
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : M ≤ normalizer (B : Set G))
    (e : (B ⧸ pCore 2 B) ≃* M22) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
  intro hf
  let A := B.subgroupOf H
  let N := M.subgroupOf H
  have hBH := h.component_le.trans h.local_le
  let a : A ≃* B := subgroupOfEquivOfLe hBH
  let n : N ≃* M := subgroupOfEquivOfLe h.local_le
  have he : (B.subgroupOf M).map n.symm.toMonoidHom = A.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩; exact hb
    · intro hx; exact ⟨⟨(x : H),x.property⟩,hx,rfl⟩
  have hA : (A.subgroupOf N).IsCComponent := he ▸ h.component.map_equiv n.symm
  have hNA : N ≤ normalizer (A : Set H) := by
    rw [←subgroupOf_normalizer_eq hBH]
    exact comap_mono hn
  have hr : primeRank 3 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin 3 (by decide) (by decide))
  let : A.Normal := normal_m22_of_fitting_contained A N (comap_mono h.component_le)
    hNA hA ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e) hr hf
  have hs : conjugateSpanBy B M = B :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hnH : H ≤ normalizer (B : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      A,map_subgroupOf_eq_of_le hBH] using hh
  apply hstrict.not_ge
  rw [←h.normalizer_span_eq,hs]
  exact le_inf le_rfl hnH
/-- An odd-index stabilizer in a Sylow overgroup contains an ambient Sylow. -/
private theorem exists_sylow_in_point_of_odd_index
    (T : Sylow 2 G) (N C : Subgroup G) (hTN : (T : Subgroup G) ≤ N)
    (hi : Odd (C.subgroupOf N).index) : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ C := by
  let P : Sylow 2 (C.subgroupOf N) := Classical.choice inferInstance
  let R : Subgroup N := (P : Subgroup (C.subgroupOf N)).map (C.subgroupOf N).subtype
  have hr : ¬ 2 ∣ R.index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hi.not_two_dvd_nat
  have hN : ¬ 2 ∣ N.index := fun hd => T.not_dvd_index (hd.trans (index_dvd_of_le hTN))
  let U : Subgroup G := R.map N.subtype
  have hu : ¬ 2 ∣ U.index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul hr hN
  refine ⟨(P.isPGroup'.map (C.subgroupOf N).subtype |>.map N.subtype).toSylow hu,?_⟩
  rintro _ ⟨r,⟨p,hp,rfl⟩,rfl⟩
  exact p.property

/-- Every distinguished M23 cocode vector centralizer contains an ambient
Sylow two-subgroup, since its stabilizer has index 23. -/
theorem m23_pair_contains_sylow (W : Subgroup G) [IsElementaryAbelian 2 W]
    (T : Sylow 2 G) (hTN : (T : Subgroup G) ≤ normalizer (W : Set G))
    (a : Automizer W ≃* M23)
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) =
      m23CocodeRepresentation (a b) (E v))
    (x : W) (hx : E (Additive.ofMul x) ∈ m23WeightTwoOrbit) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({(x : G)} : Set G) := by
  let N := normalizer (W : Set G)
  let q : N →* M23 := a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  let C := cocodeVectorStabilizer m23CocodeRepresentation (E (Additive.ofMul x))
  have hc : (centralizer ({(x : G)} : Set G)).subgroupOf N = C.comap q := by
    ext n
    simp only [mem_subgroupOf, mem_centralizer_singleton_iff, mem_comap]
    change (n : G) * (x : G) = (x : G) * n ↔
      m23CocodeRepresentation (a (W.normalizerMonoidHom.rangeRestrict n))
        (E (Additive.ofMul x)) = E (Additive.ofMul x)
    rw [←hE (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul x)]
    constructor
    · intro hn
      congr 1
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (n : G) * (x : G) * (n : G)⁻¹ = (x : G)
      rw [mul_inv_eq_iff_eq_mul]
      exact hn
    · intro hn
      have hh := congrArg (fun w : Additive W => ((Additive.toMul w : W) : G)) (E.injective hn)
      change (n : G) * (x : G) * (n : G)⁻¹ = (x : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hi : C.index = 23 := by
    have hh := C.card_mul_index
    obtain ⟨c⟩ := m23WeightTwoOrbit_stabilizer_equiv hx
    rw [Nat.card_congr c.toEquiv,m22_order,m23_order] at hh
    omega
  apply exists_sylow_in_point_of_odd_index T N _ hTN
  rw [hc,C.index_comap_of_surjective (f := q)
    (a.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective),hi]
  decide

/-- In characteristic two the actual normal M22 residual cannot push up.
Both the contained and escaping alternatives of C.2.13 are excluded. -/
theorem m22_seed_not_strict_of_characteristicTwo
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : M ≤ normalizer (B : Set G))
    (e : (B ⧸ pCore 2 B) ≃* M22)
    (hfit : generalizedFitting H = pCore 2 H) : ¬ M < H := by
  intro hstrict
  have hout := m22_seed_not_fitting_contained h hstrict hn e
  obtain ⟨K,hK,hqu,hKout,_,ho | hfK⟩ := h.ordinary_or_constrained_escape hout
  · have hle : K ≤ pCore 2 H := hfit ▸ component_le_generalizedFitting H K ho
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    exact ho.isCComponent.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hle) (inclusion_injective hle))
  · let := m22_isSimpleGroup
    let : IsQuasisimple M22 :=
      { toIsPerfect := pairResidual_m22_perfect
        simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
          QuotientGroup.quotientBot).isSimpleGroup }
    let c : (M22 ⧸ center M22) ≃* M22 :=
      (QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans QuotientGroup.quotientBot
    let q : B →* (M22 ⧸ center M22) :=
      c.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
    have hq : Function.Surjective q := c.symm.surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    let : Group.IsSolvable q.ker := by
      have hk : q.ker = pCore 2 B := by
        rw [MonoidHom.ker_comp_of_injective _ _ c.symm.injective,
          MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
      rw [hk]
      let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
      infer_instance
    exact h.no_constrained_mathieu_normal_seed (normal_subgroupOf_of_le_normalizer hn)
      (Or.inr (Or.inl ⟨c⟩)) q hq K hK hqu hKout hfK

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs

