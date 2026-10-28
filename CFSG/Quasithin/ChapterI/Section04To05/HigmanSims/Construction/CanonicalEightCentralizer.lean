module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneMatrices
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.RootLiftCorrection
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.ElementaryPlaneJoin
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedEightCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCentralFour
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneRootCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreInvolutionFusion

/-!
# The original nonabelian centralizer of a nonseed eight

The canonical plane construction retains its second binary shear. A central
cyclic-four generator of the first point core lies in the whole normalizer
core; the fixed-square exclusion shows that the second lift inverts it.
The full-H nonseed orbit calculation supplies the actual centralizer order.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
open BinaryPlane
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem canonical_aligned (h : TypeAt z V) :
    ∃ (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
      (W A : Subgroup G) (u v a : G) (b : normalizer (V : Set G)), W ≤ V ∧ Nat.card W = 4 ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      W ≤ A ∧ A ≤ centralizer (W : Set G) ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      u ∈ W ∧ v ∈ W ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      a ∈ (involutionCentralizer u).pCoreIn 2 ∧
      (b : G) ∈ (involutionCentralizer v).pCoreIn 2 ∧
      a ∉ (normalizer (V : Set G)).pCoreIn 2 ∧
      (b : G) ∉ (normalizer (V : Set G)).pCoreIn 2 ∧
      a * (b : G) ∉ (normalizer (V : Set G)).pCoreIn 2 ∧
      A = W ⊔ (zpowers a ⊔ zpowers (b : G)) ∧
      u = ((h.seedCoordinates e).symm e0 : G) ∧ b ^ 2 = 1 ∧
      V.normalizerMonoidHom b = betaAt (h.seedCoordinates e) := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let e : P ≃* Multiplicative (Fin 3 → ZMod 4) :=
    (MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans
      (h.normalizer_core.some.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 4)).symm)
  let c := h.seedCoordinates e
  let W := planeAt c
  have hWV : W ≤ V := planeAt_le c
  have hWM : W ≤ M := hWV.trans V.le_normalizer
  have hW4 : Nat.card W = 4 := planeAt_card c
  let : IsElementaryAbelian 2 W := planeAt_elementary c
  let u : V := c.symm e0
  let v : V := c.symm e1
  have huW : (u : G) ∈ W := by
    refine ⟨u, ?_, rfl⟩
    change (c (c.symm e0)).toAdd 2 = 0
    rw [c.apply_symm_apply]
    rfl
  have hvW : (v : G) ∈ W := by
    refine ⟨v, ?_, rfl⟩
    change (c (c.symm e1)).toAdd 2 = 0
    rw [c.apply_symm_apply]
    rfl
  have hu1 : (u : G) ≠ 1 := by
    intro he
    have hh := congrArg c (show u = 1 from Subtype.ext he)
    simp only [u, c.apply_symm_apply, map_one] at hh
    exact (by decide +kernel : e0 ≠ 1) hh
  have hv1 : (v : G) ≠ 1 := by
    intro he
    have hh := congrArg c (show v = 1 from Subtype.ext he)
    simp only [v, c.apply_symm_apply, map_one] at hh
    exact (by decide +kernel : e1 ≠ 1) hh
  have huv : (u : G) ≠ v := by
    intro he
    have hh := congrArg c (show u = v from Subtype.ext he)
    simp only [u, v, c.apply_symm_apply] at hh
    exact (by decide +kernel : e0 ≠ e1) hh
  have hcoord : (((e.symm (Multiplicative.ofAdd ![2, 0, 0]) : P) : M) : G) = u := by
    rw [show (u : G) = ((h.seedCoordinates e).symm e0 : G) from rfl,
      h.seedCoordinates_symm_apply e e0]
    have he : ![2, 0, 0] = (fun i => binaryDouble (e0.toAdd i)) := by decide +kernel
    rw [he]
  obtain ⟨d⟩ := h.exists_binary_plane_lifts c
  obtain ⟨p, hp2, hpb, _, haQ⟩ := h.correct_plane_lifts_in_point_core e u u.property hu1
    hcoord d.a d.b d.t d.a_core d.a_square d.b_square
    d.t_square d.commutator_core d.commutator_square d.product_core
    (h.first_plane_matrix_reduction e d.a d.a_action)
    (h.second_plane_matrix_reduction e d.b d.b_action)
  let a : M := (p : M) * d.a
  let f := V.normalizerMonoidHom
  have hker : f.ker = P := by
    rw [normalizerMonoidHom_ker, h.seed_centralizer]
    exact comap_map_eq_self_of_injective M.subtype_injective P
  have hpker : f (p : M) = 1 := by
    change (p : M) ∈ f.ker
    rw [hker]
    exact p.property
  have haf : f a = alphaAt c := by
    rw [show f a = f (p : M) * f d.a from f.map_mul _ _, hpker, one_mul]
    exact d.a_action
  have hbf : f d.b = betaAt c := d.b_action
  have hpC : ((p : M) : G) ∈ centralizer (W : Set G) := by
    apply centralizer_le hWV
    rw [h.seed_centralizer]
    exact ⟨p, p.property, rfl⟩
  have haC : (a : G) ∈ centralizer (W : Set G) :=
    (centralizer (W : Set G)).mul_mem hpC d.a_plane
  let WM := W.subgroupOf M
  have hWM4 : Nat.card WM = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv).trans hW4
  let : IsElementaryAbelian 2 WM := IsElementaryAbelian.subgroupOf hWM
  have hWK : WM ≤ f.ker := by
    intro w hw
    rw [normalizerMonoidHom_ker]
    intro v hv
    let := h.elementary
    exact setLike_mul_comm hv (hWV hw)
  have hfa : f a ≠ 1 := by
    rw [haf]
    exact alphaAt_ne_one c
  have hfb : f d.b ≠ 1 := by
    rw [hbf]
    exact betaAt_ne_one c
  have hfab : f a ≠ f d.b := by
    rw [haf, hbf]
    exact alphaAt_ne_betaAt c
  have haWM : a ∈ centralizer (WM : Set M) := by
    intro w hw
    exact Subtype.ext (haC w hw)
  have hbWM : d.b ∈ centralizer (WM : Set M) := by
    intro w hw
    exact Subtype.ext (d.b_plane w hw)
  obtain ⟨hAE, hA16, hAK⟩ := elementary_plane_join f WM hWM4 hWK a d.b hp2
    d.b_square hpb haWM hbWM hfa hfb hfab
  let AM := WM ⊔ (zpowers a ⊔ zpowers d.b)
  let A := AM.map M.subtype
  let : IsElementaryAbelian 2 AM := hAE
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAc : Nat.card A = 16 := by
    rw [card_map_of_injective M.subtype_injective]
    exact hA16
  have hWmap : WM.map M.subtype = W := map_subgroupOf_eq_of_le hWM
  have hWA : W ≤ A := hWmap ▸ map_mono (show WM ≤ AM from le_sup_left)
  have hAC : A ≤ centralizer (W : Set G) := by
    change (WM ⊔ (zpowers a ⊔ zpowers d.b)).map M.subtype ≤ _
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, hWmap]
    refine sup_le ?_ (sup_le (zpowers_le.mpr haC) (zpowers_le.mpr d.b_plane))
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hAP : A ⊓ M.pCoreIn 2 = W := by
    change AM.map M.subtype ⊓ P.map M.subtype = W
    rw [← map_inf _ _ _ M.subtype_injective, ← hker, hAK, hWmap]
  have hnotP (x : M) (hx : f x ≠ 1) : (x : G) ∉ M.pCoreIn 2 := by
    intro hh
    have hxP : x ∈ P := by
      obtain ⟨q, hq, he⟩ := hh
      have he' : q = x := Subtype.ext he
      exact he' ▸ hq
    exact hx (show x ∈ f.ker from hker.symm ▸ hxP)
  have habf : f (a * d.b) ≠ 1 := by
    intro hh
    have hb2 : f d.b * f d.b = 1 := by
      rw [← map_mul]
      rw [show d.b * d.b = 1 by simpa only [pow_two] using d.b_square, map_one]
    have he := congrArg (fun x => x * f d.b) hh
    rw [map_mul, mul_assoc, hb2, mul_one, one_mul] at he
    exact hfab he
  have hjoin : A = W ⊔ (zpowers (a : G) ⊔ zpowers (d.b : G)) := by
    change (WM ⊔ (zpowers a ⊔ zpowers d.b)).map M.subtype = _
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, hWmap]
    rfl
  exact ⟨e, W, A, u, v, a, d.b, hWV, hW4, hAelem, hAc, hWA, hAC, hAP,
    huW, hvW, hu1, hv1, huv, haQ, d.b_core, hnotP a hfa, hnotP d.b hfb,
    hnotP (a * d.b) habf, hjoin, rfl, d.b_square, d.b_action⟩

/-- Original HS data construct a literal nonseed eight with full centralizer
order32, an order-four central point-core lift, and an external seed-class
involution which inverts that lift. -/
theorem TypeAt.exists_nonabelian_eight_centralizer (h : TypeAt z V) :
    ∃ (u c b : G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧
      E.val ∉ pointCoreSeedOrbit u V ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      orderOf c = 4 ∧ c ^ 2 = u ∧
      c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
        ((involutionCentralizer u).pCoreIn 2).subtype ∧
      c ∈ centralizer (E.val : Set G) ∧ b ∈ centralizer (E.val : Set G) ∧
      b ^ 2 = 1 ∧ IsConj b z ∧ ¬ Commute b c ∧ b * c * b⁻¹ = c⁻¹ := by
  obtain ⟨e, W, A, u, v, a, b, hWV, hW4, hAE, hA16, hWA, hAC, hAP,
    huW, hvW, hu1, hv1, huv, haQ, hbQ, haP, hbP, habP, hjoin, hue, hb2M, hbf⟩ :=
    canonical_aligned h
  let huT := h.at_seed_point u (hWV huW) hu1
  let hvT := h.at_seed_point v (hWV hvW) hv1
  let Q := (involutionCentralizer u).pCoreIn 2
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 (involutionCentralizer u)).map (involutionCentralizer u).subtype
    rw [← huT.centralizer_fitting]
    exact huT.seed_le_core
  let B := W ⊔ zpowers a
  have haA : a ∈ A := by
    rw [hjoin]
    exact (show zpowers a ≤ W ⊔ (zpowers a ⊔ zpowers (b : G)) from
      le_sup_left.trans le_sup_right) (mem_zpowers a)
  have hbA : (b : G) ∈ A := by
    rw [hjoin]
    exact (show zpowers (b : G) ≤ W ⊔ (zpowers a ⊔ zpowers (b : G)) from
      le_sup_right.trans le_sup_right) (mem_zpowers (b : G))
  let := hAE
  have hBA : B ≤ A := sup_le hWA (zpowers_le.mpr haA)
  have hBQ : B ≤ Q := sup_le (hWV.trans hVQ) (zpowers_le.mpr haQ)
  have hBE : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.of_injective (inclusion hBA) (inclusion_injective hBA)
  have hVP : V ≤ (normalizer (V : Set G)).pCoreIn 2 := by
    change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.normalizer_fitting]
    exact h.seed_le_normalizer_core
  have hB8 : Nat.card B = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W a
      (elemPow_eq_one_of_isElementaryAbelian a haA)
      (fun hh => haP (hVP (hWV hh))) (centralizer_le_normalizer _ (hAC haA)), hW4]
  let E : pointCoreEights u := ⟨B, hBQ, (show W ≤ B from le_sup_left) huW, hBE, hB8⟩
  have hBV : B ⊓ V = W := by
    apply le_antisymm
    · intro x hx
      exact hAP ▸ (show x ∈ A ⊓ (normalizer (V : Set G)).pCoreIn 2 from
        ⟨hBA hx.1, hVP hx.2⟩)
    · exact le_inf le_sup_left hWV
  have hBn : E.val ∉ pointCoreSeedOrbit u V := by
    rintro ⟨g, hg⟩
    change V.map (MulAut.conj (g : G)).toMonoidHom = B at hg
    by_cases hn : (g : G) ∈ normalizer (V : Set G)
    · have he : B = V := hg.symm.trans (mem_normalizer_iff_map_conj_eq.mp hn)
      have hc := congrArg (fun S : Subgroup G => Nat.card S) hBV
      rw [he, inf_idem, h.seed_card, hW4] at hc
      omega
    · have he := huT.seed_conjugate_intersection g g.property hn
      rw [hg, inf_comm, hBV] at he
      have hc := congrArg (fun S : Subgroup G => Nat.card S) he
      rw [hW4, Nat.card_zpowers, huT.involution] at hc
      omega
  have hbC : (b : G) ∈ centralizer (E.val : Set G) := by
    intro x hx
    exact setLike_mul_comm (hBA hx) hbA
  have hbH : (b : G) ∈ involutionCentralizer u := by
    apply mem_centralizer_singleton_iff.mpr
    exact (hbC u E.property.2.1).symm
  have hb2 : orderOf (b : G) = 2 := orderOf_eq_prime
    (congrArg (fun x : normalizer (V : Set G) => (x : G)) hb2M)
    (fun he => hbP (he ▸ one_mem _))
  have hbv : IsConj (b : G) v := hvT.centralizer_core_involution_isConj b hbQ hb2
  have hvz : IsConj v z := h.centralizer_core_involution_isConj v
    (by
      change v ∈ (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype
      rw [← h.centralizer_fitting]
      exact h.seed_le_core (hWV hvW)) hvT.involution
  obtain ⟨c, hc4, hc2, hcZ, hcP⟩ := huT.exists_point_core_central_four
  have hcC : c ∈ centralizer (E.val : Set G) := by
    obtain ⟨cq, hcq, rfl⟩ := hcZ
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hcq (⟨x, hBQ hx⟩ : Q))
  obtain ⟨cM, hcM, hcEq⟩ := hcP
  change (cM : G) = c at hcEq
  let cP : pCore 2 (normalizer (V : Set G)) := ⟨cM, hcM⟩
  have hnc : ¬ Commute (b : G) c := by
    have hh := h.plane_root_not_commute e b hb2M hbf cP
      (by change (cM : G) ^ 2 = _; rw [hcEq, hc2, hue])
    simpa only [cP, hcEq] using hh
  exact ⟨u, c, b, E, hWV huW, hu1, huT, hBn,
    huT.point_core_nonseed_eight_centralizer_card E hBn,
    huT.point_core_nonseed_eight_normalizer_card E hBn,
    hc4, hc2, hcZ, hcC, hbC,
    congrArg (fun x : normalizer (V : Set G) => (x : G)) hb2M,
    hbv.trans hvz, hnc, huT.point_core_central_four_inverted c hc4 hcZ b hbH hnc⟩

end CFSG.Quasithin.HigmanSims
