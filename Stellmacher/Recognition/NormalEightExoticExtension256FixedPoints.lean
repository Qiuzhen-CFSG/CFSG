module

public import Stellmacher.Recognition.NormalEightExoticExtension256ActionSetup
public import Theory.GroupTheory.PGroup.FrattiniInvolutionAction
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Theory.GroupAction.C4SquareFixedKernel
public import Theory.GroupAction.C4SquareTransitiveKernel
public import Theory.GroupTheory.PGroup.C4SquareCentralizerFrattini

/-!
# Fixed-point reduction for the elementary sixteen

Ambient fusion gives automorphisms of the four-centralizer transitive on the
three involutions of the marked four. The fixed-point problem then reduces
to identifying the abelian base with a subgroup of the centralizer's Frattini
subgroup, and a finite calculation in its C₄-square action image.

The reduction below is conditional: it does not assert the missing Frattini
identification or the singular-action calculation. Once these hold, a putative
primitive fixed point forces all inverted base elements to have square one;
the Frattini involution lemma puts the acting involution back in the base.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), p.386, used p.395;
MacWilliams, Trans. AMS 150 (1970), §4, pp.386–393.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- The supplied ambient fusion acts transitively on the central four of its
centralizer. Only normal elementary eights in the Sylow subgroup are excluded. -/
public theorem fixedPoints_centralizer_transitive
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G)) :
    ∀ x y : centralizer (W : Set S), (x : S) ∈ W → (y : S) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set S)), a x = y := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  have hzS : orderOf ((z : center S) : S) = 2 :=
    (orderOf_coe (z : center S)).trans ((orderOf_coe z).trans hz)
  apply S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique ((z : center S) : S) hzS (z : center S).property
  intro x y hx hy
  apply hfused x y x.property y.property
  · exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (x : S) x.property)
      (fun h => hx (Subtype.ext h))
  · exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (y : S) y.property)
      (fun h => hy (Subtype.ext h))

/-- Conjugation by the four-centralizer lies in the abelian congruence kernel. -/
public theorem fixedPoints_conjugation_commute
    {P : Type*} [Group P] (W D : Subgroup P) [D.Normal]
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (c b : centralizer (W : Set P)) :
    Commute (MulAut.conjNormal (H := D) (c : P))
      (MulAut.conjNormal (H := D) (b : P)) := by
  obtain ⟨e⟩ := hmodel
  have hfix (g : centralizer (W : Set P)) (y : C4SquareExtension.Model)
      (hy : y ^ 2 = 1) : (MulAut.congr e) (MulAut.conjNormal (H := D) (g : P)) y = y := by
    have hd2 : (e.symm y) ^ 2 = 1 := by rw [← map_pow, hy, map_one]
    have hdW : (e.symm y : P) ∈ W := by
      rw [← hDO]
      exact ⟨e.symm y, subset_closure (by simpa using hd2), rfl⟩
    change e (MulAut.conjNormal (H := D) (g : P) (e.symm y)) = y
    rw [show MulAut.conjNormal (H := D) (g : P) (e.symm y) = e.symm y from ?_]
    · exact e.apply_symm_apply y
    · apply Subtype.ext
      change (g : P) * (e.symm y : P) * (g : P)⁻¹ = (e.symm y : P)
      rw [← g.property _ hdW, mul_inv_cancel_right]
  apply Commute.of_map (MulAut.congr e).injective
  exact C4SquareExtension.commute_of_fix_square_one _ _ (hfix c) (hfix b)

/-- Frattini containment and the singular-action implication suffice for the
required fixed-point assertion. Both extra hypotheses remain explicit. -/
public theorem fixed_points_of_frattini_and_singular_action
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hWD : W ≤ D) (hWB : W ≤ B) (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (hDΦ : D ≤ (frattini (centralizer (W : Set P))).map
      (centralizer (W : Set P)).subtype)
    (hsingular : ∀ b ∈ B, (∃ d ∈ D, Commute b d ∧ d ^ 2 ≠ 1) →
      ∀ d ∈ D, b * d * b⁻¹ = d⁻¹ → d ^ 2 = 1) :
    ∀ b ∈ B, b ∉ D → ∀ d ∈ D, Commute b d → d ^ 2 = 1 := by
  let C := centralizer (W : Set P)
  have hDC' : D ≤ C := (le_centralizer D).trans (centralizer_le hWD)
  let A := D.subgroupOf C
  have hAΦ : A ≤ frattini C := by
    intro d hd
    obtain ⟨y, hy, he⟩ := hDΦ hd
    have hyD : y = d := Subtype.ext he
    exact hyD ▸ hy
  have hAC : centralizer (A : Set C) ≤ A := by
    intro c hc
    apply hDC
    intro d hd
    exact congrArg Subtype.val (hc ⟨d, hDC' hd⟩ hd)
  have hcentral : ∀ d ∈ A, d ^ 2 = 1 → d ∈ center C := by
    intro d hd hd2
    have hdW : (d : P) ∈ W := by
      rw [← hDO]
      refine ⟨⟨d, hd⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val hd2
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property d hdW).symm
  intro b hb hbD d hd hbd
  by_contra hd2
  have hbC : b ∈ C := by
    intro w hw
    exact setLike_mul_comm (s := B) (hWB hw) hb
  let x : C := ⟨b, hbC⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian b hb)
  apply hbD
  have hxA : x ∈ A := by
    apply (hP.to_subgroup C).involution_mem_of_le_frattini_of_central_action
      A hAC hAΦ hcentral x hx2
    · intro c
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      apply Subtype.ext
      have hh := congrArg (fun f : MulAut D => (f ⟨((a : C) : P), a.property⟩ : P))
        (fixedPoints_conjugation_commute W D hDO hmodel c ⟨b, hbC⟩).eq
      exact hh
    · intro a ha hxa
      apply Subtype.ext
      exact hsingular b hb ⟨d, hd, hbd, hd2⟩ a ha (congrArg Subtype.val hxa)
  exact hxA

end Stellmacher.Recognition.NormalEightExoticExtension256

namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- A non-base element of the elementary sixteen fixes only square-trivial
base elements. The proof combines the Frattini identification with the finite
order-eight transitive-kernel calculation. -/
public theorem fixed_square_eq_one_of_nontrivial_elementary_action
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B]
    (hB : Nat.card B = 16) (hWB : W ≤ B)
    (_hnorm : Subgroup.normalizer (S : Set G) =
      (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G))
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : Subgroup.centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (hcard : Nat.card S = 256) :
    ∀ b ∈ B, b ∉ D → ∀ d ∈ D, Commute b d → d ^ 2 = 1 := by
  let hP : IsPGroup 2 S := S.isPGroup'
  have htransC := fixedPoints_centralizer_transitive S hZ hno W hW hunique hfused
  have hDphi : D = (frattini (centralizer (W : Set S))).map
      (centralizer (W : Set S)).subtype := by
    exact C4SquareExtension.base_eq_frattini_centralizer hP hcard hZ hno W hW
      htransC D hWD hDC hDO hmodel
  obtain ⟨e⟩ := hmodel
  let C := centralizer (W : Set S)
  let f : C →* MulAut C4SquareExtension.Model :=
    (modelAction D e).comp C.subtype
  let H : Subgroup (MulAut C4SquareExtension.Model) := f.range
  have hH : Nat.card H = 8 := by
    change Nat.card (((MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : S →* MulAut D).comp C.subtype)).range) = 8
    rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective]
    exact (restricted_conjugation_cardinals S hZ W D B hW hB hWD hWB hDC hDO
      ⟨e⟩ hcard).1
  have hfix : ∀ g ∈ H, ∀ x : C4SquareExtension.Model, x ^ 2 = 1 → g x = x := by
    rintro g ⟨c, rfl⟩ x hx
    let d := e.symm x
    have hd : d ^ 2 = 1 := by dsimp [d]; rw [← map_pow, hx, map_one]
    have hdW : (d : S) ∈ W := by
      rw [← hDO]
      exact ⟨d, subset_closure (by simpa using hd), rfl⟩
    change e (MulAut.conjNormal (H := D) (c : S) d) = x
    rw [show MulAut.conjNormal (H := D) (c : S) d = d from ?_]
    · exact e.apply_symm_apply x
    · apply Subtype.ext
      change (c : S) * (d : S) * (c : S)⁻¹ = d
      rw [← c.property _ hdW, mul_inv_cancel_right]
  have hinv : (MulEquiv.inv C4SquareExtension.Model : MulAut C4SquareExtension.Model) ∈ H := by
    have hi := ExoticTwoGroup.ActionModel.inversion_mem_of_card_sixteen
      (modelAction D e).range (card_modelAction_range D hDC e hcard)
    rcases hi with ⟨z, hz⟩
    have hinv_eq : ExoticTwoGroup.ActionModel.inversion =
        (MulEquiv.inv C4SquareExtension.Model) := by
      apply ExoticTwoGroup.ActionModel.aut_ext
      · exact ExoticTwoGroup.ActionModel.inversion_u
      · exact ExoticTwoGroup.ActionModel.inversion_v
    rw [hinv_eq] at hz
    have hzC : (z : S) ∈ C := by
      intro w hw
      have hh := congrArg (fun g : MulAut C4SquareExtension.Model =>
        g (e ⟨w, hWD hw⟩)) hz
      have hh' : e (MulAut.conjNormal (H := D) (z : S)
          ⟨w, hWD hw⟩) = (e ⟨w, hWD hw⟩)⁻¹ := by
        simpa [modelAction, MulAut.congr_apply] using hh
      have hDconj : MulAut.conjNormal (H := D) (z : S)
          ⟨w, hWD hw⟩ = (⟨w, hWD hw⟩ : D)⁻¹ := by
        apply e.injective
        simpa only [map_inv, e.symm_apply_apply] using hh'
      have hzw : (z : S) * w * (z : S)⁻¹ = w := by
        have hw2 : w ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian w hw
        have hw_inv : w⁻¹ = w := by
          calc
            w⁻¹ = w⁻¹ * 1 := by rw [mul_one]
            _ = w⁻¹ * (w * w) := by
              simpa only [pow_two] using congrArg (fun t => w⁻¹ * t) hw2.symm
            _ = w := by group
        simpa [MulAut.conjNormal_apply, hw_inv] using congrArg Subtype.val hDconj
      exact (mul_inv_eq_iff_eq_mul.mp hzw).symm
    exact ⟨⟨z, hzC⟩, by
      change (modelAction D e) z = _
      exact hz⟩
  have normalize (a : MulAut C) :
      ∃ α : MulAut C4SquareExtension.Model,
        H.map (MulAut.conj α).toMonoidHom = H ∧
        (∀ c : C, MulAut.conj α (f c) = f (a c)) ∧
        (∀ d : D, ∃ z : D, α (e d) = e z ∧
          (z : S) = (a ⟨(d : S), (le_centralizer D).trans
            (centralizer_le hWD) d.property⟩ : C)) := by
    let K := D.subgroupOf C
    have hDC' : D ≤ C := (le_centralizer D).trans (centralizer_le hWD)
    have hKmap_le : K.map (a : C →* C) ≤ K := by
      rw [map_le_iff_le_comap]
      intro d hd
      have hdphi : d ∈ frattini C := by
        have hdD : (d : S) ∈ D := by exact hd
        rw [hDphi] at hdD
        rcases hdD with ⟨z, hz, hzd⟩
        exact (Subtype.ext hzd) ▸ hz
      have hadphi := (characteristic_iff_le_comap.mp
        (inferInstance : (frattini C).Characteristic) a) hdphi
      change (a d : S) ∈ D
      rw [hDphi]
      exact ⟨a d, hadphi, rfl⟩
    have hKmap : K.map (a : C →* C) = K := by
      apply eq_of_le_of_card_ge hKmap_le
      rw [card_map_of_injective a.injective]
    let aK : MulAut K := a.subgroupMap K |>.trans (MulEquiv.subgroupCongr hKmap)
    let eD : K ≃* D := subgroupOfEquivOfLe hDC'
    let dA : MulAut D := eD.symm.trans (aK.trans eD)
    let α : MulAut C4SquareExtension.Model := (MulAut.congr e) dA
    have hdA (d : D) : (dA d : S) =
        (a ⟨(d : S), hDC' d.property⟩ : C) := by
      simp only [dA, MulEquiv.trans_apply]
      change ((aK (eD.symm d) : K) : S) =
        ((a ⟨(d : S), hDC' d.property⟩ : C) : S)
      rfl
    have hcongr (q : MulAut D) (y : C4SquareExtension.Model) :
        ((MulAut.congr e).toMonoidHom q) y = e (q (e.symm y)) := by rfl
    have hαd (d : D) : α (e d) = e (dA d) := by
      change ((MulAut.congr e).toMonoidHom dA) (e d) = _
      rw [hcongr]
      simp only [e.symm_apply_apply]
    have halpha (y : C4SquareExtension.Model) : α⁻¹ y =
        e (dA.symm (e.symm y)) := by
      change (MulAut.congr e dA)⁻¹ y = _
      rfl
    have hconj (c : C) : MulAut.conj α (f c) = f (a c) := by
      apply MulEquiv.ext
      intro x
      change (α * f c * α⁻¹) x = f (a c) x
      change α (f c (α⁻¹ x)) = f (a c) x
      rw [halpha]
      change α (((MulAut.congr e).toMonoidHom (MulAut.conjNormal (c : S)))
        (e (dA.symm (e.symm x)))) =
        ((MulAut.congr e).toMonoidHom (MulAut.conjNormal ((a c : C) : S))) x
      rw [hcongr]
      change ((MulAut.congr e).toMonoidHom dA)
          (e (MulAut.conjNormal (c : S)
            (e.symm (e (dA.symm (e.symm x)))))) =
        e (MulAut.conjNormal ((a c : C) : S) (e.symm x))
      rw [hcongr]
      simp only [e.symm_apply_apply]
      rw [e.injective.eq_iff]
      apply Subtype.ext
      rw [hdA]
      simp only [MulAut.conjNormal_apply]
      let q : C := ⟨(dA.symm (e.symm x) : S), hDC' (dA.symm (e.symm x)).property⟩
      have hq : (a q : S) = (e.symm x : S) := by
        simpa [q] using (hdA (dA.symm (e.symm x))).symm
      have hqa : (a q : C) = ⟨e.symm x, hDC' (e.symm x).property⟩ :=
        Subtype.ext hq
      have hprod : a (c * q * c⁻¹) = a c * a q * (a c)⁻¹ := by
        simp only [map_mul, map_inv]
      have hprod' := congrArg Subtype.val
        (hprod.trans (congrArg (fun z : C => a c * z * (a c)⁻¹) hqa))
      convert hprod' using 1
      · apply congrArg Subtype.val
        apply congrArg a
        apply Subtype.ext
        simp [q, mul_assoc]
      · simp [mul_assoc]
    refine ⟨α, ?_, hconj, ?_⟩
    · apply eq_of_le_of_card_ge
      · rintro z ⟨g, hg, rfl⟩
        rcases hg with ⟨c, rfl⟩
        exact ⟨a c, (hconj c).symm⟩
      · rw [card_map_of_injective (MulAut.conj α).injective]
    · intro d
      exact ⟨dA d, hαd d, hdA d⟩
  have htransH : ∀ u v : C4SquareExtension.Model, u ^ 2 = 1 → v ^ 2 = 1 →
      u ≠ 1 → v ≠ 1 →
      ∃ α : MulAut C4SquareExtension.Model,
        H.map (MulAut.conj α).toMonoidHom = H ∧ α u = v := by
    intro u v hu hv hun hvn
    have huD2 : (e.symm u : D) ^ 2 = 1 := by
      rw [← map_pow, hu, map_one]
    have hvD2 : (e.symm v : D) ^ 2 = 1 := by
      rw [← map_pow, hv, map_one]
    have huD : (e.symm u : S) ∈ W := by
      rw [← hDO]
      exact ⟨e.symm u, subset_closure (by simpa using huD2), rfl⟩
    have hvD : (e.symm v : S) ∈ W := by
      rw [← hDO]
      exact ⟨e.symm v, subset_closure (by simpa using hvD2), rfl⟩
    have huoD : orderOf (e.symm u : D) = 2 := by
      apply orderOf_eq_prime
      · exact huD2
      · intro h
        apply hun
        have h' : (e.symm u : D) = 1 := h
        simpa using congrArg e h'
    have hvoD : orderOf (e.symm v : D) = 2 := by
      apply orderOf_eq_prime
      · exact hvD2
      · intro h
        apply hvn
        have h' : (e.symm v : D) = 1 := h
        simpa using congrArg e h'
    have huo : orderOf (⟨e.symm u, le_centralizer W huD⟩ : C) = 2 := by
      simpa using huoD
    have hvo : orderOf (⟨e.symm v, le_centralizer W hvD⟩ : C) = 2 := by
      simpa using hvoD
    obtain ⟨a, ha⟩ := htransC
      ⟨e.symm u, le_centralizer W huD⟩ ⟨e.symm v, le_centralizer W hvD⟩
      huD hvD huo hvo
    obtain ⟨α, hαH, hαconj, hpoint⟩ := normalize a
    refine ⟨α, hαH, ?_⟩
    obtain ⟨z, hzu, hza⟩ := hpoint (e.symm u)
    have hzv : z = e.symm v := by
      apply Subtype.ext
      exact hza.trans (congrArg Subtype.val ha)
    rw [show u = e (e.symm u) from (e.apply_symm_apply u).symm,
      hzu, hzv, e.apply_symm_apply]
  have hsingular : ∀ b ∈ B, (∃ d ∈ D, Commute b d ∧ d ^ 2 ≠ 1) →
      ∀ d ∈ D, b * d * b⁻¹ = d⁻¹ → d ^ 2 = 1 := by
    intro b hb hboutside d hd hbd
    have hbC : (b : S) ∈ C := by
      intro w hw
      exact setLike_mul_comm (s := B) (hWB hw) hb
    have hf : f ⟨b, hbC⟩ ∈ H := ⟨⟨b, hbC⟩, rfl⟩
    rcases hboutside with ⟨d₀, hd₀, hcomm₀, hd₀ne⟩
    have hprimitive : ∃ x : C4SquareExtension.Model,
        f ⟨b, hbC⟩ x = x ∧ x ^ 2 ≠ 1 := by
      refine ⟨e ⟨d₀, hd₀⟩, ?_, ?_⟩
      · have hDcomm : MulAut.conjNormal (H := D) (b : S) ⟨d₀, hd₀⟩ = ⟨d₀, hd₀⟩ := by
          apply Subtype.ext
          change (b : S) * (d₀ : S) * (b : S)⁻¹ = d₀
          rw [hcomm₀.eq, mul_inv_cancel_right]
        simpa [f, modelAction, MulAut.congr_apply] using congrArg e hDcomm
      · intro hh
        have hd0eq : (⟨d₀, hd₀⟩ : D) ^ 2 = 1 := by
          apply e.injective
          simpa only [map_pow, map_one] using hh
        exact hd₀ne (congrArg Subtype.val hd0eq)
    have hres := C4SquareExtension.inverted_square_eq_one_of_transitive_kernel
      H hH hfix hinv htransH (f ⟨b, hbC⟩) hf hprimitive
    let x := e ⟨d, hd⟩
    have hx := hres x
    have hxd : f ⟨b, hbC⟩ x = x⁻¹ := by
      have hDinv : MulAut.conjNormal (H := D) (b : S) ⟨d, hd⟩ =
          (⟨d, hd⟩ : D)⁻¹ := by
        apply Subtype.ext
        exact hbd
      dsimp [x]
      simpa [f, modelAction, MulAut.congr_apply] using congrArg e hDinv
    have hx2 := hx hxd
    have hd2 : (⟨d, hd⟩ : D) ^ 2 = 1 := by
      apply e.injective
      simpa only [map_pow, map_one] using hx2
    exact congrArg Subtype.val hd2
  exact fixed_points_of_frattini_and_singular_action hP W D B hWD hWB hDC hDO ⟨e⟩
    (by rw [hDphi]) hsingular

end Stellmacher.Recognition.NormalEightExoticExtension256
