module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Coordinates

/-!
# The scalar centralizer of the native binary M₁₂ heart

Three short words fixing one pair-supported vector have precisely its line as
common fixed space. Ten further words carry it to the coordinate basis vectors.
Every commuting endomorphism is therefore scalar, and over F₂ every commuting
linear automorphism is the identity. The fixed-space proof uses coordinate
equations; only the short permutation-word identities are finite calculations.

This supplies the centralizer step in the ambient reduction for
Aschbacher–Smith H.11.1, printed pp.392–393 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
open Sporadic.Mathieu
namespace Ambient

private def word : List Bool → Equiv.Perm (Fin 12)
  | [] => 1
  | c :: w => (if c then m12GeneratorB else m12GeneratorA) * word w

private def stab0 := word [true, true, false, true]
private def stab1 := word [false, true, true, false, true, false, true, true, false, true, false]
private def stab2 := word [false, true, false, true, true, false, true, false, true, true, false]

private theorem stabilizers_fix :
  action stab0 (Pi.single 0 1) = Pi.single 0 1 ∧
  action stab1 (Pi.single 0 1) = Pi.single 0 1 ∧
  action stab2 (Pi.single 0 1) = Pi.single 0 1 := by decide +kernel

-- Reduction of the eleven-factor permutation words needs this recursion depth.
set_option maxRecDepth 2000 in
private theorem fixed_line (v : Coordinates)
    (ha : action stab0 v = v) (hb : action stab1 v = v) (hc : action stab2 v = v) :
    v = v 0 • (Pi.single 0 1 : Coordinates) := by
  have h5 := congrFun hc 1
  change v 1 - v 5 = v 1 at h5
  have v5 : v 5 = 0 := sub_eq_self.mp h5
  have h2 := congrFun hb 2
  change v 5 - 0 = v 2 at h2
  have v2 : v 2 = 0 := by simpa only [v5, sub_zero] using h2.symm
  have h6 := congrFun ha 2
  change v 6 - 0 = v 2 at h6
  have v6 : v 6 = 0 := by simpa only [v2, sub_zero] using h6
  have h7 := congrFun ha 5
  change v 7 - 0 = v 5 at h7
  have v7 : v 7 = 0 := by simpa only [v5, sub_zero] using h7
  have h3 := congrFun hc 3
  change v 6 - v 5 = v 3 at h3
  have v3 : v 3 = 0 := by simpa only [v6, v5, sub_zero] using h3.symm
  have h9 := congrFun ha 3
  change v 9 - 0 = v 3 at h9
  have v9 : v 9 = 0 := by simpa only [v3, sub_zero] using h9
  have h4 := congrFun hc 4
  change v 7 - v 5 = v 4 at h4
  have v4 : v 4 = 0 := by simpa only [v7, v5, sub_zero] using h4.symm
  have h1 := congrFun hb 1
  change v 4 - 0 = v 1 at h1
  have v1 : v 1 = 0 := by simpa only [v4, sub_zero] using h1.symm
  have h0 := congrFun ha 0
  change -(∑ i, v i) - 0 = v 0 at h0
  have v8 : v 8 = 0 := by
    simpa [Fin.sum_univ_succ, v1, v2, v3, v4, v5, v6, v7, v9, CharTwo.neg_eq] using h0
  ext i
  fin_cases i <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9]

private theorem word_mem (w : List Bool) : word w ∈ M12 := by
  induction w with
  | nil => exact M12.one_mem
  | cons c w ih =>
    apply M12.mul_mem _ ih
    cases c
    · exact m12GeneratorA_mem
    · exact m12GeneratorB_mem

private def movers : Fin 10 → List Bool := ![[],
  [false, true, false, true, false, true, true],
  [true, true, false, true, true, false, true, true, false],
  [false, true, false, true, true],
  [true, false, true, false, true, true, false, true, true],
  [true],
  [false, true, true],
  [true, true, false],
  [false, true, false, true, false, true, false, true, true],
  [false, true, false, true, false, true, false, true, false, true, true]]

private theorem movers_action : ∀ i : Fin 10,
    action (word (movers i)) (Pi.single 0 1) = Pi.single i 1 := by decide +kernel

private theorem coordinate_commuting_scalar (f : Coordinates →ₗ[ZMod 2] Coordinates)
    (hf : ∀ (g : M12) (v : Coordinates),
      f (coordinateRepresentation g v) = coordinateRepresentation g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  have hw (w : List Bool) (v : Coordinates) :
      f (action (word w) v) = action (word w) (f v) :=
    hf ⟨word w, word_mem w⟩ v
  have hc := fixed_line (f (Pi.single 0 1))
    (by unfold stab0; rw [← hw]; exact congrArg f stabilizers_fix.1)
    (by unfold stab1; rw [← hw]; exact congrArg f stabilizers_fix.2.1)
    (by unfold stab2; rw [← hw]; exact congrArg f stabilizers_fix.2.2)
  let c := f (Pi.single 0 1) 0
  have hb (i : Fin 10) : f (Pi.single i 1) = c • Pi.single i 1 := by
    rw [← movers_action i, hw, hc]
    exact (action (word (movers i))).map_smul _ _
  have he : f = c • LinearMap.id := by
    apply LinearMap.pi_ext
    intro i x
    have hx : (Pi.single i x : Coordinates) = x • Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    rw [hx, map_smul, hb]
    simp [smul_smul]
  refine ⟨c, fun v => ?_⟩
  rw [he]
  rfl

/-- Every endomorphism commuting with the native action is a binary scalar. -/
theorem heart_commuting_scalar (f : M12Heart →ₗ[ZMod 2] M12Heart)
    (hf : ∀ (g : M12) (v : M12Heart),
      f (m12HeartRepresentation g v) = m12HeartRepresentation g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let q := heartEquiv.symm.toLinearMap.comp (f.comp heartEquiv.toLinearMap)
  have hq (g : M12) (v : Coordinates) :
      q (coordinateRepresentation g v) = coordinateRepresentation g (q v) := by
    apply heartEquiv.injective
    change heartEquiv (heartEquiv.symm (f (heartEquiv (action g.val v)))) =
      heartEquiv (action g.val (q v))
    rw [LinearEquiv.apply_symm_apply, heartEquiv_action, heartEquiv_action]
    change f (m12HeartRepresentation g (heartEquiv v)) =
      m12HeartRepresentation g (heartEquiv (heartEquiv.symm (f (heartEquiv v))))
    rw [LinearEquiv.apply_symm_apply]
    exact hf g _
  obtain ⟨c, hc⟩ := coordinate_commuting_scalar q hq
  refine ⟨c, fun v => ?_⟩
  obtain ⟨u, rfl⟩ := heartEquiv.surjective v
  have he := congrArg heartEquiv (hc u)
  simpa only [q, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_smul] using he

/-- The centralizer of native M₁₂ in the linear automorphism group is trivial. -/
theorem heart_centralizer (e : M12Heart ≃ₗ[ZMod 2] M12Heart)
    (he : ∀ (g : M12) (v : M12Heart),
      e (m12HeartRepresentation g v) = m12HeartRepresentation g (e v)) :
    e = LinearEquiv.refl _ _ := by
  obtain ⟨c, hc⟩ := heart_commuting_scalar e.toLinearMap he
  have hc2 : c = 0 ∨ c = 1 := (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide +kernel) c
  rcases hc2 with rfl | rfl
  · have hzero : ∀ v : M12Heart, v = 0 := by
      intro v
      apply e.injective
      simpa only [zero_smul, LinearEquiv.coe_coe, map_zero] using hc v
    have hbad := congrArg heartEquiv.symm (hzero (heartEquiv (Pi.single 0 1)))
    simp at hbad
  · apply LinearEquiv.ext
    intro v
    simpa only [one_smul, LinearEquiv.coe_coe, LinearEquiv.refl_apply] using hc v

/-- Two linear automorphisms implementing the same native M₁₂ automorphism
coincide. This also makes an extending representation unique. -/
theorem heart_intertwiner_unique (a : MulAut M12)
    (e f : M12Heart ≃ₗ[ZMod 2] M12Heart)
    (he : ∀ (g : M12) (v : M12Heart),
      e (m12HeartRepresentation g v) = m12HeartRepresentation (a g) (e v))
    (hf : ∀ (g : M12) (v : M12Heart),
      f (m12HeartRepresentation g v) = m12HeartRepresentation (a g) (f v)) :
    e = f := by
  have hd : e.trans f.symm = LinearEquiv.refl _ _ := heart_centralizer _ (by
    intro g v
    apply f.injective
    change f (f.symm (e (m12HeartRepresentation g v))) =
      f (m12HeartRepresentation g (f.symm (e v)))
    rw [LinearEquiv.apply_symm_apply, he, hf, LinearEquiv.apply_symm_apply])
  apply LinearEquiv.ext
  intro v
  apply f.symm.injective
  have hv := congrArg (fun u : M12Heart ≃ₗ[ZMod 2] M12Heart => u v) hd
  simpa only [LinearEquiv.trans_apply, LinearEquiv.refl_apply,
    LinearEquiv.symm_apply_apply] using hv

end Ambient
end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
