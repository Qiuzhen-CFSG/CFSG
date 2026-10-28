module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.BinaryCubic

/-!
# The upper-layer collapse in 12.8.8(5)

Over F₂ the actual local residual fixes the marked point. Its action on the
upper image of W is therefore trivial, by the marked natural coordinates.
The homogeneous cubic norm on U/V₁ forces this image to vanish. Since the
whole upper layer consists of the same number of natural copies, its
multiplicity is zero and S₃=S.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
12.8.8(5), printed pp.851–852, PDF pp.868–869.
-/

@[expose] public section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors

variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g h : G}
  (d : Hypothesis D (ZMod 2) 1 g h)

/-- The original point subgroup, with its actual line coordinates. -/
def pointEquiv : D.V₁ ≃ d.point where
  toFun v := ⟨(d.coordinates ⟨v, d.setup.point_le v.property⟩).toAdd,
    (d.point_mem _).mp v.property⟩
  invFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val),
    (d.point_mem _).mpr (by
      rw [d.coordinates.apply_symm_apply]
      exact v.property)⟩
  left_inv v := by
    apply Subtype.ext
    change ((d.coordinates.symm (d.coordinates ⟨v, d.setup.point_le v.property⟩) : D.V) : G) = v
    exact congrArg (fun w : D.V => (w : G))
      (d.coordinates.symm_apply_apply ⟨v, d.setup.point_le v.property⟩)
  right_inv v := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (d.coordinates.apply_symm_apply _)

include d

theorem binary_local_centralizes_point : D.L₁ ≤ centralizer (D.V₁ : Set G) := by
  have hcard : Nat.card D.V₁ = 2 := by
    rw [Nat.card_congr (pointEquiv d), Module.natCard_eq_pow_finrank (K := ZMod 2),
      d.point_dimension, pow_one]
    simpa only [Nat.card_eq_fintype_card] using ZMod.card 2
  obtain ⟨z, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp hcard
  intro x hx v hv
  let a := D.V₁.normalizerMonoidHom
    ⟨x, (local_le_pointNormalizer (D := D) hx).2⟩
  have hfix (v : D.V₁) : a v = v := by
    by_cases he : v = 1
    · simp [he]
    have ha : a v ≠ 1 := fun h => he (a.injective (h.trans a.map_one.symm))
    exact (huniq (a v) ha).trans (huniq v he).symm
  have he : x * v * x⁻¹ = v := congrArg Subtype.val (hfix ⟨v, hv⟩)
  have hm := congrArg (· * x) he
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm

/-- The marked natural action fixes every vector of the binary point. -/
theorem binary_model_fixes_point (x : D.L₁) (v : Fin 3 → ZMod 2) (hv : v ∈ d.point) :
    (d.model (starProjection D ⟨x, (local_le_pointNormalizer (D := D) x.property).1⟩)).val
      *ᵥ v = v := by
  let l : D.L := ⟨x, (local_le_pointNormalizer (D := D) x.property).1⟩
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv)
  have hc := binary_local_centralizes_point d x.property w hw
  have he : (l : G) * w * (l : G)⁻¹ = w := by
    change (x : G) * w * (x : G)⁻¹ = w
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hcoord := d.equivariant l w
  have he' : (⟨(l : G) * w * (l : G)⁻¹, he.symm ▸ w.property⟩ : D.V) = w :=
    Subtype.ext he
  rw [he'] at hcoord
  simpa [w] using hcoord.symm

variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]

/-- Homogeneity for the actual cubic kills the upper marked image and hence
the entire natural layer. Earlier Section 12.8 inputs remain explicit. -/
theorem binary_upper_collapse (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    {r s : ℕ} (c : MarkedLayers d hLI r s)
    (x : D.L₁) {t : ℕ} (b : CubicSpanCoordinates d x t) :
    r = 0 ∧ S₃ D g h = S D g h := by
  have hxU : (x : G) ∈ normalizer (D.U : Set G) :=
    le_normalizer_conjugateSpanBy D.V D.H (d.setup.local_le (mem_sup_left x.property))
  let l : D.L := ⟨x, (local_le_pointNormalizer (D := D) x.property).1⟩
  have hxS : (x : G) ∈ normalizer (S D g h : Set G) :=
    I_normalizes_core D g h (hLI l.property)
  have hxW : (x : G) ∈ normalizer (W D g h : Set G) := by
    apply mem_normalizer_iff.mpr
    intro w
    exact and_congr (mem_normalizer_iff.mp hxU w) (mem_normalizer_iff.mp hxS w)
  let a := (W D g h).normalizerMonoidHom ⟨x, hxW⟩
  let q : W D g h →* UpperQuotient D g h :=
    (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))).comp (inclusion inf_le_right)
  have hfix (w : W D g h) : q (a w) = q w := by
    apply c.upper.injective
    apply Multiplicative.toAdd.injective
    funext i
    have hmark : c.upper (q w) ∈ lineCopies d.point r := by
      rw [← c.upper_mark]
      exact mem_map_of_mem c.upper.toMonoidHom
        (mem_map.mpr ⟨⟨w, w.property.2⟩, w.property, rfl⟩)
    exact (c.upper_equivariant l ⟨w, w.property.2⟩ i).trans
      (binary_model_fixes_point d x _ (hmark i))
  have hkill (w : W D g h) : q w = 1 := by
    have hnorm : ((w * a w * a (a w) : W D g h) : G) ∈ D.V₁ :=
      b.norm_mem_point ⟨w, w.property.1⟩
    have hV₁S₃ : D.V₁ ≤ S₃ D g h :=
      d.setup.point_le.trans ((d.series_inclusions hUT hf hLI).1.trans
        (d.series_inclusions hUT hf hLI).2.1)
    have hn : q (w * a w * a (a w)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hV₁S₃ hnorm)
    rw [map_mul, map_mul, hfix, hfix, hfix] at hn
    have hsquare : q w * q w = 1 := by
      apply c.upper.injective
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i j
      change (c.upper (q w)).toAdd i j + (c.upper (q w)).toAdd i j = 0
      ring_nf
      simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero]
    rwa [hsquare, one_mul] at hn
  have himage : upperImage D g h (W D g h) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact hkill ⟨w, hw⟩
  have hr : 2 ^ r = 2 ^ 0 := by
    simpa [himage] using c.card_upperImage.symm
  have hr0 : r = 0 := Nat.pow_right_injective (by decide : 2 ≤ 2) hr
  refine ⟨hr0, le_antisymm (d.series_inclusions hUT hf hLI).2.2 ?_⟩
  intro w hw
  have he : c.upper (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) ⟨w, hw⟩) = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (Nat.not_lt_zero i.val (hr0 ▸ i.isLt)).elim
  exact (QuotientGroup.eq_one_iff (⟨w, hw⟩ : S D g h)).mp
    (c.upper.injective (he.trans c.upper.map_one.symm))

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
