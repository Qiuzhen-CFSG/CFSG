module

public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel

/-!
# The central inversion and sign of `Q₈ ◦ C₄`

The central generator has two possible images under an automorphism.  The
nontrivial choice is represented by the explicit central inversion, while the
choice itself gives a homomorphism to `C₂`.

Source: the automorphism calculation in Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma 14.2.21, printed p.988.
-/

@[expose] public section

namespace QuaternionCyclic

/-- The underlying map of the central inversion in normal coordinates. -/
def centralInversionFun (x : Model) : Model :=
  ⟨x.quaternion * (if x.odd then z else 1), x.odd⟩

/-- The central inversion, in the normal form `q rᵇ ↦ (q zᵇ) rᵇ`. -/
def centralInversion : MulAut Model where
  toFun := centralInversionFun
  invFun := centralInversionFun
  left_inv := by
    intro x
    have h : ∀ x : Model, centralInversionFun (centralInversionFun x) = x := by decide
    exact h x
  right_inv := by
    intro x
    have h : ∀ x : Model, centralInversionFun (centralInversionFun x) = x := by decide
    exact h x
  map_mul' := by
    intro x y
    have h : ∀ x y : Model, centralInversionFun (x * y) =
        centralInversionFun x * centralInversionFun y := by decide
    exact h x y

@[simp] theorem centralInversion_apply (x : Model) :
    centralInversion x = centralInversionFun x := rfl

@[simp] theorem centralInversion_quaternion (q : QuaternionGroup 2) :
    centralInversion (quaternionEmbedding q) = quaternionEmbedding q := by
  have h : ∀ q : QuaternionGroup 2,
      centralInversion (quaternionEmbedding q) = quaternionEmbedding q := by decide
  exact h q

@[simp] theorem centralInversion_r :
    centralInversion r = r⁻¹ := by decide

@[simp] theorem centralInversion_sq : centralInversion ^ 2 = 1 := by
  have h : ∀ x : Model, (centralInversion ^ 2) x = (1 : MulAut Model) x := by decide
  apply MulEquiv.ext
  intro x
  exact h x

/-- The two generators of order four in the cyclic factor are distinct. -/
theorem r_ne_inv : r ≠ r⁻¹ := by
  intro h
  have hi : cyclicEmbedding (Multiplicative.ofAdd 1) =
      cyclicEmbedding (Multiplicative.ofAdd 3) := by
    rw [show cyclicEmbedding (Multiplicative.ofAdd 1) = r by rfl]
    rw [show cyclicEmbedding (Multiplicative.ofAdd 3) = r⁻¹ by decide]
    exact h
  have hc := cyclicEmbedding_injective hi
  have hne : Multiplicative.ofAdd (1 : ZMod 4) ≠ Multiplicative.ofAdd 3 := by decide
  exact hne hc

/-- Every automorphism sends the central generator to itself or its inverse. -/
theorem aut_r_eq_or_inv (e : MulAut Model) : e r = r ∨ e r = r⁻¹ := by
  have hr : r ∈ Subgroup.center Model := by
    rw [center_eq_cyclic]
    exact ⟨Multiplicative.ofAdd 1, rfl⟩
  have her : e r ∈ Subgroup.center Model := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← e.map_mul, ← e.map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hr x
  obtain ⟨c, hc⟩ := (center_eq_cyclic ▸ her)
  have horder : orderOf (cyclicEmbedding c) = 4 := by
    rw [hc, e.orderOf_eq, r_order]
  have hcvals : ∀ c : Multiplicative (ZMod 4),
      c = 1 ∨ c = Multiplicative.ofAdd 1 ∨ c = Multiplicative.ofAdd 2 ∨
        c = Multiplicative.ofAdd 3 := by decide
  rcases hcvals c with rfl | rfl | rfl | rfl
  · have h1 : cyclicEmbedding (1 : Multiplicative (ZMod 4)) = 1 := map_one cyclicEmbedding
    rw [h1, orderOf_one] at horder
    norm_num at horder
  · exact Or.inl (hc.symm.trans (by rfl))
  · rw [shared_involution] at horder
    have hzorder : orderOf (quaternionEmbedding z) = 2 := by
      rw [← r_sq, orderOf_pow, r_order]
      have hg : Nat.gcd 4 2 = 2 := by decide
      rw [hg]
    rw [hzorder] at horder
    norm_num at horder
  · exact Or.inr (hc.symm.trans (by decide))

/-- The central sign records whether an automorphism inverts `r`. -/
def centralSign : MulAut Model →* Multiplicative (ZMod 2) where
  toFun e := if e r = r then 1 else Multiplicative.ofAdd 1
  map_one' := by decide
  map_mul' := by
    intro e f
    rcases aut_r_eq_or_inv e with he | he <;>
      rcases aut_r_eq_or_inv f with hf | hf
    all_goals
      have hir : r⁻¹ ≠ r := r_ne_inv.symm
      have hs : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
      simp [MulAut.mul_apply, he, hf, hir, hs]

@[simp] theorem centralSign_apply (e : MulAut Model) :
    centralSign e = if e r = r then 1 else Multiplicative.ofAdd 1 := by
  change (if e r = r then 1 else Multiplicative.ofAdd 1) = _
  rfl

@[simp] theorem centralSign_eq_one_iff (e : MulAut Model) :
    centralSign e = 1 ↔ e r = r := by
  by_cases h : e r = r
  · simp [centralSign, h]
  · have hi : e r = r⁻¹ := (aut_r_eq_or_inv e).resolve_left h
    have hir : r⁻¹ ≠ r := r_ne_inv.symm
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    simp [centralSign, hi, hir, hne]

@[simp] theorem centralSign_eq_zero_iff (e : MulAut Model) :
    centralSign e = Multiplicative.ofAdd 0 ↔ e r = r := by
  change centralSign e = 1 ↔ e r = r
  exact centralSign_eq_one_iff e

@[simp] theorem centralSign_extendAutHom (e : MulAut (QuaternionGroup 2)) :
    centralSign (extendAutHom e) = 1 := by
  rw [centralSign_eq_one_iff]
  change extendAut e r = r
  simpa [r] using (extendAut_cyclic e (Multiplicative.ofAdd 1))

@[simp] theorem centralSign_centralInversion :
    centralSign centralInversion = Multiplicative.ofAdd 1 := by
  change (if centralInversion r = r then 1 else Multiplicative.ofAdd 1) = _
  rw [centralInversion_r]
  have hir : r⁻¹ ≠ r := by decide
  simp [hir]

/-- The central sign is onto, with `centralInversion` mapping to the nontrivial value. -/
theorem centralSign_surjective : Function.Surjective centralSign := by
  intro y
  have hy : y = 1 ∨ y = Multiplicative.ofAdd 1 := by
    have h : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide
    exact h y
  rcases hy with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨centralInversion, centralSign_centralInversion⟩

/-- The central inversion commutes with every quaternion automorphism extension. -/
theorem centralInversion_commute_extendAutHom (e : MulAut (QuaternionGroup 2)) :
    centralInversion * extendAutHom e = extendAutHom e * centralInversion := by
  apply MulEquiv.ext
  intro x
  cases x with
  | mk q b =>
    have hz : e z = z := by
      have h := extendAut_cyclic e (Multiplicative.ofAdd 2)
      have hq := congrArg (fun x : Model => x.quaternion) h
      change e z = z at hq
      exact hq
    apply Model.ext
    · cases b <;> simp [centralInversionFun, extendAutHom, extendAut, MulAut.mul_apply, hz]
    · rfl

end QuaternionCyclic

end
