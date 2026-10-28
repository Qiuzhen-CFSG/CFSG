module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# Quadratic actors on a module moved by a normal subgroup of order three

Let a finite group act faithfully on a finite-dimensional binary vector space,
and let X be normal of order three with [U,X] = U. Every quadratic elementary
abelian two-subgroup A which does not centralize X has order two, and its fixed
space has exactly half the dimension of U.

For a generator f of X, the norm operator 1 + f + f² kills [U,X], hence vanishes.
Choose a in A inverting f. If b in A centralizes f, quadraticity makes the
f-invariant image of b - 1 fixed by a. The inversion relation and the norm
identity force that image to be zero. Faithfulness then makes the centralizer
of X in A trivial, so A consists of 1 and a. Finally, the image and kernel of
a - 1 coincide: a fixed vector v is the displacement of f v. Rank-nullity gives
the exact fixed codimension.

This supplies the normal-three calculation in the ordinary-A₆ branch of
Aschbacher–Smith 13.8.21(1), printed p.956, combined manuscript of 1 March 2004.
It uses the actual representation and conjugation action, independently of
any component or choice of a model for the module.
-/

public section

namespace Representation.BinaryOffender
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem add_self_zero (v : U) : v + v = 0 := by
  have h := @two_smul (ZMod 2) U _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private theorem generator_polynomial
    (σ : Representation (ZMod 2) H U) (X : Subgroup H)
    (f : H) (hgen : Subgroup.zpowers f = X) (hf3 : f ^ 3 = 1)
    (hmove : subspaceCommutator σ ⊤ X = ⊤) :
    (σ f) ^ 2 + σ f + 1 = 0 := by
  classical
  let t := σ f
  let N := t ^ 2 + t + 1
  have ht3 : t ^ 3 = 1 := by dsimp [t]; rw [← map_pow, hf3, map_one]
  have hNt : N * t = N := by
    dsimp [N]
    rw [add_mul, add_mul, one_mul, ← pow_succ, ← pow_two, ht3]
    abel
  have hNtn (n : ℕ) : N * t ^ n = N := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hNt]
  have hkill : subspaceCommutator σ ⊤ X ≤ LinearMap.ker N := by
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, w, _, rfl⟩
    rw [← hgen, mem_zpowers_iff_mem_range_orderOf] at hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
    change N (σ (f ^ n) w - w) = 0
    rw [map_sub, map_pow]
    have h := LinearMap.congr_fun (hNtn n) w
    exact sub_eq_zero.mpr h
  have htop : ∀ w, N w = 0 := by
    intro w
    exact hkill (by rw [hmove]; exact Submodule.mem_top)
  exact LinearMap.ext htop

private theorem cyclotomic_sum (t : Module.End (ZMod 2) U)
    (ht : t ^ 2 + t + 1 = 0) (v : U) : t (t v) + t v = v := by
  have h : (t (t v) + t v) + v = 0 := LinearMap.congr_fun ht v
  exact add_right_cancel (h.trans (add_self_zero v).symm)

private theorem centralizing_quadratic_operator
    (t a b : Module.End (ZMod 2) U)
    (ht : t ^ 2 + t + 1 = 0) (hat : a * t = t ^ 2 * a)
    (hbt : b * t = t * b)
    (hq : ∀ v, a (b v - v) = b v - v) : b = 1 := by
  ext v
  apply sub_eq_zero.mp
  let w := b v - v
  have haw : a w = w := hq v
  have htw : t w = b (t v) - t v := by
    dsimp [w]
    rw [map_sub]
    exact congrArg (fun z => z - t v) (LinearMap.congr_fun hbt v).symm
  have hatw : a (t w) = t w := by rw [htw]; exact hq (t v)
  have hinv : a (t w) = t (t w) := by
    have h := LinearMap.congr_fun hat w
    change a (t w) = t (t (a w)) at h
    rwa [haw] at h
  have htw2 : t (t w) = t w := hinv.symm.trans hatw
  have hw := cyclotomic_sum t ht w
  rw [htw2, add_self_zero] at hw
  exact hw.symm

private theorem inverting_involution_half_fixed [FiniteDimensional (ZMod 2) U]
    (t a : Module.End (ZMod 2) U)
    (ht : t ^ 2 + t + 1 = 0) (ha : a * a = 1)
    (hat : a * t = t ^ 2 * a) :
    2 * Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) =
      Module.finrank (ZMod 2) U := by
  let d := a - 1
  have hsurj : LinearMap.ker d ≤ LinearMap.range d := by
    intro v hv
    have hav : a v = v := sub_eq_zero.mp hv
    refine ⟨t v, ?_⟩
    change a (t v) - t v = v
    have h := LinearMap.congr_fun hat v
    change a (t v) = t (t (a v)) at h
    rw [hav] at h
    rw [h, sub_eq_add_neg,
      (eq_neg_of_add_eq_zero_left (add_self_zero (t v))).symm]
    exact cyclotomic_sum t ht v
  have hrange : LinearMap.range d = LinearMap.ker d := by
    apply le_antisymm _ hsurj
    rintro v ⟨w, rfl⟩
    change a (a w - w) - (a w - w) = 0
    have haa : a (a w) = w := LinearMap.congr_fun ha w
    rw [map_sub, haa]
    have hneg : -(a w - w) = a w - w :=
      (eq_neg_of_add_eq_zero_left (add_self_zero (a w - w))).symm
    rw [show w - a w = -(a w - w) from (neg_sub (a w) w).symm,
      hneg, sub_self]
  have hdim := LinearMap.finrank_range_add_finrank_ker d
  rw [hrange] at hdim
  dsimp only [d] at hdim
  omega

/-- A quadratic elementary actor not centralizing a normal order-three subgroup
has rank one and fixes exactly half the module, provided the representation is
faithful and the order-three subgroup generates the commutator module. -/
theorem normalThree_quadratic_rank_fixedCodim
    [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) H U) (hfaith : Function.Injective σ)
    (X : Subgroup H) (hX : X.Normal) (hcard : Nat.card X = 3)
    (hmove : subspaceCommutator σ ⊤ X = ⊤)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hnot : ¬ A ≤ Subgroup.centralizer (X : Set H)) :
    rank A = 1 ∧ 2 * fixedCodim σ A = Module.finrank (ZMod 2) U := by
  classical
  let : X.Normal := hX
  let : IsElementaryAbelian 2 A := hA.2
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨fX, hfX⟩ := exists_ne (1 : X)
  let f : H := fX
  have hfmem : f ∈ X := fX.property
  have hfne : f ≠ 1 := fun hh => hfX (Subtype.ext hh)
  obtain ⟨hgen, hf3⟩ := Subgroup.cyclicThree_generator X hcard f hfmem hfne
  have hf2 : f ^ 2 = f⁻¹ := by
    have hh := congrArg (fun z : H => z * f⁻¹) hf3
    simpa [pow_succ, mul_assoc] using hh
  have hconj (g : H) : g * f * g⁻¹ = f ∨ g * f * g⁻¹ = f⁻¹ :=
    Subgroup.cyclicThree_normalizer_conjugates X hcard f hfmem hfne g
      (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g)
  have hcentral (g : H) (hg : g * f * g⁻¹ = f) :
      g ∈ Subgroup.centralizer (X : Set H) := by
    have hgf : Commute g f := by
      change g * f = f * g
      have hh := congrArg (fun z : H => z * g) hg
      simpa [mul_assoc] using hh
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    rw [← hgen] at hx
    obtain ⟨n, rfl⟩ := hx
    exact (hgf.zpow_right n).symm.eq
  obtain ⟨a, ha, hanc⟩ := SetLike.not_le_iff_exists.mp hnot
  have hane : a ≠ 1 := by
    intro hh
    exact hanc (hh ▸ (Subgroup.centralizer (X : Set H)).one_mem)
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hainv : a * f * a⁻¹ = f⁻¹ :=
    (hconj a).resolve_left (fun hh => hanc (hcentral a hh))
  have hat : σ a * σ f = (σ f) ^ 2 * σ a := by
    rw [← map_pow, ← map_mul, ← map_mul]
    apply congrArg σ
    rw [hf2]
    have hh := congrArg (fun z : H => z * a) hainv
    simpa [mul_assoc] using hh
  have ht : (σ f) ^ 2 + σ f + 1 = 0 :=
    generator_polynomial σ X f hgen hf3 hmove
  have hkernel (b : H) (hb : b ∈ A) (hbc : b * f * b⁻¹ = f) : b = 1 := by
    have hbf : b * f = f * b := by
      have hh := congrArg (fun z : H => z * b) hbc
      simpa [mul_assoc] using hh
    have hbt : σ b * σ f = σ f * σ b := by
      rw [← map_mul, ← map_mul, hbf]
    apply hfaith
    rw [map_one]
    exact centralizing_quadratic_operator (σ f) (σ a) (σ b) ht hat hbt (hq a ha b hb)
  have htwo (b : H) (hb : b ∈ A) : b = 1 ∨ b = a := by
    rcases hconj b with hc | hi
    · exact Or.inl (hkernel b hb hc)
    · right
      have hba : (b * a) * f * (b * a)⁻¹ = f := by
        calc
          (b * a) * f * (b * a)⁻¹ = b * (a * f * a⁻¹) * b⁻¹ := by group
          _ = b * f⁻¹ * b⁻¹ := by rw [hainv]
          _ = (b * f * b⁻¹)⁻¹ := by group
          _ = f := by rw [hi, inv_inv]
      have hprod := hkernel (b * a) (A.mul_mem hb ha) hba
      have hh := congrArg (fun z : H => z * a) hprod
      have haa : a * a = 1 := by simpa only [pow_two] using ha2
      simpa [mul_assoc, haa] using hh
  have hcardA : Nat.card A = 2 := by
    apply (Nat.card_eq_two_iff' (1 : A)).mpr
    refine ⟨⟨a, ha⟩, ?_, ?_⟩
    · exact fun hh => hane (congrArg Subtype.val hh)
    · intro b hb
      apply Subtype.ext
      exact (htwo b b.property).resolve_left (fun hh => hb (Subtype.ext hh))
  have hfixed : fixedSpace σ A = LinearMap.ker (σ a - 1) := by
    ext v
    constructor
    · intro hv
      exact sub_eq_zero.mpr (hv ⟨a, ha⟩)
    · intro hv b
      have hav : σ a v = v := sub_eq_zero.mp hv
      rcases htwo b b.property with hb | hb
      · change σ (b : H) v = v
        rw [hb, map_one]
        rfl
      · change σ (b : H) v = v
        rw [hb, hav]
  have haa : σ a * σ a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
  have hhalf := inverting_involution_half_fixed (σ f) (σ a) ht haa hat
  have hcodim := fixedCodim_add_finrank σ A
  rw [hfixed] at hcodim
  refine ⟨?_, by omega⟩
  norm_num [rank, hcardA]

end Representation.BinaryOffender
