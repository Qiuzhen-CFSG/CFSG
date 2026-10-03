module

public import Stellmacher.Recognition.Parrott.NormalizerInvolutionOrbitBound

/-!
# Eight distinct images under normalizer involutions

Conjugating the supplied reflection by x and a preserves its square and
keeps it outside K in T₂ = ⟨s₀,K⟩. Both x and a centralize y. On wF,
a multiplies by z, while x² multiplies by v or vt. Neither of the latter
lies in ⟨z⟩, and x fixes z. Thus the four x-images and their z-twists
are eight distinct involution images, retaining the supplied frame.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.681, “Generators and relations for N”. This is a direct lower
census inside T₂ using equations (1), (2), (4), (6), and (16).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem inv_of_sq {g : G} (h : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
private theorem tail {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]
private theorem conj_of_commute {p q : G} (h : Commute p q) :
    (MulAut.conj p⁻¹) q = q := by
  change p⁻¹ * q * p⁻¹⁻¹ = q
  rw [h.inv_left.eq, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

private theorem elementary_y_action (f : ParrottSylowGeneratorData n) (g : G) (hg : g ∈ e.F) :
    (MulAut.conj f.y⁻¹) g = g ∨ (MulAut.conj f.y⁻¹) g = g * n.t := by
  let _ := e.elementary
  have hct (g : G) (hg : g ∈ e.F) : Commute n.t g :=
    congrArg e.F.subtype (mul_comm (⟨n.t, n.t_mem_inf.2⟩ : e.F) ⟨g, hg⟩)
  have hyt : Commute f.y n.t := by
    have hxt := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt
    have hh := hxt.pow_left 2
    rw [f.eq04] at hh
    have hzt := f.comm_zt
    change f.y * n.t = n.t * f.y
    have he := hh.eq
    simp only [mul_assoc, hzt.eq] at he
    exact mul_right_cancel (by simpa only [mul_assoc] using he)
  rw [← f.elementary_basis] at hg
  induction hg using closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (conj_of_commute f.comm_zy.symm)
    · exact Or.inl (conj_of_commute hyt)
    · exact Or.inl f.y_conjugation.1
    · exact Or.inr f.y_conjugation.2.1
    · exact Or.inl (conj_of_commute ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq06_ya))
  | one => exact Or.inl (map_one _)
  | mul g k hg hk ihg ihk =>
    have htk := hct k (f.elementary_basis ▸ hk)
    rw [map_mul]
    rcases ihg with hg' | hg' <;> rcases ihk with hk' | hk'
    · exact Or.inl (by rw [hg', hk'])
    · exact Or.inr (by rw [hg', hk', mul_assoc])
    · exact Or.inr (by rw [hg', hk']; simp only [mul_assoc, htk.eq])
    · exact Or.inl (by rw [hg', hk']; simp only [mul_assoc, tail htk.eq, ← pow_two, f.t_sq, mul_one])
  | inv g hg ih =>
    have hi : g⁻¹ = g := inv_of_sq (elemPow_eq_one_of_isElementaryAbelian g
      (show g ∈ e.F from f.elementary_basis ▸ hg))
    simpa only [hi] using ih

private theorem coset_y_action (f : ParrottSylowGeneratorData n) (g : G)
    (hg : f.w⁻¹ * g ∈ e.F) :
    (MulAut.conj f.y⁻¹) g = g * n.v ∨
    (MulAut.conj f.y⁻¹) g = g * (n.v * n.t) := by
  let b := f.w⁻¹ * g
  have hgb : g = f.w * b := by simp [b]
  have hbF : b ∈ e.F := hg
  let _ := e.elementary
  have hvb : Commute n.v b :=
    congrArg e.F.subtype (mul_comm (⟨n.v, n.v_mem_inf.2⟩ : e.F) ⟨b, hbF⟩)
  rw [hgb, map_mul, f.y_conjugation.2.2]
  rcases elementary_y_action f b hbF with hh | hh
  · exact Or.inl (by rw [hh]; simp only [mul_assoc, hvb.eq])
  · exact Or.inr (by rw [hh]; simp only [mul_assoc, tail hvb.eq])

private theorem coset_x_square_action (f : ParrottSylowGeneratorData n) (g : G)
    (hg : f.w⁻¹ * g ∈ e.F) :
    (MulAut.conj f.x⁻¹) ((MulAut.conj f.x⁻¹) g) = g * n.v ∨
    (MulAut.conj f.x⁻¹) ((MulAut.conj f.x⁻¹) g) = g * (n.v * n.t) := by
  have hzg : Commute z g := by
    let _ := e.elementary
    have hzb : Commute z (f.w⁻¹ * g) :=
      congrArg e.F.subtype (mul_comm (⟨z, e.z_mem_inf.2⟩ : e.F) ⟨_, hg⟩)
    simpa using f.comm_zw.mul_right hzb
  have haction : (MulAut.conj f.x⁻¹) ((MulAut.conj f.x⁻¹) g) =
      (MulAut.conj f.y⁻¹) g := by
    have he : f.x⁻¹ * (f.x⁻¹ * g * f.x) * f.x = (f.x ^ 2)⁻¹ * g * (f.x ^ 2) := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    simp only [MulAut.conj_apply, inv_inv]
    rw [he, f.eq04, mul_inv_rev]
    have hzy := f.comm_zy.inv_left.inv_right.eq
    simp only [mul_assoc, tail hzy, tail hzg.inv_left.eq, tail f.comm_zy.inv_left.eq,
      inv_mul_cancel, mul_one]
  rw [haction]
  exact coset_y_action f g hg

private theorem coset_a_action (f : ParrottSylowGeneratorData n) (g : G)
    (hg : f.w⁻¹ * g ∈ e.F) : (MulAut.conj f.a⁻¹) g = g * z := by
  have haF : f.a ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  let _ := e.elementary
  have hab : Commute f.a (f.w⁻¹ * g) :=
    congrArg e.F.subtype (mul_comm (⟨f.a, haF⟩ : e.F) ⟨_, hg⟩)
  have hwa : (MulAut.conj f.a⁻¹) f.w = f.w * z := by
    have hh := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw
    change f.a⁻¹ * f.w * f.a⁻¹⁻¹ = f.w * z
    rw [inv_inv]
    calc
      _ = f.a⁻¹ * (f.a * f.w) * z⁻¹ := by rw [hh]; group
      _ = _ := by rw [inv_of_sq f.z_sq]; group
  have hzb : Commute z (f.w⁻¹ * g) :=
    congrArg e.F.subtype (mul_comm (⟨z, e.z_mem_inf.2⟩ : e.F) ⟨_, hg⟩)
  calc
    _ = (MulAut.conj f.a⁻¹) (f.w * (f.w⁻¹ * g)) := by simp
    _ = (f.w * z) * (f.w⁻¹ * g) := by rw [map_mul, hwa, conj_of_commute hab]
    _ = g * z := by rw [mul_assoc, hzb.eq]; group

private theorem eight_rotation (φ : MulAut G) (z g : G)
    (hz : z ^ 2 = 1) (hz1 : z ≠ 1) (hφz : φ z = z)
    (hfour : φ (φ (φ (φ g))) = g)
    (htwo : φ (φ g) ≠ g) (htwoz : φ (φ g) ≠ g * z) :
    Function.Injective (fun p : Fin 4 × Bool =>
      (φ ^ p.1.val) g * if p.2 then z else 1) := by
  have hzz : z * z = 1 := by simpa only [pow_two] using hz
  have hsq (x : G) : x * z * z = x := by rw [mul_assoc, hzz, mul_one]
  have hne : φ g ≠ g := by
    intro hh
    exact htwo (by rw [hh, hh])
  have hnez : φ g ≠ g * z := by
    intro hh
    exact htwo (by rw [hh, map_mul, hφz, hh, hsq])
  have hthree : φ (φ (φ g)) ≠ g := by
    intro hh
    have hlast := congrArg φ hh
    rw [hfour] at hlast
    exact hne hlast.symm
  have hthreez : φ (φ (φ g)) ≠ g * z := by
    intro hh
    have hlast := congrArg φ hh
    rw [hfour, map_mul, hφz] at hlast
    exact hnez (calc
      φ g = (φ g * z) * z := (hsq _).symm
      _ = g * z := congrArg (fun x => x * z) hlast.symm)
  have hback (x y : G) (hh : φ x = φ y * z) : x = y * z := by
    apply φ.injective
    rwa [map_mul, hφz]
  have hzright (x y : G) (hh : x * z = y) : x = y * z := by
    rw [← hh, hsq]
  have h00 (x : G) : x ≠ x * z := by
    intro hh
    have he : (1 : G) = z := mul_left_cancel (by simpa only [mul_one] using hh)
    exact hz1 he.symm
  have hsep (i j : Fin 4) (hij : i ≠ j) :
      (φ ^ i.val) g ≠ (φ ^ j.val) g ∧
      (φ ^ i.val) g ≠ (φ ^ j.val) g * z := by
    fin_cases i <;> fin_cases j <;>
      simp only [pow_zero,
        MulAut.one_apply, pow_succ, MulAut.mul_apply]
    all_goals first | exact (hij rfl).elim | skip
    all_goals constructor
    all_goals intro hh
    all_goals first
      | exact hne hh
      | exact hne hh.symm
      | exact hnez hh
      | exact hnez (hzright _ _ hh.symm)
      | exact htwo hh
      | exact htwo hh.symm
      | exact htwoz hh
      | exact htwoz (hzright _ _ hh.symm)
      | exact hthree hh
      | exact hthree hh.symm
      | exact hthreez hh
      | exact hthreez (hzright _ _ hh.symm)
      | exact hne (φ.injective hh)
      | exact hne (φ.injective hh.symm)
      | exact hnez (hback _ _ hh)
      | exact hnez (hback _ _ (hzright _ _ hh.symm))
      | exact htwo (φ.injective hh)
      | exact htwo (φ.injective hh.symm)
      | exact htwoz (hback _ _ hh)
      | exact htwoz (hback _ _ (hzright _ _ hh.symm))
      | exact hne (φ.injective (φ.injective hh))
      | exact hne (φ.injective (φ.injective hh.symm))
      | exact hnez (hback _ _ (hback _ _ hh))
      | exact hnez (hback _ _ (hback _ _ (hzright _ _ hh.symm)))
  rintro ⟨i, b⟩ ⟨j, c⟩ heq
  have hij : i = j := by
    by_contra hh
    obtain ⟨hne, hnez⟩ := hsep i j hh
    cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at heq
    · exact hne heq
    · exact hnez heq
    · exact hnez (hzright _ _ heq)
    · exact hne (mul_right_cancel heq)
  subst j
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · exact (h00 ((φ ^ i.val) g) (by simpa using heq)).elim
    · exact (h00 ((φ ^ i.val) g) (by simpa using heq.symm)).elim
    · rfl
  subst c
  rfl


private theorem images_conj
    (f : ParrottCentralizerGeneratorData n) (s₀ k g : G)
    (hk : k ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype)
    (hky : Commute k f.y) (hg : g ∈ f.secondSylowInvolutionImages s₀)
    (hcos : f.w⁻¹ * (MulAut.conj k⁻¹) g ∈ e.F) :
    (MulAut.conj k⁻¹) g ∈ f.secondSylowInvolutionImages s₀ := by
  let X := (pCore 2 (normalizer (e.F : Set G))).map
    (normalizer (e.F : Set G)).subtype
  let T₂ := X ⊔ zpowers s₀
  let φ := MulAut.conj k⁻¹
  obtain ⟨_, s, hsT, hsX, hs2, hsg⟩ := hg
  have hkT : k ∈ T₂ := mem_sup_left hk
  have hs'T : φ s ∈ T₂ := by
    simpa only [φ, MulAut.conj_apply, inv_inv] using
      T₂.mul_mem (T₂.mul_mem (T₂.inv_mem hkT) hsT) hkT
  have hs'X : φ s ∉ X := by
    intro hh
    have hh' := X.mul_mem (X.mul_mem hk hh) (X.inv_mem hk)
    apply hsX
    simpa only [φ, MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one] using hh'
  have hφy : φ f.y = f.y := conj_of_commute hky
  refine ⟨hcos, φ s, hs'T, hs'X, ?_, ?_⟩
  · rw [← map_pow, hs2, map_one]
  · rw [← hφy, ← map_inv, ← map_mul, ← map_mul, hsg]

private theorem coset_x_mem (f : ParrottSylowGeneratorData n) (g : G)
    (hg : f.w⁻¹ * g ∈ e.F) : f.w⁻¹ * (MulAut.conj f.x⁻¹) g ∈ e.F := by
  have hxN : f.x ∈ normalizer (e.F : Set G) :=
    map_subtype_le _ f.x_mem_normalizer_core
  have hbF : (MulAut.conj f.x⁻¹) (f.w⁻¹ * g) ∈ e.F := by
    simpa only [MulAut.conj_apply, inv_inv] using
      (mem_normalizer_iff''.mp hxN (f.w⁻¹ * g)).mp hg
  have huF : f.u ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have hwx : (MulAut.conj f.x⁻¹) f.w = f.w * f.u := by
    have hh := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq01_xw
    change f.x⁻¹ * f.w * f.x⁻¹⁻¹ = f.w * f.u
    rw [inv_inv]
    calc
      _ = f.x⁻¹ * (f.x * f.w) * f.u⁻¹ := by rw [hh]; group
      _ = _ := by rw [inv_of_sq f.u_sq]; group
  have he : (MulAut.conj f.x⁻¹) g =
      (f.w * f.u) * (MulAut.conj f.x⁻¹) (f.w⁻¹ * g) := by
    rw [← hwx, ← map_mul, mul_inv_cancel_left]
  rw [he]
  simpa only [mul_assoc, inv_mul_cancel_left] using e.F.mul_mem huF hbF

/-- The supplied reflection yields at least eight distinct images in wF.
The transporters are its conjugates by powers of x and by a, all in
the literal subgroup generated by the core and the supplied reflection. -/
public theorem ParrottCentralizerGeneratorData.secondSylowInvolutionImages_ncard_ge_eight
    [Finite G] (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) (s₀ : G)
    (hs₀T : s₀ ∉ (e.sylow : Subgroup G)) (hs₀ : s₀ ^ 2 = 1)
    (hcos : f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F) :
    8 ≤ (f.secondSylowInvolutionImages s₀).ncard := by
  classical
  let φ := MulAut.conj f.x⁻¹
  let g := s₀⁻¹ * f.y * s₀
  let S := f.secondSylowInvolutionImages s₀
  have hg : g ∈ S := ⟨hcos, s₀, mem_sup_right (mem_zpowers s₀),
    fun hh => hs₀T (n.core_le_sylow hh), hs₀, rfl⟩
  have hxy : Commute f.x f.y := by
    have hy : f.y = f.x ^ 2 * z⁻¹ := by rw [f.eq04]; group
    rw [hy]
    exact ((Commute.refl f.x).pow_right 2).mul_right f.comm_zx.symm.inv_right
  have hφ (v : G) (hv : v ∈ S) : φ v ∈ S :=
    images_conj f s₀ f.x v f.toParrottSylowGeneratorData.x_mem_normalizer_core hxy hv
      (coset_x_mem f.toParrottSylowGeneratorData v hv.1)
  have haF : f.a ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have htwist (v : G) (hv : v ∈ S) : v * z ∈ S := by
    have he := coset_a_action f.toParrottSylowGeneratorData v hv.1
    have haX := n.omega_le_core (n.elementary_le_omega haF)
    have hay := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq06_ya).symm
    have hc : f.w⁻¹ * (MulAut.conj f.a⁻¹) v ∈ e.F := by
      rw [he, ← mul_assoc]
      exact e.F.mul_mem hv.1 e.z_mem_inf.2
    exact he ▸ images_conj f s₀ f.a v haX hay hv hc
  have hφz : φ z = z := conj_of_commute f.comm_zx.symm
  have hfour : φ (φ (φ (φ g))) = g := by
    have he : φ (φ (φ (φ g))) = (f.x ^ 4)⁻¹ * g * (f.x ^ 4) := by
      simp only [φ, MulAut.conj_apply, inv_inv, show (4 : ℕ) = 2 + 2 from rfl,
        pow_add, pow_two, mul_inv_rev, mul_assoc]
    rw [he, f.eq01_x]
    simp
  let Z := zpowers z ⊔ zpowers n.t
  have hvZ : n.v ∉ Z := by
    intro hh
    exact n.v_not_mem_core_center (n.core_center_eq.symm ▸ hh)
  have hzZ : z ∈ Z := mem_sup_left (mem_zpowers z)
  have htZ : n.t ∈ Z := mem_sup_right (mem_zpowers n.t)
  have hvtZ : n.v * n.t ∉ Z := fun hh => hvZ ((Z.mul_mem_cancel_right htZ).mp hh)
  have hne (b : G) (hb : b ∉ Z) : g * b ≠ g ∧ g * b ≠ g * z := by
    constructor
    · intro hh
      have hb1 : b = 1 := mul_left_cancel (hh.trans (mul_one g).symm)
      exact hb (hb1 ▸ Z.one_mem)
    · intro hh
      exact hb (mul_left_cancel hh ▸ hzZ)
  have htwo : φ (φ g) ≠ g ∧ φ (φ g) ≠ g * z := by
    rcases coset_x_square_action f.toParrottSylowGeneratorData g hcos with hh | hh
    · change φ (φ g) = g * n.v at hh
      rw [hh]
      exact hne n.v hvZ
    · change φ (φ g) = g * (n.v * n.t) at hh
      rw [hh]
      exact hne _ hvtZ
  have hz1 : z ≠ 1 := by
    intro hh
    have ho := h.involution
    simp [hh] at ho
  have hinj := eight_rotation φ z g f.z_sq hz1 hφz hfour htwo.1 htwo.2
  have hp (i : ℕ) : (φ ^ i) g ∈ S := by
    induction i with
    | zero => simpa using hg
    | succ i ih =>
      simpa only [pow_succ', MulAut.mul_apply] using hφ _ ih
  let inject : Fin 4 × Bool → S := fun p =>
    ⟨(φ ^ p.1.val) g * if p.2 then z else 1, by
      cases hb : p.2
      · simpa only [hb, Bool.false_eq_true, ↓reduceIte, mul_one] using hp p.1.val
      · simpa only [hb, ↓reduceIte] using htwist _ (hp p.1.val)⟩
  have hinject : Function.Injective inject := fun p q hpq =>
    hinj (congrArg Subtype.val hpq)
  have hc := Nat.card_le_card_of_injective inject hinject
  have hBool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  simpa only [Nat.card_prod, Nat.card_fin, hBool, Nat.card_coe_set_eq,
    show 4 * 2 = (8 : ℕ) from rfl] using hc

end Stellmacher.Recognition
