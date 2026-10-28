module

public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupTheory.PGroup.HomocyclicDeepInvolution
public import Theory.GroupTheory.PGroup.NormalEightFour

/-!
# The four-torsion kernel: counterexample and valid reductions

The proposed assertion that the whole four-torsion kernel equals `D` is false.
An explicit group of order 1024 with `D ≃ C₈ × C₈` and kernel of order 128 is
constructed and verified mathematically in
`docs/homocyclic-four-torsion-counterexample.md`. The independent exact GAP
certificate is `scripts/check_homocyclic_four_torsion_counterexample.g`.
That counterexample is not a Lean construction. Its centralizer of `W` does
have a characteristic involution, so the stronger kernel route alone fails.
The Lean theorems below establish the valid involution and section reductions.

Let `D` be a normal abelian self-centralizing subgroup of a finite two-group,
homocyclic of rank two and exponent at least eight. Suppose its omega four
`W` is normal, central omega has order two, and the ambient group has no
normal elementary eight. Every involution fixing four-torsion in `D`
belongs to `D`.

The deep-involution calculation makes its action commute with the image of
`C(W)`. Pairing the involution with a conjugate from the other coset of
`C(W)` gives an action central in the whole ambient image. A square root
in `D` corrects this product to an involution. The normal-eight obstruction
then kills the product action and hence the original action. All normality
arguments take place in the original group, not just in `C(W)`.

A nontrivial four-torsion kernel modulo `D` therefore supplies a normal
index-two extension of `D` with no new involutions. The last theorem exports
this reduction. It does not assert that arbitrary elements fixing
four-torsion belong to `D`: the counterexample realizes such an extension.

Source context: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386,
and the final paragraph of p.395, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The reductions here are proved directly, without assuming the classification
cited in those passages.
-/

open Subgroup

namespace IsPGroup

/-- A central involution action whose inverted elements have square one
cannot enlarge a normal omega four without producing a normal elementary eight. -/
public theorem involution_mem_of_normal_four_central_action
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (x : P) (hx : x ^ 2 = 1) (hxC : x ∈ centralizer (W : Set P))
    (hcomm : ∀ g : P, Commute (MulAut.conjNormal (H := D) g)
      (MulAut.conjNormal (H := D) x))
    (hinv : ∀ d ∈ D, x * d * x⁻¹ = d⁻¹ → d ^ 2 = 1) : x ∈ D := by
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  have hCW : zpowers x ≤ centralizer (W : Set P) := zpowers_le.mpr hxC
  let U := W ⊔ zpowers x
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.sup_of_le_centralizer hCW
  have hdiff (g : P) : g * x * g⁻¹ * x⁻¹ ∈ W := by
    let d := g * x * g⁻¹ * x⁻¹
    let f : P →* MulAut D := MulAut.conjNormal
    have hker : f d = 1 := by
      dsimp [d, f]
      simp only [map_mul, map_inv]
      rw [(hcomm g).eq]
      group
    have hd : d ∈ D := by
      apply hDC
      intro a ha
      have hh := congrArg (fun t : MulAut D => (t ⟨a, ha⟩ : P)) hker
      change d * a * d⁻¹ = a at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hde : (d * x) ^ 2 = 1 := by
      change (g * x * g⁻¹ * x⁻¹ * x) ^ 2 = 1
      rw [inv_mul_cancel_right, ← MulAut.conj_apply, ← map_pow, hx, map_one]
    have hdi : x * d * x⁻¹ = d⁻¹ := by
      have hprod : d * (x * d * x⁻¹) = 1 := by
        calc
          d * (x * d * x⁻¹) = (d * x) ^ 2 * (x ^ 2)⁻¹ := by
            simp only [pow_two]; group
          _ = 1 := by rw [hde, hx]; simp
      exact eq_inv_of_mul_eq_one_right hprod
    rw [← hO]
    refine ⟨⟨d, hd⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    simpa using hinv d hd hdi
  let : U.Normal := by
    constructor
    intro y hy g
    have hmap : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      rw [show U = W ⊔ zpowers x from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · rintro _ ⟨w, hw, rfl⟩
        exact (le_sup_left : W ≤ U) ((inferInstance : W.Normal).conj_mem w hw g)
      · apply zpowers_le.mpr
        have hh : MulAut.conj g x = (g * x * g⁻¹ * x⁻¹) * x := by
          simp [MulAut.conj_apply]
        change MulAut.conj g x ∈ U
        rw [hh]
        exact U.mul_mem ((le_sup_left : W ≤ U) (hdiff g))
          ((le_sup_right : zpowers x ≤ U) (mem_zpowers x))
    exact hmap (mem_map_of_mem _ hy)
  have hUC : U ≤ centralizer (W : Set P) := sup_le (le_centralizer W) hCW
  have hUW := normal_elementary_le_four_of_no_normal_eight hno W U hW hUC
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  exact hWD (hUW ((le_sup_right : zpowers x ≤ U) (mem_zpowers x)))

end IsPGroup

private theorem zmod_square_root (n : ℕ) (hn : 2 ≤ n)
    (x : Multiplicative (ZMod (2 ^ n))) (hx : x ^ 2 = 1) :
    ∃ y : Multiplicative (ZMod (2 ^ n)), y ^ 2 = x := by
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have hzero : (2 : ZMod (2 ^ n)) * x.toAdd = 0 := by
    have hh := congrArg Multiplicative.toAdd hx
    change 2 • x.toAdd = 0 at hh
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hh
  have hd : 2 ^ n ∣ 2 * x.toAdd.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using hzero
  have hfour : 4 ∣ 2 ^ n := by
    change 2 ^ 2 ∣ 2 ^ n
    exact pow_dvd_pow 2 hn
  have heven : 2 ∣ x.toAdd.val := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2)
    (show 2 * 2 ∣ 2 * x.toAdd.val from hfour.trans hd)
  obtain ⟨k, hk⟩ := heven
  refine ⟨Multiplicative.ofAdd (k : ZMod (2 ^ n)), ?_⟩
  apply Multiplicative.toAdd.injective
  change 2 • (k : ZMod (2 ^ n)) = x.toAdd
  rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val x.toAdd, hk]
  simp

private theorem homocyclic_square_root {D : Type*} [Group D]
    (n : ℕ) (hn : 2 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (d : D) (hd : d ^ 2 = 1) : ∃ r : D, r ^ 2 = d := by
  have he : (e d) ^ 2 = 1 := by rw [← map_pow, hd, map_one]
  obtain ⟨a, ha⟩ := zmod_square_root n hn (e d).1 (congrArg Prod.fst he)
  obtain ⟨b, hb⟩ := zmod_square_root n hn (e d).2 (congrArg Prod.snd he)
  refine ⟨e.symm (a, b), ?_⟩
  apply e.injective
  rw [map_pow, e.apply_symm_apply]
  exact Prod.ext ha hb

namespace IsPGroup

/-- Involutions fixing four-torsion belong to the homocyclic base, under the
normal-eight obstruction in the original group. -/
public theorem involution_mem_of_homocyclic_fixing_four_torsion
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (x : P) (hx : x ^ 2 = 1)
    (hfour : ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d) : x ∈ D := by
  let f : P →* MulAut D := MulAut.conjNormal
  let C := centralizer (W : Set P)
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hker (u : P) : f u = 1 ↔ u ∈ D := by
    constructor
    · intro h
      apply hDC
      intro d hd
      have hh := congrArg (fun a : MulAut D => (a ⟨d, hd⟩ : P)) h
      change u * d * u⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hu
      ext d
      change u * (d : P) * u⁻¹ = d
      rw [(D.le_centralizer hu d d.property).symm, mul_inv_cancel_right]
  have htwo (u : P) (hu : u ∈ C) (d : D) (hd : d ^ 2 = 1) : f u d = d := by
    have hdW : (d : P) ∈ W := by
      rw [← hO]
      exact ⟨d, subset_closure (by simpa using hd), rfl⟩
    apply Subtype.ext
    change u * (d : P) * u⁻¹ = d
    rw [(hu d hdW).symm, mul_inv_cancel_right]
  have hmemC (u : P) (hu : ∀ d : D, d ^ 4 = 1 → f u d = d) : u ∈ C := by
    intro w hw
    have hw2 : (⟨w, hWD hw⟩ : D) ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw
    have hw4 : (⟨w, hWD hw⟩ : D) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, hw2, one_pow]
    have hh := congrArg Subtype.val (hu ⟨w, hWD hw⟩ hw4)
    change u * w * u⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hdeep (u : P) (hu : u ^ 2 = 1)
      (hu4 : ∀ d : D, d ^ 4 = 1 → f u d = d) :=
    deep_involution_of_homocyclic_fixing_four_torsion n hn e (f u)
      (by rw [← map_pow, hu, map_one]) hu4
  have hcentral (u : P) (hu : u ^ 2 = 1)
      (hu4 : ∀ d : D, d ^ 4 = 1 → f u d = d)
      (hc : ∀ v : P, Commute (f v) (f u)) : u ∈ D := by
    apply involution_mem_of_normal_four_central_action hno W hW D hDC hO u hu
      (hmemC u hu4) hc
    intro d hd hdi
    have hh : f u (⟨d, hd⟩ : D) = (⟨d, hd⟩ : D)⁻¹ := Subtype.ext hdi
    exact congrArg Subtype.val ((hdeep u hu hu4).2 ⟨d, hd⟩ hh)
  have hCi : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two hP hZ W hW
  obtain ⟨t, ht⟩ := index_dvd_two_iff.mp (dvd_of_eq hCi)
  have hall (a : MulAut D) (haC : ∀ u ∈ C, Commute (f u) a)
      (hat : Commute (f t) a) : ∀ u, Commute (f u) a := by
    intro u
    rcases ht u with hu | hu
    · have hh := (haC (u * t) hu).mul_left hat.inv_left
      simpa only [map_mul, mul_inv_cancel_right] using hh
    · exact haC u hu
  let x' := t * x * t⁻¹
  have hx' : x' ^ 2 = 1 := by
    change (MulAut.conj t x) ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have hfour' : ∀ d : D, d ^ 4 = 1 → f x' d = d := by
    intro d hd
    have hd' : (f t⁻¹ d) ^ 4 = 1 := by rw [← map_pow, hd, map_one]
    change f (t * x * t⁻¹) d = d
    simp only [map_mul, MulAut.mul_apply]
    rw [show f x (f t⁻¹ d) = f t⁻¹ d from hfour _ hd', map_inv]
    exact (f t).apply_symm_apply d
  have hcx : ∀ u ∈ C, Commute (f u) (f x) := fun u hu =>
    (hdeep x hx hfour).1 (f u) (htwo u hu)
  have hcx' : ∀ u ∈ C, Commute (f u) (f x') := fun u hu =>
    (hdeep x' hx' hfour').1 (f u) (htwo u hu)
  have hxx' : Commute (f x) (f x') := hcx' x (hmemC x hfour)
  let v := x * x'
  have hvfour : ∀ d : D, d ^ 4 = 1 → f v d = d := by
    intro d hd
    change f (x * x') d = d
    simp only [map_mul, MulAut.mul_apply]
    rw [hfour' d hd, hfour d hd]
  have hv2D : v ^ 2 ∈ D := by
    apply (hker _).mp
    rw [map_pow, show f v = f x * f x' from f.map_mul x x', hxx'.mul_pow]
    simp only [← map_pow, hx, hx', map_one, mul_one]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hx'i : x'⁻¹ = x' := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx')
  have hvinv : x * v * x⁻¹ = v⁻¹ := by
    dsimp [v]
    rw [mul_inv_rev, hxi, hx'i]
    calc
      x * (x * x') * x = (x * x) * x' * x := by group
      _ = x' * x := by rw [← pow_two, hx, one_mul]
  have hv2inv : f x (⟨v ^ 2, hv2D⟩ : D) = (⟨v ^ 2, hv2D⟩ : D)⁻¹ := by
    apply Subtype.ext
    change MulAut.conj x (v ^ 2) = (v ^ 2)⁻¹
    rw [map_pow, show MulAut.conj x v = v⁻¹ from hvinv, inv_pow]
  have hv4 : (v ^ 2) ^ 2 = 1 := congrArg Subtype.val
    ((hdeep x hx hfour).2 ⟨v ^ 2, hv2D⟩ hv2inv)
  obtain ⟨r, hr⟩ := homocyclic_square_root n (by omega) e (⟨v ^ 2, hv2D⟩ : D)
    (Subtype.ext hv4)
  have hr4 : r ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hr]
    exact Subtype.ext hv4
  have hvr : Commute v (r : P) := by
    have hh := congrArg Subtype.val (hvfour r hr4)
    change v * (r : P) * v⁻¹ = r at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let y := v * (r : P)⁻¹
  have hy : y ^ 2 = 1 := by
    dsimp [y]
    rw [hvr.inv_right.mul_pow, inv_pow, ← Subgroup.coe_pow, hr]
    simp
  have hfy : f y = f x * f x' := by
    change f (v * (r : P)⁻¹) = _
    rw [map_mul, map_inv, (hker _).mpr r.property, inv_one, mul_one]
    exact f.map_mul x x'
  have hyfour : ∀ d : D, d ^ 4 = 1 → f y d = d := by
    intro d hd
    rw [hfy, MulAut.mul_apply, hfour' d hd, hfour d hd]
  have hfxt : f x' = f t * f x * (f t)⁻¹ := by simp only [x', map_mul, map_inv]
  have httx : Commute ((f t) ^ 2) (f x) := by
    rw [← map_pow]
    exact hcx (t ^ 2) (C.sq_mem_of_index_two hCi t)
  have hty : Commute (f t) (f y) := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [hfy]
    calc
      f t * (f x * f x') * (f t)⁻¹ =
          f x' * ((f t) ^ 2 * f x * ((f t) ^ 2)⁻¹) := by rw [hfxt]; group
      _ = f x' * f x := by rw [httx.eq, mul_inv_cancel_right]
      _ = f x * f x' := hxx'.eq.symm
  have hyD : y ∈ D := hcentral y hy hyfour (hall (f y)
    (fun u hu => by rw [hfy]; exact (hcx u hu).mul_right (hcx' u hu)) hty)
  have hprod : f x * f x' = 1 := hfy.symm.trans ((hker y).mpr hyD)
  have hfx'eq : f x' = f x := by
    have hh : (f x)⁻¹ = f x := by rw [← map_inv, hxi]
    exact (eq_inv_of_mul_eq_one_right hprod).trans hh
  apply hcentral x hx hfour (hall (f x) hcx ?_)
  exact mul_inv_eq_iff_eq_mul.mp (hfxt.symm.trans hfx'eq)

end IsPGroup

namespace IsPGroup

/-- A nontrivial fourth-root kernel gives a normal extension of index two
with no new involutions. -/
public theorem exists_normal_index_two_extension_of_four_torsion_kernel
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (g : P) (hg : g ∉ D)
    (hgfour : ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) g d = d) :
    ∃ X : Subgroup P, X.Normal ∧ D ≤ X ∧ D.relIndex X = 2 ∧
      (∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d) ∧
      (∀ x ∈ X, x ^ 2 = 1 → x ∈ D) := by
  let f : P →* MulAut D := MulAut.conjNormal
  let K := ((OmegaAction.omegaRestriction D 2 2).comp f).ker
  have hmem (x : P) : x ∈ K ↔ ∀ d : D, d ^ 4 = 1 → f x d = d :=
    OmegaAction.mem_ker_restriction_iff f 2 2 x
  have hDK : D ≤ K := by
    intro x hx
    apply (hmem x).mpr
    intro d _
    apply Subtype.ext
    change x * (d : P) * x⁻¹ = d
    rw [(D.le_centralizer hx d d.property).symm, mul_inv_cancel_right]
  let q := QuotientGroup.mk' D
  let N := K.map q
  let : N.Normal := QuotientGroup.map_normal D K
  have hN : Nontrivial N := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    refine ⟨Nat.card_pos.ne', ?_⟩
    intro hc
    have hbot : N = ⊥ := card_eq_one.mp hc
    have hqg : q g ∈ N := mem_map_of_mem q ((hmem g).mpr hgfour)
    rw [hbot, mem_bot] at hqg
    exact hg ((QuotientGroup.eq_one_iff (N := D) (x := g)).mp hqg)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 (P ⧸ D)) := ⟨hP.to_quotient D⟩
  obtain ⟨Z, hZN, hZNle, hZcard, _⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hN
  let : Z.Normal := hZN
  let X := Z.comap q
  have hDX : D ≤ X := by
    intro d hd
    change q d ∈ Z
    rw [show q d = 1 from (QuotientGroup.eq_one_iff (N := D) (x := d)).mpr hd]
    exact Z.one_mem
  have hXK : X ≤ K := by
    have hh : X ≤ N.comap q := comap_mono hZNle
    have he : N.comap q = K := by
      change (K.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D) = K
      rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hDK]
    exact he ▸ hh
  have hi : D.relIndex X = 2 := by
    rw [← QuotientGroup.ker_mk' D, relIndex_ker]
    change Nat.card ((Z.comap q).map q) = 2
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D)]
    exact hZcard
  refine ⟨X, inferInstance, hDX, hi, ?_, ?_⟩
  · intro x hx
    exact (hmem x).mp (hXK hx)
  · intro x hx hx2
    exact involution_mem_of_homocyclic_fixing_four_torsion hP hZ hno W hW D hDC hO
      n hn e x hx2 ((hmem x).mp (hXK hx))

end IsPGroup
