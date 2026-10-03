module

public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseFourTorsionKernel
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Reductions for a nonfaithful large homocyclic base

Let `D` be a normal homocyclic abelian subgroup of exponent at least eight.
For an involutory automorphism fixing four-torsion, the norm map covers every
square in `D`: its displacement is an involution, and a square root of that
displacement corrects the norm. Consequently, in a four-torsion-fixing
overgroup with no new involutions, every element of fourth power one already
belongs to `D`.

Under the ambient normal-eight obstruction, apply this to the full
four-torsion kernel `K`. Its second omega subgroup equals that of `D`, is
central in `K`, and is isomorphic to `C₄ × C₄`. A proper index-two extension
of the self-centralizing base makes `K` nonabelian.

The assembly criterion in `HomocyclicLargeBaseNonfaithful` isolates two further
structural obligations:
characteristicity of `K` in the centralizer of the normal four, and cyclicity
of its derived subgroup. If both hold, the first omega subgroup of that
nontrivial derived subgroup gives the required characteristic involution.
Neither structural obligation is asserted unconditionally here; in particular,
normality of the given base or extension is never treated as characteristicity.

Source context: MacWilliams, *On 2-groups with no normal abelian subgroups of
rank 3*, Trans. AMS 150 (1970), printed pp.377–379, especially (xvii).
The source uses Alperin's metacyclic centralizer result and an invariant base;
those additional conclusions still require proofs for the present inputs.
The square-root calculation below is adapted from the private calculation in
`HomocyclicLargeBaseFourTorsionKernel`; the norm argument is direct.
-/

open Subgroup
open scoped IsMulCommutative

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

/-- The norm of an involutory automorphism fixing four-torsion covers all squares. -/
public theorem norm_covers_squares_of_homocyclic_deep_involution
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut D) (ha : a ^ 2 = 1)
    (hfour : ∀ d : D, d ^ 4 = 1 → a d = d) (d : D) :
    ∃ r : D, a r * r = d ^ 2 := by
  let u := a d * d⁻¹
  have haa (v : D) : a (a v) = v := by
    have hh := congrArg (fun b : MulAut D => b v) ha
    exact hh
  have hui : a u = u⁻¹ := by
    dsimp [u]
    rw [map_mul, map_inv, haa, mul_inv_rev, inv_inv]
  have hu : u ^ 2 = 1 :=
    (deep_involution_of_homocyclic_fixing_four_torsion n hn e a ha hfour).2 u hui
  obtain ⟨s, hs⟩ := homocyclic_square_root n (by omega) e u hu
  have hs4 : s ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hs, hu]
  refine ⟨d * s⁻¹, ?_⟩
  rw [map_mul, map_inv, hfour s hs4]
  calc
    a d * s⁻¹ * (d * s⁻¹) = (a d * d) * (s ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
      ac_rfl
    _ = d ^ 2 := by
      rw [hs]
      simp [u, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc, pow_two]

/-- A kernel element whose square is a base square already belongs to the base. -/
public theorem mem_of_square_in_base_squares_of_homocyclic_fixing_four_torsion
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (X : Subgroup P) (hDX : D ≤ X)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hfour : ∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d)
    (hinv : ∀ x ∈ X, x ^ 2 = 1 → x ∈ D)
    (x : P) (hx : x ∈ X) (d : D) (hd : x ^ 2 = (d : P) ^ 2) : x ∈ D := by
  let a : MulAut D := MulAut.conjNormal x
  have hx2 : x ^ 2 ∈ D := hd ▸ D.pow_mem d.property 2
  have ha : a ^ 2 = 1 := by
    change (MulAut.conjNormal (H := D) x) ^ 2 = 1
    rw [← map_pow]
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change x ^ 2 * (v : P) * (x ^ 2)⁻¹ = v
    rw [(D.le_centralizer hx2 v v.property).symm, mul_inv_cancel_right]
  obtain ⟨r, hr⟩ := norm_covers_squares_of_homocyclic_deep_involution
    n hn e a ha (hfour x hx) d
  have hprod : (x * (r : P)⁻¹) ^ 2 = 1 := by
    have hnorm : x * (r : P) * x⁻¹ * (r : P) = (d : P) ^ 2 :=
      congrArg Subtype.val hr
    calc
      (x * (r : P)⁻¹) ^ 2 =
          (x * (r : P) * x⁻¹)⁻¹ * (r : P)⁻¹ * x ^ 2 := by
            have hc : Commute (x ^ 2) (r : P) :=
              (D.le_centralizer hx2 r r.property).symm
            calc
              (x * (r : P)⁻¹) ^ 2 =
                  (x * (r : P) * x⁻¹)⁻¹ * x ^ 2 * (r : P)⁻¹ := by
                    simp only [pow_two]; group
              _ = _ := by rw [mul_assoc, hc.inv_right.eq, ← mul_assoc]
      _ = 1 := by
        have hc : Commute (x * (r : P) * x⁻¹) (r : P) :=
          (D.le_centralizer ((inferInstance : D.Normal).conj_mem r r.property x) r r.property).symm
        rw [hc.inv_inv.eq, ← mul_inv_rev, hnorm, hd, inv_mul_cancel]
  have hm := hinv (x * (r : P)⁻¹) (X.mul_mem hx (X.inv_mem (hDX r.property))) hprod
  simpa using D.mul_mem hm r.property

end IsPGroup

namespace IsPGroup

/-- No new involutions in the kernel also excludes new elements of order four. -/
public theorem four_torsion_mem_of_homocyclic_fixing_four_torsion
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (X : Subgroup P) (hDX : D ≤ X)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hfour : ∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d)
    (hinv : ∀ x ∈ X, x ^ 2 = 1 → x ∈ D)
    (x : P) (hx : x ∈ X) (hx4 : x ^ 4 = 1) : x ∈ D := by
  have hx22 : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hx4
  have hx2 : x ^ 2 ∈ D := hinv (x ^ 2) (X.pow_mem hx 2) hx22
  obtain ⟨d, hd⟩ := homocyclic_square_root n (by omega) e
    (⟨x ^ 2, hx2⟩ : D) (Subtype.ext hx22)
  exact mem_of_square_in_base_squares_of_homocyclic_fixing_four_torsion
    D X hDX n hn e hfour hinv x hx d (congrArg Subtype.val hd).symm

end IsPGroup

namespace Subgroup

/-- A nonabelian characteristic subgroup with cyclic derived subgroup singles out an involution. -/
public theorem exists_characteristic_two_of_nonabelian_characteristic_cyclic_derived
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (K : Subgroup G) [K.Characteristic]
    (hnonab : ¬ IsMulCommutative K) [IsCyclic (_root_.commutator K)] :
    ∃ L : Subgroup G, L.Characteristic ∧ Nat.card L = 2 := by
  let J := _root_.commutator K
  have hJne : J ≠ ⊥ := fun h => hnonab ((commutator_eq_bot_iff K).mp h)
  have hdvd : 2 ∣ Nat.card J := by
    rcases ((hG.to_subgroup K).to_subgroup J).card_eq_or_dvd with h | h
    · exact False.elim (hJne (card_eq_one.mp h))
    · exact h
  let O := omega₁ J (p := 2)
  let : O.Characteristic := omega₁_characteristic J
  have hc : Nat.card O = 2 := by
    rw [show O = (powMonoidHom 2 : J →* J).ker from OmegaAction.omega_eq_pow_ker 2 1]
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvd]
  let M := O.map J.subtype
  let : M.Characteristic := characteristic_of_characteristic_of_characteristic
  let L := M.map K.subtype
  exact ⟨L, characteristic_of_characteristic_of_characteristic, by
    rw [card_map_of_injective K.subtype_injective, card_map_of_injective J.subtype_injective]
    exact hc⟩

end Subgroup

namespace Subgroup

/-- The kernel of conjugation on the second binary omega subgroup of a normal base. -/
@[expose] public noncomputable def fourTorsionKernel {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] : Subgroup P :=
  ((OmegaAction.omegaRestriction D 2 2).comp
    (MulAut.conjNormal : P →* MulAut D)).ker

/-- A conjugation-restriction kernel is normal in the ambient group. -/
public instance fourTorsionKernel_normal {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] : (fourTorsionKernel D).Normal :=
  inferInstanceAs (MonoidHom.ker _).Normal

/-- Membership in the kernel means fixing every element of fourth power one. -/
public theorem mem_fourTorsionKernel_iff {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] (x : P) :
    x ∈ fourTorsionKernel D ↔
      ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d :=
  OmegaAction.mem_ker_restriction_iff _ 2 2 x

/-- An abelian base fixes its own four-torsion. -/
public theorem le_fourTorsionKernel {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] : D ≤ fourTorsionKernel D := by
  intro x hx
  apply (mem_fourTorsionKernel_iff D x).mpr
  intro d _
  apply Subtype.ext
  change x * (d : P) * x⁻¹ = d
  rw [(D.le_centralizer hx d d.property).symm, mul_inv_cancel_right]

/-- The four-torsion kernel centralizes any elementary binary subgroup of the base. -/
public theorem fourTorsionKernel_le_centralizer {P : Type*} [Group P]
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 W] (hWD : W ≤ D) :
    fourTorsionKernel D ≤ centralizer (W : Set P) := by
  intro x hx w hw
  have hw2 : (⟨w, hWD hw⟩ : D) ^ 2 = 1 :=
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw)
  have hw4 : (⟨w, hWD hw⟩ : D) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hw2, one_pow]
  have hh := congrArg Subtype.val ((mem_fourTorsionKernel_iff D x).mp hx _ hw4)
  change x * w * x⁻¹ = w at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The kernel and the base have identical second omega subgroups in the ambient group. -/
public theorem omega_two_fourTorsionKernel_eq
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    (omega (fourTorsionKernel D) (p := 2) 2).map (fourTorsionKernel D).subtype =
      (omega D (p := 2) 2).map D.subtype := by
  let K := fourTorsionKernel D
  have hinv : ∀ x ∈ K, x ^ 2 = 1 → x ∈ D := by
    intro x hx hx2
    exact IsPGroup.involution_mem_of_homocyclic_fixing_four_torsion
      hP hZ hno W hW D hDC hO n hn e x hx2 ((mem_fourTorsionKernel_iff D x).mp hx)
  have hfour : ∀ x ∈ K, x ^ 4 = 1 → x ∈ D := by
    intro x hx hx4
    exact IsPGroup.four_torsion_mem_of_homocyclic_fixing_four_torsion
      D K (le_fourTorsionKernel D) n hn e
      (fun x hx => (mem_fourTorsionKernel_iff D x).mp hx) hinv x hx hx4
  change (closure {x : K | x ^ (2 ^ 2) = 1}).map K.subtype =
    (closure {x : D | x ^ (2 ^ 2) = 1}).map D.subtype
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy4 : (y : P) ^ 4 = 1 := congrArg Subtype.val hy
    exact ⟨⟨y, hfour y y.property hy4⟩, Subtype.ext hy4, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, le_fourTorsionKernel D y.property⟩,
      Subtype.ext (congrArg (fun d : D => (d : P)) hy), rfl⟩

/-- A proper extension inside the kernel makes the kernel nonabelian. -/
public theorem nonabelian_fourTorsionKernel_of_extension
    {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (X : Subgroup P) (hi : D.relIndex X = 2)
    (hfour : ∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d) :
    ¬ IsMulCommutative (fourTorsionKernel D) := by
  intro hab
  let := hab
  have hXD : X ≤ D := by
    intro x hx
    apply hDC
    intro d hd
    exact (fourTorsionKernel D).le_centralizer
      ((mem_fourTorsionKernel_iff D x).mpr (hfour x hx)) d (le_fourTorsionKernel D hd)
  have h1 := relIndex_eq_one.mpr hXD
  omega

end Subgroup

namespace Subgroup

/-- The second omega subgroup of the full four-torsion kernel is central. -/
public theorem omega_two_fourTorsionKernel_central
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    omega (fourTorsionKernel D) (p := 2) 2 ≤ center (fourTorsionKernel D) := by
  let K := fourTorsionKernel D
  intro z hz
  have hm := mem_map_of_mem K.subtype hz
  rw [omega_two_fourTorsionKernel_eq hP hZ hno W hW D hDC hO n hn e] at hm
  obtain ⟨d, hd, he⟩ := hm
  have hd4 : d ^ 4 = 1 := by
    rw [OmegaAction.omega_eq_pow_ker] at hd
    exact hd
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  have hh := congrArg Subtype.val ((mem_fourTorsionKernel_iff D x).mp x.property d hd4)
  change (x : P) * (d : P) * (x : P)⁻¹ = d at hh
  change (d : P) = (z : P) at he
  rw [he] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The second omega subgroup of the full kernel is a product of two cyclic fours. -/
public noncomputable def omegaTwoFourTorsionKernelEquiv
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    omega (fourTorsionKernel D) (p := 2) 2 ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  let K := fourTorsionKernel D
  let f := (omega K (p := 2) 2).equivMapOfInjective K.subtype K.subtype_injective
  let g := (omega D (p := 2) 2).equivMapOfInjective D.subtype D.subtype_injective
  let h := MulEquiv.subgroupCongr
    (omega_two_fourTorsionKernel_eq hP hZ hno W hW D hDC hO n hn e)
  exact ((f.trans h).trans g.symm).trans
    ((e.omega 2 2).trans (OmegaAction.productOmegaEquiv n n 2 (by omega) (by omega)))

end Subgroup
