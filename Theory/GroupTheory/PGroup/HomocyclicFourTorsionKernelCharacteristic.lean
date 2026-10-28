module

public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseNonfaithfulReduction

/-!
# Characteristicity of the large homocyclic four-torsion kernel

Let `D` be a normal abelian homocyclic subgroup of exponent at least eight,
`W = Ω₁(D)`, and `C = C_P(W)`. Under the normal-eight obstruction and the
self-centralizing-base hypotheses, the full kernel `K` of conjugation on
`Ω₂(D)` is characteristic in `C`.

The proof uses two intrinsic power properties. Every square in `C` belongs
to `K`: an automorphism of an abelian group fixing involutions has square
fixing four-torsion. Conversely, every element of `Ω₂(D)` is a square in
`D`. Thus any automorphism of `C` sends such an element into `K`; the
previously proved equality `Ω₂(K) = Ω₂(D)` puts its image back in `D`.
Consequently `Ω₂(D)`, and hence its centralizer `K`, is invariant. We use
this argument elementwise, without choosing a characteristic base.

Source context: MacWilliams, *On 2-groups with no normal abelian subgroups
of rank 3*, Trans. AMS 150 (1970), printed pp.377–379, (xvii)–(xix).
This intrinsic argument supplies the invariance needed when the given base
is merely normal; it does not transfer the source's invariant-base assumption.
The coordinate square-root calculation adapts the corresponding private
calculation in `HomocyclicLargeBaseNonfaithfulReduction` to fourth roots.
-/

open Subgroup
open scoped IsMulCommutative

private theorem square_aut_fixes_four {G : Type*} [Group G] [IsMulCommutative G]
    (a : MulAut G) (ha : ∀ d : G, d ^ 2 = 1 → a d = d)
    (d : G) (hd : d ^ 4 = 1) : a (a d) = d := by
  have hd2 : (d ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hd
  have hu : (a d * d⁻¹) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, ha _ hd2, mul_inv_cancel]
  have he := ha _ hu
  rw [map_mul, map_inv] at he
  calc
    a (a d) = (a (a d) * (a d)⁻¹) * a d := by group
    _ = (a d * d⁻¹) * a d := by rw [he]
    _ = (a d * d⁻¹) ^ 2 * d := by rw [pow_two]; group
    _ = d := by rw [hu, one_mul]

private theorem zmod_four_square_root (n : ℕ) (hn : 3 ≤ n)
    (x : Multiplicative (ZMod (2 ^ n))) (hx : x ^ 4 = 1) :
    ∃ y : Multiplicative (ZMod (2 ^ n)), y ^ 2 = x := by
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have hzero : (4 : ZMod (2 ^ n)) * x.toAdd = 0 := by
    have hh := congrArg Multiplicative.toAdd hx
    change 4 • x.toAdd = 0 at hh
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hh
  have hd : 2 ^ n ∣ 4 * x.toAdd.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using hzero
  have height : 8 ∣ 2 ^ n := by
    change 2 ^ 3 ∣ 2 ^ n
    exact pow_dvd_pow 2 hn
  have heven : 2 ∣ x.toAdd.val := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4)
    (show 4 * 2 ∣ 4 * x.toAdd.val from height.trans hd)
  obtain ⟨k, hk⟩ := heven
  refine ⟨Multiplicative.ofAdd (k : ZMod (2 ^ n)), ?_⟩
  apply Multiplicative.toAdd.injective
  change 2 • (k : ZMod (2 ^ n)) = x.toAdd
  rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val x.toAdd, hk]
  simp

private theorem homocyclic_four_square_root {D : Type*} [Group D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (d : D) (hd : d ^ 4 = 1) : ∃ r : D, r ^ 2 = d := by
  have he : (e d) ^ 4 = 1 := by rw [← map_pow, hd, map_one]
  obtain ⟨a, ha⟩ := zmod_four_square_root n hn (e d).1 (congrArg Prod.fst he)
  obtain ⟨b, hb⟩ := zmod_four_square_root n hn (e d).2 (congrArg Prod.snd he)
  refine ⟨e.symm (a, b), ?_⟩
  apply e.injective
  rw [map_pow, e.apply_symm_apply]
  exact Prod.ext ha hb

namespace Subgroup

/-- Squares in the centralizer of the first omega subgroup fix the second omega subgroup. -/
public theorem square_mem_fourTorsionKernel_of_mem_centralizer
    {P : Type*} [Group P]
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (x : P) (hx : x ∈ centralizer (W : Set P)) : x ^ 2 ∈ fourTorsionKernel D := by
  apply (mem_fourTorsionKernel_iff D _).mpr
  intro d hd
  rw [map_pow]
  change MulAut.conjNormal x (MulAut.conjNormal x d) = d
  apply square_aut_fixes_four _ _ d hd
  intro v hv
  have hvW : (v : P) ∈ W := by
    rw [← hO]
    exact ⟨v, subset_closure (by simpa using hv), rfl⟩
  apply Subtype.ext
  change x * (v : P) * x⁻¹ = v
  rw [(hx v hvW).symm, mul_inv_cancel_right]

/-- The full four-torsion kernel is characteristic in the centralizer of the normal four.
Neither the base nor an index-two extension is assumed characteristic. -/
public theorem fourTorsionKernel_characteristic_in_centralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    ((fourTorsionKernel D).subgroupOf (centralizer (W : Set P))).Characteristic := by
  let C := centralizer (W : Set P)
  let K := fourTorsionKernel D
  have hKC : K ≤ C := fourTorsionKernel_le_centralizer W D hWD
  have hDC' : D ≤ C := (le_fourTorsionKernel D).trans hKC
  have hfourmem (y : P) (hy : y ∈ K) (hy4 : y ^ 4 = 1) : y ∈ D := by
    have hyO : y ∈ (omega K (p := 2) 2).map K.subtype :=
      ⟨⟨y, hy⟩, subset_closure (Subtype.ext hy4), rfl⟩
    rw [omega_two_fourTorsionKernel_eq hP hZ hno W hW D hDC hO n hn e] at hyO
    obtain ⟨d, _, hd⟩ := hyO
    exact hd ▸ d.property
  apply characteristic_iff_le_comap.mpr
  intro f x hx
  change (f x : P) ∈ K
  apply (mem_fourTorsionKernel_iff D _).mpr
  intro d hd
  obtain ⟨r, hr⟩ := homocyclic_four_square_root n hn e d hd
  let dC : C := ⟨d, hDC' d.property⟩
  let rC : C := ⟨r, hDC' r.property⟩
  have hrd : rC ^ 2 = dC := Subtype.ext (congrArg (fun v : D => (v : P)) hr)
  have hpreK : (f.symm dC : P) ∈ K := by
    rw [← hrd, map_pow]
    exact square_mem_fourTorsionKernel_of_mem_centralizer W D hO
      (f.symm rC) (f.symm rC).property
  have hdC : dC ^ 4 = 1 := Subtype.ext (congrArg (fun v : D => (v : P)) hd)
  have hpre4 : (f.symm dC : P) ^ 4 = 1 := by
    have hh : (f.symm dC) ^ 4 = 1 := by rw [← map_pow, hdC, map_one]
    exact congrArg Subtype.val hh
  have hpreD := hfourmem _ hpreK hpre4
  have hcomm : x * f.symm dC = f.symm dC * x := by
    apply Subtype.ext
    have hh := congrArg Subtype.val ((mem_fourTorsionKernel_iff D x).mp hx
      ⟨f.symm dC, hpreD⟩ (Subtype.ext hpre4))
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hfcomm : f x * dC = dC * f x := by
    simpa only [map_mul, f.apply_symm_apply] using congrArg f hcomm
  apply Subtype.ext
  change (f x : P) * (d : P) * (f x : P)⁻¹ = d
  exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val hfcomm)

end Subgroup
