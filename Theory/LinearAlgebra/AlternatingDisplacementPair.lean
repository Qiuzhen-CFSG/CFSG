module
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Tactic

/-!
# Alternating displacement from two orthogonal centralizer bounds

Suppose two subspaces generate a binary symplectic space. If an isometry
moves each into its own orthogonal displacement subspace, and those two
images are mutually orthogonal, its displacement form is alternating.
Expand the isometry equation on one vector from each summand; its cross
terms cancel, and the diagonal terms vanish by orthogonality. Even rank
then makes a nonzero displacement fill any plane containing its image.
Alternating displacement forms supported on the same plane descend to the
same two-dimensional quotient, so a binary value determines each entire map.

The source application is the type-a₂ calculation on the actual U/Z(U)
in Aschbacher--Smith, 14.3.30, printed p.1002.
-/

public section
namespace Theory.LinearAlgebra
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- Two centralizer hyperplanes and their orthogonal displacement lines
force the symplectic involution's displacement form to be alternating. -/
theorem alternating_displacement_of_two_subspaces
    (B : LinearMap.BilinForm (ZMod 2) M) (hB : B.IsAlt)
    (S T P Q : Submodule (ZMod 2) M) (hgen : S ⊔ T = ⊤)
    (hSP : P ≤ B.orthogonal S) (hTQ : Q ≤ B.orthogonal T)
    (hPQ : Q ≤ B.orthogonal P)
    (t : M ≃ₗ[ZMod 2] M) (ht : ∀ x y, B (t x) (t y) = B x y)
    (hmoveS : ∀ x ∈ S, t x - x ∈ P)
    (hmoveT : ∀ x ∈ T, t x - x ∈ Q) :
    ∀ x, B x (t x - x) = 0 := by
  intro x
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (hgen ▸ Submodule.mem_top (x := x))
  let a := t u - u
  let b := t v - v
  have ha : a ∈ P := hmoveS u hu
  have hb : b ∈ Q := hmoveT v hv
  have hua : B u a = 0 := hSP ha u hu
  have hvb : B v b = 0 := hTQ hb v hv
  have hab : B a b = 0 := hPQ hb a ha
  have hcross : B u b + B a v = 0 := by
    have he := ht u v
    have htu : t u = u + a := by dsimp [a]; abel
    have htv : t v = v + b := by dsimp [b]; abel
    rw [htu, htv] at he
    simp only [map_add, LinearMap.add_apply, hab, add_zero] at he
    linear_combination he
  have hva : B v a = B a v := by simpa only [CharTwo.neg_eq] using (hB.neg_eq a v).symm
  have hm : t (u + v) - (u + v) = a + b := by simp only [map_add, a, b]; abel
  rw [hm]
  simp only [map_add, LinearMap.add_apply, hua, hvb, hva, zero_add, add_zero]
  simpa only [add_comm] using hcross

/-- A nonzero alternating displacement inside a plane fills that plane.
Nondegeneracy transfers the alternating form's even rank to the displacement. -/
theorem range_eq_plane_of_alternating_displacement [FiniteDimensional (ZMod 2) M]
    (B : LinearMap.BilinForm (ZMod 2) M) (hB : B.IsAlt) (hND : B.Nondegenerate)
    (N : M →ₗ[ZMod 2] M) (hN : N ≠ 0) (hAlt : ∀ x, B x (N x) = 0)
    (P : Submodule (ZMod 2) M) (hP : Module.finrank (ZMod 2) P = 2)
    (hNP : N.range ≤ P) : N.range = P := by
  let C : LinearMap.BilinForm (ZMod 2) M := B.compLeft N
  have hC : C.IsAlt := by
    intro x
    exact hB.eq_iff.mp (hAlt x)
  have hker : C.ker = N.ker := by
    ext x
    constructor
    · intro hx
      apply hND.1
      intro y
      exact LinearMap.congr_fun hx y
    · intro hx
      ext y
      change B (N x) y = 0
      rw [hx, map_zero, LinearMap.zero_apply]
  have he := AlternatingForm.even_finrank_sub_finrank_ker C hC
  have hd := N.finrank_range_add_finrank_ker
  rw [hker, ← hd, Nat.add_sub_cancel_right] at he
  have hle := Submodule.finrank_mono hNP
  have hpos : 0 < Module.finrank (ZMod 2) N.range := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hN (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
  have hdim : Module.finrank (ZMod 2) N.range = 2 := by
    rw [hP] at hle
    obtain ⟨k, hk⟩ := he
    omega
  exact Submodule.eq_of_le_of_finrank_eq hNP (hdim.trans hP.symm)

private theorem alternating_plane_ext {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    [FiniteDimensional (ZMod 2) Q] (hd : Module.finrank (ZMod 2) Q = 2)
    (C D : LinearMap.BilinForm (ZMod 2) Q) (hC : C.IsAlt) (hD : D.IsAlt)
    (he : C (Module.finBasisOfFinrankEq (ZMod 2) Q hd 0)
      (Module.finBasisOfFinrankEq (ZMod 2) Q hd 1) =
      D (Module.finBasisOfFinrankEq (ZMod 2) Q hd 0)
      (Module.finBasisOfFinrankEq (ZMod 2) Q hd 1)) : C = D := by
  let e := Module.finBasisOfFinrankEq (ZMod 2) Q hd
  have hrev : C (e 1) (e 0) = D (e 1) (e 0) := by
    rw [← hC.neg_eq, ← hD.neg_eq]
    exact congrArg Neg.neg he
  ext x y
  rw [← e.sum_repr x, ← e.sum_repr y]
  have he' : C (e 0) (e 1) = D (e 0) (e 1) := he
  simp only [Fin.sum_univ_two, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, hC.self_eq_zero, hD.self_eq_zero,
    hrev, he', smul_zero, add_zero, zero_add]

/-- A family of distinct linear maps with alternating displacement form and
image in one binary plane contains at most two maps. -/
theorem card_le_two_of_alternating_plane_maps [FiniteDimensional (ZMod 2) M]
    {A : Type*} [Finite A] (B : LinearMap.BilinForm (ZMod 2) M)
    (hND : B.Nondegenerate) (P : Submodule (ZMod 2) M)
    (hP : Module.finrank (ZMod 2) P = 2)
    (N : A → M →ₗ[ZMod 2] M) (hinj : Function.Injective N)
    (hAlt : ∀ a x, B (N a x) x = 0)
    (hNP : ∀ a, (N a).range ≤ P) : Nat.card A ≤ 2 := by
  let W := B.orthogonal P
  let Q := M ⧸ W
  have hQ : Module.finrank (ZMod 2) Q = 2 := by
    have hdim := W.finrank_quotient_add_finrank
    have horth := B.finrank_orthogonal hND P
    have hle := Submodule.finrank_le P
    change Module.finrank (ZMod 2) Q + Module.finrank (ZMod 2) W = _ at hdim
    change Module.finrank (ZMod 2) W = _ at horth
    omega
  let C (a : A) : LinearMap.BilinForm (ZMod 2) M := B.compLeft (N a)
  have hC (a : A) : (C a).IsAlt := hAlt a
  have hright (a : A) : W ≤ (C a).flip.ker := by
    intro x hx
    ext y
    exact hx (N a y) (hNP a (LinearMap.mem_range_self _ y))
  have hleft (a : A) : W ≤ (C a).ker := by
    intro x hx
    ext y
    exact (hC a).eq_iff.mpr (LinearMap.congr_fun (hright a hx) y)
  let D (a : A) := LinearMap.liftQ₂ W W (C a) (hleft a) (hright a)
  have hD (a : A) : (D a).IsAlt := by
    intro x
    refine Submodule.Quotient.induction_on W x ?_
    intro x
    exact hAlt a x
  let e := Module.finBasisOfFinrankEq (ZMod 2) Q hQ
  let f (a : A) : ZMod 2 := D a (e 0) (e 1)
  have hf : Function.Injective f := by
    intro a b hab
    have hDE : D a = D b := alternating_plane_ext hQ (D a) (D b) (hD a) (hD b) hab
    apply hinj
    ext x
    apply sub_eq_zero.mp
    apply hND.1
    intro y
    have hval := congrArg (fun E : LinearMap.BilinForm (ZMod 2) Q =>
      E (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) hDE
    change B (N a x) y = B (N b x) y at hval
    simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using hval
  simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective f hf

end Theory.LinearAlgebra
