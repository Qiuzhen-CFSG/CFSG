module
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Singular extensions of a binary plane in dimension six

A two-space in a nondegenerate binary quadratic six-space lies in at most
two totally singular three-spaces. Two distinct such spaces span the polar
orthogonal of the common plane. A third forces a vector outside the first
space into its polar orthogonal, which equals that first space.

Source: Aschbacher--Smith,12.6.28(4), printed p.835. The subgroup-coordinate
application is in Chapter12.Section06.NaturalSource.SingularExtensions.
-/

public section
open Module
namespace BinaryPermutation.EightSingularExtensions
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem singular_orthogonal_eq (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank (ZMod 2) W = 6)
    (E : Submodule (ZMod 2) W) (he : finrank (ZMod 2) E = 3)
    (hs : ∀ e ∈ E, Q e = 0) : LinearMap.BilinForm.orthogonal Q.polarBilin E = E := by
  apply (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · intro e he x hx
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      hs _ (E.add_mem hx he),hs _ hx,hs _ he,sub_zero]
  · rw [LinearMap.BilinForm.finrank_orthogonal hQ,hd,he]

/-- A singular plane in a nondegenerate binary six-space lies in at most two
singular three-spaces. -/
theorem not_three (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank (ZMod 2) W = 6)
    (D : Submodule (ZMod 2) W) (hD : finrank (ZMod 2) D = 2)
    (E : Fin 3 → Submodule (ZMod 2) W)
    (hE : ∀ i, D ≤ E i ∧ finrank (ZMod 2) (E i) = 3 ∧ ∀ e ∈ E i, Q e = 0) :
    ¬ Function.Injective E := by
  intro hinj
  have distinct {i j : Fin 3} (hij : i ≠ j) : E i ≠ E j := fun h => hij (hinj h)
  have meet {i j : Fin 3} (hij : i ≠ j) : E i ⊓ E j = D := by
    have hle : D ≤ E i ⊓ E j := le_inf (hE i).1 (hE j).1
    have hi : E i ⊓ E j < E i := lt_of_le_of_ne inf_le_left (by
      intro he
      have hij' : E i ≤ E j := he ▸ inf_le_right
      exact distinct hij (Submodule.eq_of_le_of_finrank_le hij' (by rw [(hE i).2.1,(hE j).2.1])))
    exact (Submodule.eq_of_le_of_finrank_le hle (by
      have hh := Submodule.finrank_lt_finrank_of_lt hi
      rw [(hE i).2.1] at hh
      omega)).symm
  let U := LinearMap.BilinForm.orthogonal Q.polarBilin D
  have hU : finrank (ZMod 2) U = 4 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ,hd,hD]
  have hEU (i) : E i ≤ U := by
    intro v hv d hd'
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      (hE i).2.2 _ ((E i).add_mem ((hE i).1 hd') hv),
      (hE i).2.2 _ ((hE i).1 hd'),(hE i).2.2 _ hv,sub_zero]
  have hsum : E 0 ⊔ E 1 = U := by
    apply Submodule.eq_of_le_of_finrank_le (sup_le (hEU 0) (hEU 1))
    have hh := (E 0).finrank_sup_add_finrank_inf_eq (E 1)
    rw [(hE 0).2.1,(hE 1).2.1,meet (by decide : (0 : Fin 3) ≠ 1),hD] at hh
    omega
  have hproper : D < E 2 := lt_of_le_of_ne (hE 2).1 (by
    intro h
    have hh := congrArg (fun U : Submodule (ZMod 2) W => finrank (ZMod 2) U) h
    rw [hD,(hE 2).2.1] at hh
    omega)
  obtain ⟨v,hv,hvD⟩ := SetLike.exists_of_lt hproper
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp (hsum.symm ▸ hEU 2 hv)
  have haD : a ∉ D := by
    intro haD
    have hab : a+b ∈ E 1 := (E 1).add_mem ((hE 1).1 haD) hb
    exact hvD ((meet (by decide : (2 : Fin 3) ≠ 1)) ▸ (show a+b ∈ E 2 ⊓ E 1 from ⟨hv,hab⟩))
  have hbD : b ∉ D := by
    intro hbD
    have hab : a+b ∈ E 0 := (E 0).add_mem ha ((hE 0).1 hbD)
    exact hvD ((meet (by decide : (2 : Fin 3) ≠ 0)) ▸ (show a+b ∈ E 2 ⊓ E 0 from ⟨hv,hab⟩))
  have hp : Q.polarBilin a b = 0 := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      (hE 2).2.2 _ hv,(hE 0).2.2 _ ha,(hE 1).2.2 _ hb,sub_zero]
  have hspan : D ⊔ Submodule.span (ZMod 2) {a} = E 0 := by
    apply Submodule.eq_of_le_of_finrank_le (sup_le (hE 0).1 (Submodule.span_le.mpr (by simpa)))
    have hlt : D < D ⊔ Submodule.span (ZMod 2) {a} := lt_of_le_of_ne le_sup_left (by
      intro he
      exact haD (he.symm ▸ (show a ∈ D ⊔ Submodule.span (ZMod 2) {a} from
        (show Submodule.span (ZMod 2) {a} ≤ D ⊔ Submodule.span (ZMod 2) {a} from le_sup_right) (Submodule.subset_span (by simp)))))
    have hh := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hD] at hh
    rw [(hE 0).2.1]
    omega
  have hborth : b ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (E 0) := by
    rw [←hspan]
    intro x hx
    obtain ⟨d,hd',c,hc,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,hp,smul_zero,add_zero]
    exact hEU 1 hb d hd'
  rw [singular_orthogonal_eq Q hQ hd (E 0) (hE 0).2.1 (hE 0).2.2] at hborth
  exact hbD ((meet (by decide : (0 : Fin 3) ≠ 1)) ▸ (show b ∈ E 0 ⊓ E 1 from ⟨hborth,hb⟩))
end BinaryPermutation.EightSingularExtensions
