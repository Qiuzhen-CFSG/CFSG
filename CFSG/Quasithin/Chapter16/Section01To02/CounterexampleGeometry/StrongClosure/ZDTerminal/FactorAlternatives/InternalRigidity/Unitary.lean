module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Unitary.Coordinates
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Unitary.Sylow
public import BenderSuzuki.Converse.PSU3

/-!
# Sylow-factor rigidity in the binary projective unitary model

The actual upper Hermitian root image is a Sylow two-subgroup. Conjugate
an arbitrary Sylow subgroup onto this image, transport the strongly closed
factor union, and pull both factors back through the injective root map.
Strong closure makes their coordinate union invariant under the full torus.
The coordinate theorem then proves nesting, which injectivity transports
back to the original factors.

The coefficient field has order `q²`, its fixed field has order `q`, and
`q = 2ⁿ` with `n ≥ 2`. Both the Sylow calculation and torus action use the
actual projective image, including its scalar quotient. The published
statement retains both elementary-four hypotheses.

This discharges the unitary premise of
`terminal_factors_nested_of_nonlinear_models`. Source: Aschbacher,
*On finite groups of component type* (1975), Lemma 3.4, final paragraph
on p.96; GLS4, Chapter 2, Theorem ZD. The concrete matrix calculations
are from Huppert II.10.12.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity
private theorem root_factors_nested {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {q : ℕ} (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2 < q)
    (B C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : B ≤ rootImage J hJ) (hC : C ≤ rootImage J hJ)
    (hcomm : ⁅B, C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set _) ∪ C) (rootImage J hJ) ⊤) :
    B ≤ C ∨ C ≤ B := by
  let f := hermitianUnipotentPSU J hJ
  have hc : ∀ z ∈ B.comap f, ∀ w ∈ C.comap f, Commute z w := by
    intro z hz w hw
    apply (root_injective J hJ)
    change f (z*w) = f (w*z)
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp
      ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hz) (f w) hw).symm
  have ht : ∀ (k : Eˣ) z, z ∈ B.comap f ∨ z ∈ C.comap f →
      hermitianTorusAction J k z ∈ B.comap f ∨ hermitianTorusAction J k z ∈ C.comap f := by
    intro k z hz
    have hh := hclosed.2 (f z) hz (hermitianTorusPSU J hJ k)⁻¹ (mem_top _) ?_
    · simpa only [f, inv_inv, projective_torus_action, Subgroup.mem_comap,
        Set.mem_union, SetLike.mem_coe] using hh
    · simp only [f, inv_inv, projective_torus_action]
      exact ⟨hermitianTorusAction J k z, rfl⟩
  rcases UnitaryCoordinates.factors_nested J hJ hcard hfixed hq (B.comap f) (C.comap f) hc ht with h | h
  · left
    intro x hx
    obtain ⟨z, rfl⟩ := hB hx
    exact h hx
  · right
    intro x hx
    obtain ⟨z, rfl⟩ := hC hx
    exact h hx

/-- Commuting Sylow factors with strongly closed union nest in PSU₃(2ⁿ). -/
public theorem unitary_rigidity (n : ℕ) (hn : 2 ≤ n) (E : Type) [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) :
    SylowFactorRigidity (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP E 2 := BenderSuzuki.Converse.charP_two_of_card
    (n := 2*n) (by omega) (by rw [hcard, ← pow_mul]; ring_nf)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  intro P B C hBP hCP hBC _hB _hC hclosed
  let U := UnitarySylow.rootSylow J hJ (show n ≠ 0 by omega) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P U
  let e := MulAut.conj g
  have hP : (P : Subgroup _).map e.toMonoidHom = rootImage J hJ :=
    congrArg Sylow.toSubgroup hg
  have hBr : B.map e.toMonoidHom ≤ rootImage J hJ := hP ▸ map_mono hBP
  have hCr : C.map e.toMonoidHom ≤ rootImage J hJ := hP ▸ map_mono hCP
  have hcomm : ⁅B.map e.toMonoidHom, C.map e.toMonoidHom⁆ = ⊥ := by
    rw [← map_commutator, hBC, Subgroup.map_bot]
  have hc : IsStronglyClosedSet
      ((B.map e.toMonoidHom : Set _) ∪ C.map e.toMonoidHom) (rootImage J hJ) ⊤ := by
    have hh := stronglyClosed_image P ((B : Set _) ∪ C) hclosed e.toMonoidHom e.surjective
    rwa [Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map, hP] at hh
  have hq : 2 < 2^n := by
    have h4 : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    omega
  rcases root_factors_nested J hJ hcard hfixed hq _ _ hBr hCr hcomm hc with h | h
  · exact Or.inl ((Subgroup.map_le_map_iff_of_injective e.injective).mp h)
  · exact Or.inr ((Subgroup.map_le_map_iff_of_injective e.injective).mp h)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity
