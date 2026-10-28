module

public import Theory.GroupTheory.DirectProduct.DihedralMaximalSplitting
public import Theory.SpecificGroups.SymmetricFourSylow

/-!
# The abelian remainder in a symmetric-four direct product

Let B be a finite two-group and P a Sylow two-subgroup of S₄ × B.
If no nontrivial characteristic subgroup of P is normal in S₄ × B,
then a maximal splitting of B into D₈ factors has an abelian remainder.
Indeed P is a product of a dihedral Sylow subgroup of S₄ and B.
A characteristic subgroup lying inside B is ambient-normal: conjugation
by S₄ is trivial there, and conjugation by B is already conjugation by P.
This discharges the hypothesis of the specialized factor-extraction argument.

Source: Goldschmidt, Automorphisms of Trivalent Graphs (1980), (2.14),
printed p.385, the characteristic derived-remainder step.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.DihedralFactorExtraction

private abbrev S₄ := Equiv.Perm (Fin 4)

/-- A characteristic subgroup of the Sylow product contained in its B
factor is ambient-normal, so the original characteristic obstruction kills it. -/
theorem symmetricFour_characteristic_remainder_eq_bot (B : Type*) [Group B] [Finite B]
    (hB : IsPGroup 2 B) (P : Sylow 2 (Equiv.Perm (Fin 4) × B))
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup (Equiv.Perm (Fin 4) × B)).subtype).Normal) :
    ∀ K : Subgroup (DihedralGroup 4 × B), K.Characteristic →
      K ≤ (⊥ : Subgroup (DihedralGroup 4)).prod ⊤ → K = ⊥ := by
  classical
  let A : Subgroup (S₄ × B) := (⊥ : Subgroup S₄).prod ⊤
  have hA : IsPGroup 2 A := hB.of_injective
    ((MonoidHom.snd S₄ B).comp A.subtype) (by
      intro x y hxy
      apply Subtype.ext
      exact Prod.ext (x.property.1.trans y.property.1.symm) hxy)
  have hAP : A ≤ P := hA.le_sylow_of_normal P
  let T : Sylow 2 S₄ := P.mapSurjective (f := MonoidHom.fst S₄ B)
    (fun a => ⟨(a,1),rfl⟩)
  have hprod : (P : Subgroup (S₄ × B)) = (T : Subgroup S₄).prod ⊤ := by
    apply le_antisymm
    · intro x hx
      exact ⟨⟨x,hx,rfl⟩,mem_top _⟩
    · rintro ⟨a,b⟩ ⟨ha,_⟩
      obtain ⟨⟨a₀,b₀⟩,hx,he⟩ := ha
      change a₀ = a at he
      subst a₀
      have hh : (1,b₀⁻¹*b) ∈ P := hAP ⟨one_mem _,mem_top _⟩
      simpa using mul_mem hx hh
  obtain ⟨t⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four T
  let e : P ≃* DihedralGroup 4 × B :=
    (MulEquiv.subgroupCongr hprod).trans ((prodEquiv (T : Subgroup S₄) ⊤).trans
      (MulEquiv.prodCongr t (topEquiv : (⊤ : Subgroup B) ≃* B)))
  intro K hK hKB
  let L : Subgroup P := K.comap e.toMonoidHom
  have hL : L.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    have hh := characteristic_iff_le_comap.mp hK (MulAut.congr e a) hx
    change e.toMonoidHom (a x) ∈ K
    simpa [MulAut.congr] using hh
  have hfirst (x : P) (hx : x ∈ L) : (x : S₄ × B).1 = 1 := by
    have hh : (e x).1 = 1 := (hKB hx).1
    have he : t ⟨(x : S₄ × B).1,⟨x,x.property,rfl⟩⟩ = 1 := hh
    have he' := t.injective (he.trans t.map_one.symm)
    exact congrArg Subtype.val he'
  have hnormal : (L.map (P : Subgroup (S₄ × B)).subtype).Normal := by
    let _ : L.Characteristic := hL
    refine ⟨?_⟩
    intro x hx g
    obtain ⟨x₀,hx₀,rfl⟩ := hx
    let b : P := ⟨(1,g.2),hAP ⟨one_mem _,mem_top _⟩⟩
    refine ⟨b*x₀*b⁻¹,(inferInstance : L.Normal).conj_mem x₀ hx₀ b,?_⟩
    apply Prod.ext
    · simp [b,hfirst x₀ hx₀]
    · rfl
  have hLbot : L = ⊥ := by
    by_contra hh
    exact hP L hL hh hnormal
  apply bot_unique
  intro x hx
  have he : e.symm x ∈ L := by
    change e (e.symm x) ∈ K
    simpa using hx
  have hh : e.symm x = 1 := hLbot.le he
  exact (e.symm.injective (hh.trans e.symm.map_one.symm))

/-- In the literal S₄ × B model, the original absence of characteristic
ambient-normal subgroups makes the maximally split two-group remainder abelian. -/
theorem symmetricFour_exists_abelian_remainder (B : Type*) [Group B] [Finite B]
    (hB : IsPGroup 2 B) (P : Sylow 2 (Equiv.Perm (Fin 4) × B))
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup (Equiv.Perm (Fin 4) × B)).subtype).Normal) :
    ∃ n : ℕ, ∃ R : Subgroup B,
      Nonempty (B ≃* (Fin n → DihedralGroup 4) × R) ∧ IsMulCommutative R :=
  exists_abelian_remainder B (symmetricFour_characteristic_remainder_eq_bot B hB P hP)

end Theory.GroupTheory.DihedralFactorExtraction
