module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.GroupTheory.TwoLocalTransport
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Tactic.FinCases

/-!
# Automorphisms permute the two symplectic parabolic classes

Both full parabolics have the same order: their determinant kernels have
three-coordinate radicals and quotient SL₂, and both determinant characters
surject onto the field units. Each parabolic is a two-local. The fixed-radical
coverage theorem puts its image under any automorphism inside a conjugate
full parabolic; equality follows from the orders.

The resulting action is on the actual sets of conjugate subgroups. Its kernel
is precisely diagram preservation, and its carrier has at most two elements.
This does not require a graph generator or a separate nonconjugacy argument.

Source: GLS3, Theorem 2.5.12, `refs/KGroup/GLS3/chapter2.tex`; the restriction
needed in Aschbacher--Smith, `refs/quasithin.pdf`, printed p.510 and Remark
A.2.4 on p.33. The two-local and matrix ingredients are proved in the imported
symplectic modules, independently of automorphism classification.
-/

@[expose] public section

open Matrix
open scoped Pointwise
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def pointRadicalCoordinates : pointRadical (F := F) ≃ F × F × F where
  toFun q := (q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0),
    q.val.val.val (.inl 0) (.inr 0))
  invFun x := ⟨pointRadicalElement x.1 x.2.1 x.2.2, pointRadicalElement_mem _ _ _⟩
  left_inv q := Subtype.ext (pointRadical_eq_element q.val q.property).symm
  right_inv _ := rfl

private def symmetricCoordinates : Plane.symmetricMatrices F ≃ F × F × F where
  toFun B := (B.val 0 0, B.val 0 1, B.val 1 1)
  invFun x := ⟨!![x.1, x.2.1; x.2.1, x.2.2], by
    ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals try rfl
    exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) B.property).symm
  right_inv _ := rfl

private theorem card_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card H * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

omit [Finite F] in
/-- The full point and plane parabolics have the same order. -/
theorem card_pointParabolic_eq_card_planeParabolic :
    Nat.card (pointParabolic (F := F)) = Nat.card (planeParabolic (F := F)) := by
  have hrad : Nat.card (pointRadical (F := F)) = Nat.card (Plane.radical (F := F)) := by
    exact Nat.card_congr (pointRadicalCoordinates.trans
      (symmetricCoordinates.symm.trans
        (Multiplicative.ofAdd : Plane.symmetricMatrices F ≃ Multiplicative (Plane.symmetricMatrices F))
          |>.trans Plane.radicalEquiv.toEquiv.symm))
  have hlocal : Nat.card (pointLocal (F := F)) = Nat.card (planeLocal (F := F)) := by
    rw [card_of_surjective pointQuotient pointQuotient_surjective,
      card_of_surjective Plane.quotientMap Plane.quotientMap_surjective]
    exact congrArg (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * ·) hrad
  have hpoint : Function.Surjective (determinantCharacter (point F)) := by
    intro a
    exact ⟨⟨diagonalTorus a 1, (diagonalTorus_mem_borel a 1).1⟩,
      diagonalTorus_point_character a 1⟩
  have hplane : Function.Surjective (determinantCharacter (plane F)) := by
    intro a
    exact ⟨⟨diagonalTorus a 1, (diagonalTorus_mem_borel a 1).2⟩, by
      simpa using diagonalTorus_plane_character a 1⟩
  have hk (W : Submodule F (Vector F)) :
      Nat.card (determinantCharacter W).ker = Nat.card (determinantKernel W) :=
    (Subgroup.card_map_of_injective (stabilizer W).subtype_injective).symm
  change Nat.card (stabilizer (point F)) = Nat.card (stabilizer (plane F))
  rw [card_of_surjective _ hpoint, card_of_surjective _ hplane, hk, hk]
  exact congrArg (Nat.card Fˣ * ·) hlocal

/-- Every automorphism maps each actual full parabolic to a conjugate of
one of the two full parabolics. -/
theorem map_parabolic_eq_conjugate (hF : 2 < Nat.card F) (a : MulAut (Sp F))
    (P : Subgroup (Sp F)) (hP : P = pointParabolic ∨ P = planeParabolic) :
    ∃ Q : Subgroup (Sp F), (Q = pointParabolic ∨ Q = planeParabolic) ∧
      ∃ g : Sp F, P.map a.toMonoidHom = Q.map (MulAut.conj g).toMonoidHom := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hc : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 1 < (n : ℕ) := by
    by_contra h
    have hh : (n : ℕ) ≤ 1 := by omega
    have hh' : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hh
    rw [← hc] at hh'
    norm_num at hh'
    omega
  have hPlocal : IsTwoLocal P := by
    rcases hP with rfl | rfl
    · exact pointParabolic_isTwoLocal hc hn'
    · exact planeParabolic_isTwoLocal hc hn'
  obtain ⟨g, hg⟩ := twoLocal_parabolic_cover_of_charTwo
    (P.map a.toMonoidHom) (Theory.GroupTheory.isTwoLocal_map_aut hPlocal a)
  have hcard (Q : Subgroup (Sp F)) (hQ : Q = pointParabolic ∨ Q = planeParabolic) :
      Nat.card Q ≤ Nat.card ((P.map a.toMonoidHom).map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective a.injective]
    have hh := card_pointParabolic_eq_card_planeParabolic (F := F)
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl <;> omega
  have finish (Q : Subgroup (Sp F)) (hQ : Q = pointParabolic ∨ Q = planeParabolic)
      (hle : (P.map a.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ Q) :
      P.map a.toMonoidHom = Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    have heq := Subgroup.eq_of_le_of_card_ge hle (hcard Q hQ)
    have hh := congrArg (fun R : Subgroup (Sp F) => (MulAut.conj g⁻¹) • R) heq
    change (MulAut.conj g⁻¹) • ((MulAut.conj g) • (a • P)) =
      (MulAut.conj g⁻¹) • Q at hh
    change a • P = (MulAut.conj g⁻¹) • Q
    simpa only [map_inv, inv_smul_smul] using hh
  rcases hg with hp | hp
  · exact ⟨pointParabolic, Or.inl rfl, g⁻¹, finish _ (Or.inl rfl) hp⟩
  · exact ⟨planeParabolic, Or.inr rfl, g⁻¹, finish _ (Or.inr rfl) hp⟩


/-- The actual inner-conjugacy class of a subgroup, as a set of subgroups. -/
def subgroupConjugacyClass {G : Type*} [Group G] (P : Subgroup G) : Set (Subgroup G) :=
  Set.range (fun g : G => (MulAut.conj g) • P)

private theorem aut_conj_smul {G : Type*} [Group G] (a : MulAut G) (g : G)
    (P : Subgroup G) : a • ((MulAut.conj g) • P) = (MulAut.conj (a g)) • (a • P) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  ext x
  simp

private theorem smul_subgroupConjugacyClass {G : Type*} [Group G]
    (a : MulAut G) (P : Subgroup G) :
    a • subgroupConjugacyClass P = subgroupConjugacyClass (a • P) := by
  ext Q
  constructor
  · rintro ⟨R, ⟨g, rfl⟩, rfl⟩
    exact ⟨a g, (aut_conj_smul a g P).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨(MulAut.conj (a.symm g)) • P, ⟨a.symm g, rfl⟩, ?_⟩
    dsimp only
    rw [aut_conj_smul, a.apply_symm_apply]

private theorem subgroupConjugacyClass_conj {G : Type*} [Group G]
    (g : G) (P : Subgroup G) :
    subgroupConjugacyClass ((MulAut.conj g) • P) = subgroupConjugacyClass P := by
  ext Q
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, by dsimp only; rw [map_mul, mul_smul]⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    dsimp only
    rw [← mul_smul, ← map_mul, inv_mul_cancel_right]

private theorem subgroupConjugacyClass_self {G : Type*} [Group G] (P : Subgroup G) :
    P ∈ subgroupConjugacyClass P := by
  exact ⟨1, by dsimp only; rw [map_one, one_smul]⟩

/-- The automorphism-invariant family of the two actual parabolic classes. -/
def parabolicClasses (hF : 2 < Nat.card F) :
    SubMulAction (MulAut (Sp F)) (Set (Subgroup (Sp F))) where
  carrier := {C | C = subgroupConjugacyClass pointParabolic ∨
    C = subgroupConjugacyClass planeParabolic}
  smul_mem' a C hC := by
    have step (P : Subgroup (Sp F)) (hP : P = pointParabolic ∨ P = planeParabolic) :
        a • subgroupConjugacyClass P = subgroupConjugacyClass pointParabolic ∨
        a • subgroupConjugacyClass P = subgroupConjugacyClass planeParabolic := by
      obtain ⟨Q, hQ, g, hg⟩ := map_parabolic_eq_conjugate hF a P hP
      change a • P = (MulAut.conj g) • Q at hg
      rw [smul_subgroupConjugacyClass, hg, subgroupConjugacyClass_conj]
      rcases hQ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hC with rfl | rfl
    · exact step _ (Or.inl rfl)
    · exact step _ (Or.inr rfl)

/-- The family has at most two elements; no separate nonconjugacy assertion
is needed for the outer-quotient bound. -/
theorem card_parabolicClasses_le_two (hF : 2 < Nat.card F) :
    Nat.card (parabolicClasses hF) ≤ 2 := by
  let f : Bool → parabolicClasses hF := fun b =>
    if b then ⟨subgroupConjugacyClass pointParabolic, Or.inl rfl⟩ else
      ⟨subgroupConjugacyClass planeParabolic, Or.inr rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨C, hC⟩
    rcases hC with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  simpa using Nat.card_le_card_of_surjective f hf

/-- The permutation representation on the two parabolic conjugacy classes. -/
def parabolicClassAction (hF : 2 < Nat.card F) :
    MulAut (Sp F) →* Equiv.Perm (parabolicClasses hF) :=
  MulAction.toPermHom _ _

/-- Fixing both parabolic classes is exactly diagram preservation. -/
theorem mem_parabolicClassAction_ker_iff (hF : 2 < Nat.card F) (a : MulAut (Sp F)) :
    a ∈ (parabolicClassAction hF).ker ↔ PreservesDiagram a := by
  have fixed_iff (P : Subgroup (Sp F)) :
      a • subgroupConjugacyClass P = subgroupConjugacyClass P ↔
        PreservesParabolicClass a P := by
    rw [smul_subgroupConjugacyClass]
    constructor
    · intro h
      have hh := subgroupConjugacyClass_self (a • P)
      rw [h] at hh
      obtain ⟨g, hg⟩ := hh
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, hg⟩
      change a • P = (MulAut.conj g) • P at hg
      rw [hg, subgroupConjugacyClass_conj]
  constructor
  · intro ha
    have he : parabolicClassAction hF a = 1 := ha
    constructor
    · apply (fixed_iff pointParabolic).mp
      exact congrArg (fun p : Equiv.Perm (parabolicClasses hF) =>
        (p ⟨subgroupConjugacyClass pointParabolic, Or.inl rfl⟩).val) he
    · apply (fixed_iff planeParabolic).mp
      exact congrArg (fun p : Equiv.Perm (parabolicClasses hF) =>
        (p ⟨subgroupConjugacyClass planeParabolic, Or.inr rfl⟩).val) he
  · intro ha
    apply Equiv.ext
    rintro ⟨C, hC⟩
    apply Subtype.ext
    rcases hC with rfl | rfl
    · exact (fixed_iff pointParabolic).mpr ha.1
    · exact (fixed_iff planeParabolic).mpr ha.2

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
