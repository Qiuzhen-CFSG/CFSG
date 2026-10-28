module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates
public import Theory.Representation.G2.RestrictedModules.NaturalHighestWeight

/-!
# The adjoint highest weight of G₂ in characteristic two

The common fixed space of E(1), F(1), and C(1) is the line of the zeroth
coordinate derivation. Separately, all six positive root groups fix that vector
at every parameter, identifying the fixed line of the whole positive unipotent
subgroup. Its torus character is l*m, with short/long coroot pairings (0,1).
The fourteen reconstructed derivations supply an explicit basis and weight table.

Source: GLS3, Examples 1.14.9(c) and 2.8.10(g). The marked coroots are those
verified in NaturalHighestWeight: Wilson F is short and Wilson E is long.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Restricted.Adjoint.Coordinates
variable (F : Type*) [Field F] [CharP F 2]
/-- A nonzero vector on the adjoint highest line. -/
def highestVector : Space F := Pi.single 0 1

omit [CharP F 2] in
theorem highestVector_ne_zero : highestVector F ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [highestVector] at this

/-- All six positive root subgroups fix the highest vector. -/
theorem highestVector_fixed_roots (a : F) :
    action F (rootA a) (highestVector F) = highestVector F ∧
    action F (rootB a) (highestVector F) = highestVector F ∧
    action F (rootC a) (highestVector F) = highestVector F ∧
    action F (rootD a) (highestVector F) = highestVector F ∧
    action F (rootE a) (highestVector F) = highestVector F ∧
    action F (rootF a) (highestVector F) = highestVector F := by
  simp only [action_rootA, action_rootB, action_rootC, action_rootD, action_rootE,
    action_rootF, highestVector]
  constructor
  · ext i; fin_cases i <;> simp
  constructor
  · ext i; fin_cases i <;> simp
  constructor
  · ext i; fin_cases i <;> simp
  constructor
  · ext i; fin_cases i <;> simp
  constructor <;> ext i <;> fin_cases i <;> simp

/-- The complete positive unipotent group fixes the highest vector. -/
theorem highestVector_fixed_unipotentProduct (t : Fin 6 → F) :
    action F (unipotentProduct t) (highestVector F) = highestVector F := by
  simp only [unipotentProduct, map_mul, Module.End.mul_apply]
  rw [(highestVector_fixed_roots F _).2.2.2.2.2,
    (highestVector_fixed_roots F _).2.2.2.2.1,
    (highestVector_fixed_roots F _).2.2.2.1,
    (highestVector_fixed_roots F _).2.2.1,
    (highestVector_fixed_roots F _).2.1,
    (highestVector_fixed_roots F _).1]

/-- Three unit-valued root elements already determine the highest line. -/
theorem fixed_threeRoots_iff (v : Space F) :
    (action F (rootE 1) v = v ∧ action F (rootF 1) v = v ∧
      action F (rootC 1) v = v) ↔ ∃ a : F, v = a • highestVector F := by
  constructor
  · rintro ⟨hE, hF, hC⟩
    have h1 : v 1 = 0 := by simpa using congrFun hE 0
    have h7 : v 7 = 0 := by simpa using congrFun hE 4
    have h5 : v 5 = 0 := by simpa using congrFun hE 6
    have h8 : v 8 = 0 := by simpa using congrFun hE 9
    have h11 : v 11 = 0 := by simpa using congrFun hE 12
    have h13 : v 13 = 0 := by simpa [h5] using congrFun hE 3
    have h3 : v 3 = 0 := by simpa using congrFun hF 2
    have h9 : v 9 = 0 := by simpa using congrFun hF 10
    have h10 : v 10 = 0 := by simpa [h9, h11] using congrFun hF 5
    have h12 : v 12 = 0 := by simpa using congrFun hF 6
    have h6 : v 6 = 0 := by simpa [h12, h13] using congrFun hF 7
    have h4 : v 4 = 0 := by simpa [h9, h12] using congrFun hC 0
    have h2 : v 2 = 0 := by simpa [h3, h4] using congrFun hF 1
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [highestVector, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, h12, h13]
  · rintro ⟨a, rfl⟩
    simp only [map_smul, (highestVector_fixed_roots F 1).2.2.2.2.1,
      (highestVector_fixed_roots F 1).2.2.2.2.2,
      (highestVector_fixed_roots F 1).2.2.1, and_self]

/-- Every element of the positive unipotent subgroup fixes the highest vector. -/
theorem highestVector_fixed_unipotent (g : Model F) (hg : g ∈ unipotent) :
    action F g (highestVector F) = highestVector F := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  exact highestVector_fixed_unipotentProduct F t

/-- The full positive unipotent fixed space is exactly the highest line. -/
theorem fixed_unipotent_iff (v : Space F) :
    (∀ g ∈ (unipotent : Subgroup (Model F)), action F g v = v) ↔
      ∃ a : F, v = a • highestVector F := by
  constructor
  · intro h
    apply (fixed_threeRoots_iff F v).mp
    exact ⟨h _ (Subgroup.subset_closure (by simp)),
      h _ (Subgroup.subset_closure (by simp)), h _ (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨a, rfl⟩ g hg
    rw [map_smul, highestVector_fixed_unipotent F g hg]

/-- The highest weight is the torus character l*m. -/
theorem highestVector_torus (l m : Fˣ) :
    action F (torus l m) (highestVector F) = ((l*m : Fˣ) : F) • highestVector F := by
  ext i
  fin_cases i <;> simp [highestVector, torusWeights]

/-- Short-coroot pairing zero for GLS3's λ₁. -/
theorem highestVector_shortCoroot (t : Fˣ) :
    action F (shortCoroot t) (highestVector F) = highestVector F := by
  simpa [shortCoroot] using highestVector_torus F t t⁻¹

/-- Long-coroot pairing one for GLS3's λ₁. -/
theorem highestVector_longCoroot (t : Fˣ) :
    action F (longCoroot t) (highestVector F) = (t : F) • highestVector F := by
  simpa [longCoroot] using highestVector_torus F 1 t
end Atlas.G2.Restricted.Adjoint.Coordinates

noncomputable section
namespace Atlas.G2.Restricted.Adjoint
variable (F : Type*) [Field F] [CharP F 2]
/-- The fourteen explicit derivations form a basis of the actual adjoint space. -/
def basis : Module.Basis (Fin 14) F (Space F) :=
  (Pi.basisFun F (Fin 14)).map (Coordinates.equiv F).symm
@[simp] theorem basis_apply (i : Fin 14) :
    basis F i = Coordinates.fromParams F (Pi.single i 1) := by
  simp [basis, Pi.basisFun_apply]
/-- Each explicit basis derivation has exactly one nonzero parameter. -/
@[simp] theorem basis_coordinates (i : Fin 14) :
    Coordinates.equiv F (basis F i) = Pi.single i 1 := by
  rw [basis_apply, Coordinates.equiv_apply, Coordinates.params_fromParams]
/-- The explicit highest derivation. -/
def highestVector : Space F := Coordinates.fromParams F (Coordinates.highestVector F)
@[simp] theorem equiv_highestVector :
    Coordinates.equiv F (highestVector F) = Coordinates.highestVector F :=
  Coordinates.params_fromParams F _
/-- Coordinates intertwine the actual conjugation action. -/
theorem equiv_action (g : Model F) (D : Space F) :
    Coordinates.equiv F (action F g D) =
      Coordinates.action F g (Coordinates.equiv F D) := by
  change Coordinates.equiv F (action F g D) =
    Coordinates.equiv F (action F g ((Coordinates.equiv F).symm (Coordinates.equiv F D)))
  rw [LinearEquiv.symm_apply_apply]
/-- The full weight table on the actual derivation basis. -/
theorem basis_torus (l m : Fˣ) (i : Fin 14) :
    action F (torus l m) (basis F i) =
      (Coordinates.torusWeights F l m i : F) • basis F i := by
  apply (Coordinates.equiv F).injective
  rw [equiv_action, map_smul, basis_coordinates, Coordinates.action_torus]
  ext j
  by_cases h : i = j
  · subst j
    simp
  · simp [Ne.symm h]
/-- On the octonions the highest vector sends x to [x₆,x₇,0,0,0,0,0,0]. -/
theorem highestVector_apply (x : Atlas.SplitOctonion.Carrier F) :
    (highestVector F).val x = ![x 6, x 7, 0, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;>
    simp [highestVector, Coordinates.endomorphism, Coordinates.highestVector]
/-- The highest derivation is nonzero. -/
theorem highestVector_ne_zero : highestVector F ≠ 0 := by
  intro h
  apply Coordinates.highestVector_ne_zero F
  simpa only [equiv_highestVector, map_zero] using congrArg (Coordinates.equiv F) h
private theorem highestVector_action_iff (g : Model F) (a : F) :
    action F g (highestVector F) = a • highestVector F ↔
      Coordinates.action F g (Coordinates.highestVector F) = a • Coordinates.highestVector F := by
  rw [← (Coordinates.equiv F).injective.eq_iff]
  rw [equiv_action, map_smul, equiv_highestVector]
/-- All six positive root groups, at every parameter, fix the actual highest derivation. -/
theorem highestVector_fixed_roots (a : F) :
    action F (rootA a) (highestVector F) = highestVector F ∧
    action F (rootB a) (highestVector F) = highestVector F ∧
    action F (rootC a) (highestVector F) = highestVector F ∧
    action F (rootD a) (highestVector F) = highestVector F ∧
    action F (rootE a) (highestVector F) = highestVector F ∧
    action F (rootF a) (highestVector F) = highestVector F := by
  have h (g : Model F) (hg : Coordinates.action F g (Coordinates.highestVector F) =
      Coordinates.highestVector F) : action F g (highestVector F) = highestVector F := by
    simpa only [one_smul] using (highestVector_action_iff F g 1).mpr (by simpa using hg)
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ := Coordinates.highestVector_fixed_roots F a
  exact ⟨h _ hA, h _ hB, h _ hC, h _ hD, h _ hE, h _ hF⟩
/-- Every positive unipotent element fixes the highest derivation. -/
theorem highestVector_fixed_unipotent (g : Model F) (hg : g ∈ unipotent) :
    action F g (highestVector F) = highestVector F := by
  apply (Coordinates.equiv F).injective
  rw [equiv_action, equiv_highestVector]
  exact Coordinates.highestVector_fixed_unipotent F g hg
/-- The positive unipotent fixed space in the actual adjoint module is the highest line. -/
theorem fixed_unipotent_iff (D : Space F) :
    (∀ g ∈ (unipotent : Subgroup (Model F)), action F g D = D) ↔
      ∃ a : F, D = a • highestVector F := by
  constructor
  · intro h
    have hc : ∀ g ∈ (unipotent : Subgroup (Model F)),
        Coordinates.action F g (Coordinates.equiv F D) = Coordinates.equiv F D := by
      intro g hg
      rw [← equiv_action, h g hg]
    obtain ⟨a, ha⟩ := (Coordinates.fixed_unipotent_iff F _).mp hc
    refine ⟨a, (Coordinates.equiv F).injective ?_⟩
    simpa only [map_smul, equiv_highestVector] using ha
  · rintro ⟨a, rfl⟩ g hg
    rw [map_smul, highestVector_fixed_unipotent F g hg]
/-- Highest torus character l*m on genuine derivations. -/
theorem highestVector_torus (l m : Fˣ) :
    action F (torus l m) (highestVector F) = ((l*m : Fˣ) : F) • highestVector F :=
  (highestVector_action_iff F _ _).mpr (Coordinates.highestVector_torus F l m)
/-- Short-coroot pairing zero. -/
theorem highestVector_shortCoroot (t : Fˣ) :
    action F (shortCoroot t) (highestVector F) = highestVector F := by
  simpa [shortCoroot] using highestVector_torus F t t⁻¹
/-- Long-coroot pairing one: this is GLS3's λ₁. -/
theorem highestVector_longCoroot (t : Fˣ) :
    action F (longCoroot t) (highestVector F) = (t : F) • highestVector F := by
  simpa [longCoroot] using highestVector_torus F 1 t
end Atlas.G2.Restricted.Adjoint
