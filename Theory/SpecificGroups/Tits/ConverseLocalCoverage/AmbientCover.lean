module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.Representatives
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover

/-!
# A finite input set for the Tits double-coset certificate

Transport the certified 1755-coset cover through the actual Parrott–Atlas
isomorphism and then use the five-coset cover of the first parabolic.
This gives 8775 explicit representatives modulo left Sylow factors.
Consequently a double-coset certificate need only place these finitely
many elements in the eighteen proposed double cosets.

Source: Parrott (1972), §5, p.683; the ambient cover and local normal forms
are independently certified in the imported modules.
-/

@[expose] public section
namespace Tits.ConverseLocalCoverage
open Subgroup ExceptionalParabolics Theory.GroupTheory.CosetEnumeration
open OuterOddSubgroups.OverlapCentralizers

/-- The explicit representative set from the two established coset covers. -/
noncomputable def ambientRep (i : Fin 1755) (j : Fin 5) : Atlas1600Group :=
  firstRotation ^ j.val * eval atlas1600ParrottAssignment
    (R1Certificate.input.reps.getD (R1Certificate.index i) [])

private theorem mapped_eval (w : Word ParrottGenerator) :
    parrottFiniteImageEquiv (eval parrottGenerator w) =
      eval atlas1600ParrottAssignment w := by
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b <;> simp [letterValue]

set_option maxRecDepth 30000 in
private theorem concrete_covers (x : ParrottGroup) :
    ∃ h : parrottR1Subgroup, ∃ i : Fin 1755,
      x = h.val * representative parrottGenerator R1Certificate.input
        (R1Certificate.index i) := by
  let C : ParrottR1CosetCover := {
    rep := fun i => representative parrottGenerator R1Certificate.input (R1Certificate.index i)
    initial := R1Certificate.initial
    initial_eq := by simp [representative, R1Certificate.initial_index, R1Certificate.model.zero]
    step := fun a => tablePermutation R1Certificate.table R1Certificate.inverse_table (a, true)
    transition := fun i a => by
      simpa only [Fact.Valid, Related, eval_singleton, letterValue, ↓reduceIte,
        tablePermutation, Equiv.coe_fn_mk] using R1Certificate.edges i a }
  exact C.covers x

/-- The established finite cover, retaining bounded representative indices. -/
theorem ambient_cover (x : Atlas1600Group) :
    ∃ (s : S) (i : Fin 1755) (j : Fin 5), x = s.val * ambientRep i j := by
  obtain ⟨h, i, he⟩ := concrete_covers (parrottFiniteImageEquiv.symm x)
  have hxform : x = parrottFiniteImageEquiv h.val * parrottFiniteImageEquiv
      (representative parrottGenerator R1Certificate.input (R1Certificate.index i)) := by
    rw [← map_mul, ← he, MulEquiv.apply_symm_apply]
  have hh : parrottFiniteImageEquiv h.val ∈ first := by
    rw [← ReeLocalBlockOrders.first_map]
    exact mem_map_of_mem _ h.property
  obtain ⟨⟨n, j⟩, hnj⟩ := firstNormalForm_surjective ⟨parrottFiniteImageEquiv h.val, hh⟩
  have hnf := congrArg Subtype.val hnj
  change atlas1600SylowTwoNormalForm n * firstRotation ^ j.val =
    parrottFiniteImageEquiv h.val at hnf
  refine ⟨⟨atlas1600SylowTwoNormalForm n, atlas1600SylowTwoNormalForm_mem n⟩, i, j, ?_⟩
  rw [hxform, ← hnf, representative, mapped_eval]
  exact mul_assoc _ _ _

/-- Checking the 8775 explicit representatives suffices for double-coset coverage. -/
theorem doubleCoset_cover_of_ambient
    (h : ∀ (i : Fin 1755) (j : Fin 5), ∃ (a b : S) (k : Fin 18),
      ambientRep i j = a.val * doubleCosetRep k * b.val)
    (x : Atlas1600Group) : ∃ (a b : S) (k : Fin 18),
      x = a.val * doubleCosetRep k * b.val := by
  obtain ⟨s, i, j, he⟩ := ambient_cover x
  obtain ⟨a, b, k, hk⟩ := h i j
  refine ⟨s * a, b, k, ?_⟩
  change x = (s.val * a.val) * doubleCosetRep k * b.val
  rw [he, hk]
  simp only [mul_assoc]

end Tits.ConverseLocalCoverage
end
