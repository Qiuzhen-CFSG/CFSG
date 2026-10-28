module

public import Theory.Representation.Mathieu.M23DegreeSpectrum
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.Defs
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration

/-!
# Small simple quotients of the M23 point-module inductions

Change-of-marking intertwiners and finite contragredient duality transfer a
filtration of the canonical cocode induction to every induction in `Models`.
Every maximal quotient occurs among the simple factors of that filtration,
so factors of degrees 11, 44 and 120 give the requested small-head bound.
The final theorem applies this bound to the actual ten-dimensional point
submodule in the parent spectrum reduction.

The canonical cocode filtration is proved by the imported native-action and
matrix certificates. Substituting it gives the unconditional
`smallInducedHeads` and discharges the head premise in
`InducedHeads.finrank_eq_eleven_of_point_ten`. The conditional interfaces remain
available, and irreducibility is over F2 throughout.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M23 paragraph, manuscript p.16; Theorem 6.6/Table 6.7.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M23DegreeSpectrum
namespace InducedHeads

/-- Duality reverses the filtration without changing its simple-factor degrees. -/
theorem coordinateFiltration_code_of_cocode (e : Models.pointGroup ≃* M22) {D : Set ℕ}
    (h : FactorDegreeFiltration D (Coordinates.action e false)) :
    FactorDegreeFiltration D (Coordinates.action e true) :=
  h.dual.of_equiv (coordinateDualEquiv e).symm

/-- One canonical cocode filtration supplies both orientations and every marking. -/
theorem coordinateFiltration_of_canonical {D : Set ℕ}
    (h : FactorDegreeFiltration D canonicalCocodeAction)
    (e : Models.pointGroup ≃* M22) (b : Bool) :
    FactorDegreeFiltration D (Coordinates.action e b) := by
  have he : FactorDegreeFiltration D (Coordinates.action e false) :=
    h.of_equiv (coordinateMarkingEquiv canonicalMarking e false)
  cases b
  · exact he
  · exact coordinateFiltration_code_of_cocode e he

/-- The filtration controls literal maximal quotients of the original induction. -/
theorem quotient_finrank_mem_of_coordinateFiltration
    (e : Models.pointGroup ≃* M22) (b : Bool) {D : Set ℕ}
    (h : FactorDegreeFiltration D (Coordinates.action e b))
    (N : Subrepresentation (Models.induced e b)) (hN : IsCoatom N) :
    Module.finrank (ZMod 2) (Models.InducedSpace e b ⧸ N.toSubmodule) ∈ D := by
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  let q : (Models.induced e b).IntertwiningMap N.quotientRepresentation :=
    ⟨N.toSubmodule.mkQ, fun _ => rfl⟩
  let f := q.comp (Coordinates.inducedEquiv e b).symm.toIntertwiningMap
  apply h.finrank_mem f
  intro hf
  let : Nontrivial (Models.InducedSpace e b ⧸ N.toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial N.quotientRepresentation
  obtain ⟨x, hx⟩ := exists_ne (0 : Models.InducedSpace e b ⧸ N.toSubmodule)
  obtain ⟨v, hv⟩ := N.toSubmodule.mkQ_surjective x
  have hz := congrArg (fun t => t (Coordinates.inducedEquiv e b v)) hf
  change q ((Coordinates.inducedEquiv e b).symm (Coordinates.inducedEquiv e b v)) = 0 at hz
  rw [Representation.Equiv.symm_apply_apply] at hz
  exact hx (hv.symm.trans hz)

end InducedHeads

/-- The concrete canonical filtration discharges the full marked head premise. -/
theorem smallInducedHeads_of_cocodeFiltration
    (h : FactorDegreeFiltration InducedHeads.factorDegrees
      InducedHeads.canonicalCocodeAction) : SmallInducedHeads := by
  intro e b N hN
  have hd := InducedHeads.quotient_finrank_mem_of_coordinateFiltration e b
    (InducedHeads.coordinateFiltration_of_canonical h e b) N hN
  simp only [InducedHeads.factorDegrees, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  omega

/-- Apply the calculation to the actual recognized ten-dimensional point
submodule, using the original induced surjection in the parent reduction. -/
theorem finrank_eq_eleven_of_point_ten_of_cocodeFiltration
    (h : FactorDegreeFiltration InducedHeads.factorDegrees
      InducedHeads.canonicalCocodeAction)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 24)
    (S : Subrepresentation (pointRestriction ρ)) [S.toRepresentation.IsIrreducible]
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 10) :
    Module.finrank (ZMod 2) V = 11 :=
  finrank_eq_eleven_of_point_ten (smallInducedHeads_of_cocodeFiltration h) ρ hd S hS

/-- Every maximal quotient of either native point-module induction, with any
actual M22 marking, has binary dimension eleven or greater than 24. -/
theorem smallInducedHeads : SmallInducedHeads :=
  smallInducedHeads_of_cocodeFiltration InducedHeads.canonicalCocodeFiltration

/-- Apply the proved induced-head bound to the literal ten-dimensional point
submodule in the parent spectrum reduction, with no filtration premise. -/
theorem InducedHeads.finrank_eq_eleven_of_point_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 24)
    (S : Subrepresentation (pointRestriction ρ)) [S.toRepresentation.IsIrreducible]
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 10) :
    Module.finrank (ZMod 2) V = 11 :=
  M23DegreeSpectrum.finrank_eq_eleven_of_point_ten smallInducedHeads ρ hd S hS

end Representation.MathieuSmall.M23DegreeSpectrum
