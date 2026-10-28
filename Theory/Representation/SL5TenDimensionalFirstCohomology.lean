module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.Quotient
public import Mathlib.RepresentationTheory.Irreducible

/-!
# First cohomology of ten-dimensional irreducible SL₅(2) modules

Every ten-dimensional irreducible binary SL₅(2) module has trivial first
cohomology. The exhaustive classification identifies it with the second or
third exterior power of the natural module. Both model calculations express
every crossed homomorphism as principal, and representation equivalences
transport their vanishing to the original module.

The canonical quotient isomorphism SL₅(2) ≃ PSL₅(2) gives the same conclusion
for the literal projective carrier. No finite-dimensionality assumption beyond
finrank ten is needed. The earlier conditional assembly interfaces are retained.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419, citing Jones--Parshall [JP76].
-/

@[expose] public section

namespace Representation.SL5TenDimensional
open OneCohomology

/-- A calculation expressing every crossed homomorphism as principal proves H¹ = 0. -/
theorem h1_subsingleton_of_cocycles_principal (r : ℕ)
    (h : ∀ f : cocycles (exteriorAction r), ∃ v, principal (exteriorAction r) v = f) :
    Subsingleton (H1 (exteriorAction r)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact LinearMap.range_eq_top.mpr h

/-- Transport vanishing from an exterior-power model along a representation equivalence. -/
theorem h1_subsingleton_of_equiv_exterior
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (r : ℕ)
    (e : ρ.Equiv (exteriorAction r))
    [Subsingleton (H1 (exteriorAction r))] : Subsingleton (H1 ρ) := by
  let eH := H1Congr ρ (exteriorAction r) (MulEquiv.refl Group) e.toLinearEquiv
    (fun g v => DFunLike.congr_fun (e.toIntertwiningMap.isIntertwining' g) v)
  exact eH.injective.subsingleton

/-- Combine the two model calculations for any explicitly identified module. -/
theorem h1_subsingleton_of_model_identification
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V)
    (hid : Nonempty (ρ.Equiv (exteriorAction 2)) ∨ Nonempty (ρ.Equiv (exteriorAction 3)))
    (h2 : Subsingleton (H1 (exteriorAction 2)))
    (h3 : Subsingleton (H1 (exteriorAction 3))) : Subsingleton (H1 ρ) := by
  rcases hid with h | h
  · obtain ⟨e⟩ := h
    let := h2
    exact h1_subsingleton_of_equiv_exterior ρ 2 e
  · obtain ⟨e⟩ := h
    let := h3
    exact h1_subsingleton_of_equiv_exterior ρ 3 e

/-- Every ten-dimensional irreducible binary SL₅(2) module has trivial H¹.
The exhaustive identification and both exterior-power calculations are discharged. -/
theorem h1_subsingleton_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [IsIrreducible ρ]
    (hdim : Module.finrank (ZMod 2) V = 10) : Subsingleton (H1 ρ) :=
  h1_subsingleton_of_model_identification ρ
    (Classification.identification_of_finrank_ten ρ hdim)
    exteriorSquare_h1_subsingleton exteriorCube_h1_subsingleton

/-- The dimension-zero formulation of I.1.6(7) on SL₅(2). -/
theorem finrank_h1_eq_zero_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [IsIrreducible ρ]
    (hdim : Module.finrank (ZMod 2) V = 10) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  let := h1_subsingleton_of_finrank_ten ρ hdim
  exact Module.finrank_zero_of_subsingleton

/-- Vanishing for an arbitrary group explicitly identified with SL₅(2).
Pullback preserves the invariant-subspace lattice and transports H¹. -/
theorem h1_subsingleton_of_group_equiv
    {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (e : G ≃* Group) (hdim : Module.finrank (ZMod 2) V = 10) :
    Subsingleton (H1 ρ) := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr
      inferInstance
  let := h1_subsingleton_of_finrank_ten σ hdim
  exact (H1Congr ρ σ e (LinearEquiv.refl (ZMod 2) V) (fun g v => by
    change ρ g v = ρ (e.symm (e g)) v
    rw [e.symm_apply_apply])).injective.subsingleton

/-- I.1.6(7) on the literal L₅(2) = PSL₅(2) carrier, using the canonical
quotient isomorphism proved in `Models`. -/
theorem projective_h1_subsingleton_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) V)
    [IsIrreducible ρ] (hdim : Module.finrank (ZMod 2) V = 10) :
    Subsingleton (H1 ρ) :=
  h1_subsingleton_of_group_equiv ρ projectiveEquiv.symm hdim

/-- The source dimension-zero conclusion for every ten-dimensional irreducible
binary L₅(2) module. -/
theorem projective_finrank_h1_eq_zero_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) V)
    [IsIrreducible ρ] (hdim : Module.finrank (ZMod 2) V = 10) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  let := projective_h1_subsingleton_of_finrank_ten ρ hdim
  exact Module.finrank_zero_of_subsingleton

end Representation.SL5TenDimensional
