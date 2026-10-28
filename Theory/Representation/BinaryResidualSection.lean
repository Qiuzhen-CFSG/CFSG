module
public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.SimpleHeadQuotient
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.Order.Atoms.Finite

/-!
# Detecting a binary residual on a simple section

A nontrivial action of a two-perfect subgroup survives on an irreducible
invariant subquotient. Choose a minimal moving subspace and a maximal
proper invariant subspace in it. If both layers were fixed, displacement
would give a homomorphism into an elementary two-group, which two-perfectness
kills. This also covers O² of solvable actors, where ordinary perfectness
would be an unjustified restriction.

Source application: DGS, Groups and Graphs (1985), proof of 10.7, p.159.
This extends the minimal-section argument in
QuadraticFourGroup/Recognition/IrreducibleReduction/Section.
-/

@[expose] public section
open Subgroup
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem twoPerfect_fixes_of_two_trivial_layers
    (L : Subgroup G) (hL : IsPPerfect 2 L) (U : Subrepresentation ρ)
    (hU : ∀ g ∈ L, ∀ u : U, ρ g u = u)
    (hQ : L ≤ U.quotientRepresentation.ker) : L ≤ ρ.ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  ext v
  have hd (x : L) : ρ x v - v ∈ U := by
    apply (Submodule.Quotient.eq U.toSubmodule).mp
    have he := DFunLike.congr_fun (hQ x.property) (U.toSubmodule.mkQ v)
    exact he
  let d : L →* Multiplicative V := {
    toFun x := Multiplicative.ofAdd (ρ x v - v)
    map_one' := by simp
    map_mul' x y := by
      change ρ ((x : G) * y) v - v = (ρ x v - v) + (ρ y v - v)
      have he := hU x x.property ⟨ρ y v - v, hd y⟩
      change ρ x (ρ y v - v) = ρ y v - v at he
      rw [map_sub] at he
      rw [map_mul, Module.End.mul_apply]
      calc
        _ = (ρ x (ρ y v) - ρ x v) + (ρ x v - v) := by abel
        _ = _ := by rw [he]; abel
  }
  have he : d ⟨g, hg⟩ = 1 := DFunLike.congr_fun
    (hL.hom_eq_one_of_isPGroup (ZModModule.isPGroup_multiplicative (n := 2)) d) ⟨g,hg⟩
  exact sub_eq_zero.mp (show ρ g v - v = 0 from he)

/-- A nontrivial two-perfect action survives on an actual irreducible subquotient. -/
theorem exists_irreducible_section_surviving_twoPerfect
    [FiniteDimensional (ZMod 2) V]
    (L : Subgroup G) (hL : IsPPerfect 2 L) (hne : ¬ L ≤ ρ.ker) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧ ¬ L ≤ N.quotientRepresentation.ker := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun U : Subrepresentation ρ => (U : Set V)) SetLike.coe_injective
  let P : Subrepresentation ρ → Prop := fun U => ¬ ∀ g ∈ L, ∀ u : U, ρ g u = u
  have hP : ∃ U, P U := by
    refine ⟨⊤, ?_⟩
    intro he
    apply hne
    intro g hg
    rw [MonoidHom.mem_ker]
    ext v
    exact he g hg ⟨v, by trivial⟩
  obtain ⟨U, hU, hmin⟩ := (inferInstance : WellFoundedLT (Subrepresentation ρ)).exists_minimal
    {U | P U} hP
  have hUne : U.toSubmodule ≠ ⊥ := by
    intro he
    apply hU
    intro g hg u
    have hu : (u : V) ∈ U.toSubmodule := u.property
    rw [he, Submodule.mem_bot] at hu
    simp [hu]
  let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  let : Finite (Subrepresentation U.toRepresentation) :=
    Finite.of_injective (fun N : Subrepresentation U.toRepresentation => (N : Set U))
      SetLike.coe_injective
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation U.toRepresentation)
  refine ⟨U, N, SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN, ?_⟩
  intro hQ
  let T : Subrepresentation ρ := {
    toSubmodule := N.toSubmodule.map U.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := by
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨U.toRepresentation g u, N.apply_mem_toSubmodule g hu, rfl⟩
  }
  have hTU : T ≤ U := Submodule.map_subtype_le _ _
  have hTne : T ≠ U := by
    intro he
    apply hN.1
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro u _
    obtain ⟨v, hv, hvu⟩ := (show (u : V) ∈ T from he.symm ▸ u.property)
    exact (Subtype.ext hvu : v = u) ▸ hv
  have hT : ∀ g ∈ L, ∀ t : T, ρ g t = t := by
    by_contra hn
    exact hTne (le_antisymm hTU (hmin hn hTU))
  have hNfix : ∀ g ∈ L, ∀ u : N, U.toRepresentation g u = u := by
    intro g hg u
    apply Subtype.ext
    exact hT g hg ⟨u, ⟨u, u.property, rfl⟩⟩
  have hker := twoPerfect_fixes_of_two_trivial_layers L hL N hNfix hQ
  apply hU
  intro g hg u
  exact congrArg Subtype.val (DFunLike.congr_fun (hker hg) u)


end Representation
