module
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Image
public import Mathlib.Order.Atoms.Finite

/-!
# An irreducible section detecting a perfect subgroup

Choose a minimal invariant subspace on which the perfect subgroup acts
nontrivially, then quotient by a maximal proper invariant subspace. The
quotient is irreducible. If it were centralized, the subgroup would centralize
both layers; each displacement would then be a homomorphism to an abelian
group, contradicting perfectness and the choice of the subspace.

Applied to the component in a faithful quadratic four-group representation,
this constructs a literal invariant subquotient on which the component
survives. No faithfulness of individual composition factors is assumed.

Source: GLS, volume 2, Theorem 25.14, Step 2, choice of W.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem perfect_fixes_of_two_trivial_layers
    (L : Subgroup G) [Group.IsPerfect L] (U : Subrepresentation ρ)
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
  have he : d ⟨g, hg⟩ = 1 := Abelianization.commutator_subset_ker d
    (Group.IsPerfect.mem_commutator (g := (⟨g, hg⟩ : L)))
  exact sub_eq_zero.mp (show ρ g v - v = 0 from he)

private theorem irreducible_quotient_of_isCoatom
    (N : Subrepresentation ρ) (hN : IsCoatom N) : N.quotientRepresentation.IsIrreducible := by
  have hn : N.toSubmodule ≠ ⊤ := fun he => hN.1 (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (V ⧸ N.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap N.toSubmodule.mkQ
    apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule g hv
  }
  have hNT : N ≤ T := by
    intro v hv
    change N.toSubmodule.mkQ v ∈ S
    have hz : N.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.toSubmodule.zero_mem
  rcases eq_or_lt_of_le hNT with he | hlt
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).mpr (show v ∈ N from he.symm ▸ hw)
  · right
    have ht : T = ⊤ := hN.2 T hlt
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact (show v ∈ T from ht.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from by trivial))

/-- A nontrivial perfect action survives on an actual irreducible subquotient. -/
theorem exists_irreducible_section_surviving_perfect
    [FiniteDimensional (ZMod 2) V]
    (L : Subgroup G) [Group.IsPerfect L] (hne : ¬ L ≤ ρ.ker) :
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
  refine ⟨U, N, irreducible_quotient_of_isCoatom N hN, ?_⟩
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
  have hker := perfect_fixes_of_two_trivial_layers L N hNfix hQ
  apply hU
  intro g hg u
  exact congrArg Subtype.val (DFunLike.congr_fun (hker hg) u)

/-- The source component survives on some irreducible invariant subquotient. -/
theorem Hypotheses.exists_irreducible_section
    [FiniteDimensional (ZMod 2) V] {L B : Subgroup G} {a : G}
    (h : Hypotheses ρ L B a) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
        L.map (BinaryOffender.actionHom N.quotientRepresentation) ≠ ⊥ := by
  let := h.component.2
  have hne : ¬ L ≤ ρ.ker := by
    intro he
    have hL : L = ⊥ := le_bot_iff.mp
      (he.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr h.faithful).le)
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp this hL
  obtain ⟨U, N, hi, hn⟩ := exists_irreducible_section_surviving_perfect L hne
  refine ⟨U, N, hi, ?_⟩
  intro he
  apply hn
  intro g hg
  have hg' := (Subgroup.map_eq_bot_iff L).mp he hg
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro w
  exact (BinaryOffender.actionHom_eq_one_iff N.quotientRepresentation g).mp hg' w

end Representation.QuadraticFourGroup
end
