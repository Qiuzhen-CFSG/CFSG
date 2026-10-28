module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.NaturalFixed
public import Mathlib.Order.Atoms.Finite

/-!
# Consequences of compatible natural heads

A generating two-space and compatible natural quotients give a unique
maximal submodule: the natural Sylow fixed space is one-dimensional, so the
fixed-generator theorem applies. If the whole module is not natural, every
natural maximal quotient has nonzero kernel; finiteness then supplies an
irreducible submodule in such a kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed p.961. The common natural head
identifications remain an explicit premise here; their construction is the
separate marked-parabolic argument. No uniqueness or chief-factor
classification is included in that premise.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

omit [FiniteDimensional (ZMod 2) U] in
theorem IsNatural.finrank_eq_four (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (h : IsNatural ρ eH) : Module.finrank (ZMod 2) U = 4 := by
  obtain ⟨e, _⟩ := h
  rw [e.finrank_eq]
  simp [NaturalSpace]

omit [FiniteDimensional (ZMod 2) U] in
theorem IsNatural.faithful (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (h : IsNatural ρ eH) : Function.Injective ρ := by
  obtain ⟨e, he⟩ := h
  intro g k hgk
  apply eH.injective
  ext v
  obtain ⟨u, rfl⟩ := e.surjective v
  rw [← he, ← he, hgk]

theorem unique_maximal_of_natural_heads
    (s : GeneratingSeed ρ) (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (T : Sylow 2 H) (hs : s.sylow = (T : Subgroup H))
    (hheads : AllNaturalHeads ρ eH) (W : Subrepresentation ρ) (hW : IsCoatom W) :
    ∀ X : Subrepresentation ρ, IsCoatom X → X = W := by
  apply s.unique_maximal ρ (naturalAction eH) _ hheads W hW
  rw [hs]
  apply natural_sylow_fixedSpace_finrank
  norm_num [NaturalSpace, Nat.card_eq_fintype_card]

omit [FiniteDimensional (ZMod 2) U] in
theorem natural_of_natural_head_of_eq_bot
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (W : Subrepresentation ρ)
    (hW : W = ⊥) (hq : IsNatural W.quotientRepresentation eH) : IsNatural ρ eH := by
  obtain ⟨e, he⟩ := hq
  have hW' : W.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hW
  let f := (W.toSubmodule.quotEquivOfEqBot hW').symm
  refine ⟨f.trans e, ?_⟩
  intro g u
  change e (f (ρ g u)) = eH g (e (f u))
  have h := he g (W.toSubmodule.mkQ u)
  rw [Subrepresentation.quotientRepresentation_mk] at h
  simpa only [f, Submodule.quotEquivOfEqBot_symm_apply, Submodule.mkQ_apply] using h

theorem exists_nonzero_maximal_and_atom_of_not_natural
    (s : GeneratingSeed ρ) (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH) (hnatural : ¬ IsNatural ρ eH) :
    ∃ W I : Subrepresentation ρ, IsCoatom W ∧ W ≠ ⊥ ∧ IsAtom I ∧ I ≤ W := by
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) := Finite.of_injective
    (fun W : Subrepresentation ρ => (W : Set U)) SetLike.coe_injective
  obtain ⟨v, _, hv0, _, _⟩ := s.exists_fixed_generator ρ
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro he
    have hv : v ∈ (⊥ : Subrepresentation ρ) := he.symm ▸
      (show v ∈ (⊤ : Subrepresentation ρ) from by trivial)
    exact hv0 hv
  obtain ⟨W, hW, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  have hW0 : W ≠ ⊥ := fun h =>
    hnatural (natural_of_natural_head_of_eq_bot ρ eH W h (hheads W hW))
  obtain ⟨I, hI, hIW⟩ := (eq_bot_or_exists_atom_le W).resolve_left hW0
  exact ⟨W, I, hW, hW0, hI, hIW⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
