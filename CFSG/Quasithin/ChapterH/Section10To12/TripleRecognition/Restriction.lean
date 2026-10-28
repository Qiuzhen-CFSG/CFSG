module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleJames
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.NormalInvariants
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Restriction to the genuine triple Mathieu component

A nonzero invariant subspace of a faithful irreducible ambient module remains
faithful on a normal triple cover. Indeed its kernel is central or the whole
component, and either nontrivial possibility fixes the component's cubic
center. Normality of that center and ambient irreducibility rule this out.

An irreducible constituent therefore has binary dimension at least twelve by
James's theorem. When the ambient dimension is twelve it fills the whole
space, proving irreducibility of restriction and the actual module equivalence.
The final statements specialize normality to the literal equality F*(G) = L.

Source: Aschbacher–Smith H.12.1(3), proof on printed p.394 (PDF p.405).
The separate displacement argument must still supply dimension twelve before
this restriction bridge establishes that source clause.
-/

public section

open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- Every nonzero constituent is faithful on the normal triple component. -/
theorem faithful_constituent (L : Subgroup G) [L.Normal] (hL : IsTripleM22 L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ)
    (W : Subrepresentation (ρ.comp L.subtype)) (hW : W ≠ ⊥) :
    Function.Injective W.toRepresentation := by
  let := hL.quasisimple
  have hfix : invariants (ρ.comp ((center L).map L.subtype).subtype) = ⊥ := by
    by_contra h
    have hk := le_ker_of_normal_invariants_ne_bot ρ ((center L).map L.subtype) h
    have he : (center L).map L.subtype = ⊥ :=
      le_bot_iff.mp ((ρ.ker_eq_bot_iff.mpr hf) ▸ hk)
    have hc := Subgroup.card_map_of_injective (K := center L) L.subtype_injective
    rw [he, Subgroup.card_bot, hL.center_card] at hc
    omega
  have hnfix : ¬ center L ≤ W.toRepresentation.ker := by
    intro hk
    apply hW
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro v hv
    have hmem : v ∈ invariants (ρ.comp ((center L).map L.subtype).subtype) := by
      intro z
      obtain ⟨a, ha, haz⟩ := z.property
      have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp (hk ha)) (⟨v, hv⟩ : W)
      change ρ (z : G) v = v
      rw [← haz]
      exact congrArg Subtype.val he
    simpa only [hfix, Submodule.mem_bot] using hmem
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsQuasisimple.normal_le_center_or_eq_top W.toRepresentation.ker with hc | ht
  · let : Fact (Nat.card (center L)).Prime := ⟨hL.center_card ▸ Nat.prime_three⟩
    rcases (W.toRepresentation.ker.subgroupOf (center L)).eq_bot_or_eq_top_of_prime_card
      with hb | ht
    · apply bot_unique
      intro x hx
      have hm : (⟨x, hc hx⟩ : center L) ∈ W.toRepresentation.ker.subgroupOf (center L) := hx
      rw [hb] at hm
      exact congrArg Subtype.val (mem_bot.mp hm)
    · apply (hnfix _).elim
      intro x hx
      have hm : (⟨x, hx⟩ : center L) ∈ W.toRepresentation.ker.subgroupOf (center L) :=
        ht ▸ mem_top _
      exact hm
  · exact (hnfix (ht ▸ le_top)).elim

/-- At binary dimension twelve the restriction is itself irreducible. -/
theorem irreducible_restriction (L : Subgroup G) [L.Normal] (hL : IsTripleM22 L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12) :
    Representation.IsIrreducible (ρ.comp L.subtype) := by
  let := Representation.finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨W, hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp L.subtype)
  let := hW
  have ha := (Subrepresentation.irreducible_iff_isAtom W).mp hW
  have hb := hL.faithful_irreducible_finrank_ge_twelve W.toRepresentation
    (faithful_constituent L hL ρ hf W ha.ne_bot)
  have he : W.toSubmodule = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) (hd ▸ hb)
  have ht : W = ⊤ := Subrepresentation.toSubmodule_injective he
  exact isSimpleOrder_iff_isAtom_top.mpr (ht ▸ ha)

/-- The degree lower bound also holds for a faithful irreducible ambient action. -/
theorem ambient_finrank_ge_twelve (L : Subgroup G) [L.Normal] (hL : IsTripleM22 L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : 12 ≤ Module.finrank (ZMod 2) V := by
  let := Representation.finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨W, hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp L.subtype)
  let := hW
  have ha := (Subrepresentation.irreducible_iff_isAtom W).mp hW
  exact (hL.faithful_irreducible_finrank_ge_twelve W.toRepresentation
    (faithful_constituent L hL ρ hf W ha.ne_bot)).trans (Submodule.finrank_le _)

/-- The restriction bridge with the literal generalized-Fitting source hypothesis. -/
theorem restriction_equiv_of_generalizedFitting (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12) :
    Nonempty (Representation.Equiv (ρ.comp L.subtype) hL.binaryRepresentation) := by
  let : L.Normal := hF ▸ inferInstance
  let := irreducible_restriction L hL ρ hf hd
  exact hL.equiv_binaryRepresentation_of_finrank_twelve (ρ.comp L.subtype)
    (hf.comp L.subtype_injective) hd

/-- The ambient lower bound under F*(G) = L, used by the displacement assembly. -/
theorem ambient_finrank_ge_twelve_of_generalizedFitting
    (L : Subgroup G) (hL : IsTripleM22 L) (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : 12 ≤ Module.finrank (ZMod 2) V := by
  let : L.Normal := hF ▸ inferInstance
  exact ambient_finrank_ge_twelve L hL ρ hf

end CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition
