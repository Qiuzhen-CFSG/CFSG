module
public import Theory.Representation.BinaryOffender.CrossedComponentPair
public import Theory.Representation.CliffordRestriction
public import Theory.Representation.SemisimpleCoinvariants
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Faithfulness for fully moving component pairs

Clifford restriction through a normal exchanged pair makes each component
restriction semisimple. Full movement therefore forces its fixed space to
vanish. When both components are centerless, every nonzero submodule for
the pair is faithful: its kernel centralizes each factor and the direct
product has trivial center. Finally, a faithful commuting perfect factor
prevents an irreducible restriction, whose linear centralizer is cyclic.

These are the constituent and multiplicity steps for the tensor case of
Aschbacher--Smith D.3.7, printed pp.197--198. They do not assert the tensor
classification or its numerical exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Full movement by a component of an exchanged pair has no fixed vectors. -/
theorem full_component_pair_fixed_eq_bot
    (ρ : Representation (ZMod 2) G V) (hi : ρ.IsIrreducible)
    (J : Subgroup G) (hJ : IsComponent G J)
    (hindex : (normalizer (J : Set G)).index = 2)
    (a : G) (han : a ∉ normalizer (J : Set G))
    (hm : subspaceCommutator ρ ⊤ J = ⊤) : fixedSpace ρ J = ⊥ := by
  let J' := J.map (MulAut.conj a).toMonoidHom
  let X := J ⊔ J'
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hindex a han
  have hne : J ≠ J' := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : J' ≤ centralizer (J : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    ((hJ.map_conj a).commutator_eq_bot_of_ne hJ hne.symm)
  have hn : X ≤ normalizer (J : Set G) :=
    sup_le J.le_normalizer (hc.trans (centralizer_le_normalizer _))
  let := irreducible_restriction_semisimple_of_normal_chain ρ hi J X le_sup_left hn
  apply invariants_eq_bot_of_semisimple_of_coinvariants_eq_top (ρ.comp J.subtype)
  rwa [←subspaceCommutator_top_eq_coinvariants]

omit [FiniteDimensional (ZMod 2) V] in
/-- Every nonzero submodule of a fixed-free centerless component pair is faithful. -/
theorem pair_subrepresentation_faithful
    (ρ : Representation (ZMod 2) G V)
    (J K : Subgroup G) (hJ : IsComponent G J) (hK : IsComponent G K)
    (hne : J ≠ K) (hZJ : center J = ⊥) (hZK : center K = ⊥)
    (hfixJ : fixedSpace ρ J = ⊥) (hfixK : fixedSpace ρ K = ⊥)
    (R : Subrepresentation (ρ.comp (J ⊔ K).subtype)) (hR : R ≠ ⊥) :
    Function.Injective R.toRepresentation := by
  let X := J ⊔ K
  let P := J.subgroupOf X
  let Q := K.subgroupOf X
  let N := R.toRepresentation.ker
  have hPN : ¬ P ≤ N := by
    intro h
    apply hR
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hfixJ.le
    intro j
    have he := LinearMap.congr_fun (h (show (⟨j,(show J ≤ X from le_sup_left) j.property⟩ : X) ∈ P from j.property))
      (⟨v,hv⟩ : R.toSubmodule)
    exact congrArg Subtype.val he
  have hQN : ¬ Q ≤ N := by
    intro h
    apply hR
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hfixK.le
    intro k
    have he := LinearMap.congr_fun (h (show (⟨k,(show K ≤ X from le_sup_right) k.property⟩ : X) ∈ Q from k.property))
      (⟨v,hv⟩ : R.toSubmodule)
    exact congrArg Subtype.val he
  have hNP : N ≤ centralizer (P : Set X) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (((hJ.subgroupOf (show J ≤ X from le_sup_left)).normal_dichotomy N).resolve_left hPN))
  have hNQ : N ≤ centralizer (Q : Set X) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (((hK.subgroupOf (show K ≤ X from le_sup_right)).normal_dichotomy N).resolve_left hQN))
  have hc : J ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hK hne)
  have hd : Disjoint J K := by
    apply disjoint_def.mpr
    intro x hxJ hxK
    have hz : (⟨x,hxJ⟩ : J) ∈ center J := mem_center_iff.mpr fun j =>
      Subtype.ext ((hc j.property x hxK).symm)
    exact congrArg (fun j : J => (j : G)) (mem_bot.mp (hZJ ▸ hz))
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting J K hd hc
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxJ : (x : G) ∈ centralizer (J : Set G) := by
    intro j hj
    exact congrArg Subtype.val ((hNP hx) ⟨j,(show J ≤ X from le_sup_left) hj⟩ hj)
  have hxK : (x : G) ∈ centralizer (K : Set G) := by
    intro k hk
    exact congrArg Subtype.val ((hNQ hx) ⟨k,(show K ≤ X from le_sup_right) hk⟩ hk)
  obtain ⟨⟨j,k⟩,hjk⟩ := e.surjective x
  have hxjk : (x : G) = (j : G) * (k : G) :=
    (congrArg Subtype.val hjk).symm.trans (he j k)
  have hjC : (j : G) ∈ centralizer (J : Set G) :=
    (centralizer (J : Set G)).mul_mem_cancel_right
      ((le_centralizer_iff.mp hc) k.property) |>.mp (hxjk ▸ hxJ)
  have hkC : (k : G) ∈ centralizer (K : Set G) :=
    (centralizer (K : Set G)).mul_mem_cancel_left (hc j.property) |>.mp (hxjk ▸ hxK)
  have hj1 : j = 1 := mem_bot.mp (hZJ ▸
    (show j ∈ center J from mem_center_iff.mpr fun z => Subtype.ext (hjC z z.property)))
  have hk1 : k = 1 := mem_bot.mp (hZK ▸
    (show k ∈ center K from mem_center_iff.mpr fun z => Subtype.ext (hkC z z.property)))
  apply mem_bot.mpr
  apply Subtype.ext
  simpa only [hj1,hk1,coe_one,one_mul] using hxjk
/-- A nontrivial perfect commuting factor prevents an irreducible restriction. -/
theorem not_irreducible_of_faithful_commuting_perfect
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (J K : Subgroup G) [Group.IsPerfect K] [Nontrivial K]
    (hc : K ≤ centralizer (J : Set G)) :
    ¬ IsIrreducible (ρ.comp J.subtype) := by
  intro hi
  let σ : Representation (ZMod 2) J V := ρ.comp J.subtype
  let : σ.IsIrreducible := hi
  let C := CentralizerField.linearCentralizer σ
  let f : K →* C := (ρ.asGroupHom.comp K.subtype).codRestrict C (by
    intro k
    apply (CentralizerField.mem_linearCentralizer_iff σ _).mpr
    intro j v
    change ρ (k : G) (ρ (j : G) v) = ρ (j : G) (ρ (k : G) v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g : G => ρ g v) ((hc k.property j j.property).symm))
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : C => z.val.val) hab
  let : IsCyclic (IntertwiningMap σ σ)ˣ := CentralizerField.units_isCyclic σ
  let : IsCyclic C := isCyclic_of_injective
    (CentralizerField.centralizerUnitsEquiv σ).toMonoidHom
    (CentralizerField.centralizerUnitsEquiv σ).injective
  let : Group.IsSolvable C :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := C)).comm a b
  exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_isSolvable_injective hinj)

end Representation.BinaryOffender

open scoped MonoidAlgebra
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A simple group acts faithfully on every nonzero submodule when its full fixed space vanishes. -/
theorem simple_subrepresentation_faithful_of_fixed_eq_bot
    (ρ : Representation (ZMod 2) G V) [IsSimpleGroup G]
    (hfix : ρ.invariants = ⊥) (S : Subrepresentation ρ) (hS : S ≠ ⊥) :
    Function.Injective S.toRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.toRepresentation.ker inferInstance with h | h
  · exact h
  · apply False.elim
    apply hS
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hfix.le
    intro g
    have hg : g ∈ S.toRepresentation.ker := h.symm ▸ mem_top g
    exact congrArg Subtype.val (LinearMap.congr_fun hg (⟨v,hv⟩ : S.toSubmodule))

variable [FiniteDimensional (ZMod 2) V]
/-- A semisimple module with a faithful commuting perfect factor has at least
 two nonzero summands for the first factor. -/
theorem two_mul_le_finrank_of_commuting_perfect [Nontrivial V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (J K : Subgroup G) [Group.IsPerfect K] [Nontrivial K]
    (hc : K ≤ centralizer (J : Set G))
    [IsSemisimpleModule (ZMod 2)[J] (Representation.asModule (ρ.comp J.subtype))]
    (d : ℕ)
    (hd : ∀ S : Subrepresentation (ρ.comp J.subtype), S ≠ ⊥ →
      d ≤ Module.finrank (ZMod 2) S.toSubmodule) :
    2 * d ≤ Module.finrank (ZMod 2) V := by
  have hnot := not_irreducible_of_faithful_commuting_perfect ρ hf J K hc
  obtain ⟨S,hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp J.subtype)
  have hSa := (Subrepresentation.irreducible_iff_isAtom S).mp hS
  have hSt : S ≠ ⊤ := fun he => hnot (isSimpleOrder_iff_isAtom_top.mpr (he ▸ hSa))
  let : IsSemisimpleRepresentation (ρ.comp J.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr inferInstance
  obtain ⟨Q,hQ⟩ := exists_isCompl S
  have hQb : Q ≠ ⊥ := by
    intro he
    apply hSt
    simpa only [he,sup_bot_eq] using hQ.sup_eq_top
  have hcomp : IsCompl S.toSubmodule Q.toSubmodule := by
    constructor
    · apply disjoint_iff.mpr
      exact congrArg Subrepresentation.toSubmodule hQ.inf_eq_bot
    · apply codisjoint_iff.mpr
      change S.toSubmodule ⊔ Q.toSubmodule =
        (⊤ : Subrepresentation (ρ.comp J.subtype)).toSubmodule
      rw [←Subrepresentation.toSubmodule_sup,hQ.sup_eq_top]
  have he := Submodule.finrank_add_eq_of_isCompl hcomp
  have hs := hd S hSa.ne_bot
  have hq := hd Q hQb
  omega

end Representation.BinaryOffender
