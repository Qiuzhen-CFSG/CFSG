module

public import Theory.Representation.BinaryOffender.QuadraticDisjointSummands
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.IrreducibleSimpleFaithful

/-!
# Quadratic actors stabilizing faithful normal constituents

Let a quadratic actor move an invariant subspace to a disjoint translate.
Every element in its intersection with the subgroup acting faithfully on that
subspace is trivial: its displacement is fixed by the moving element and lies
in both disjoint spaces. For a simple constituent of a normal subgroup, any
distinct translate is disjoint. Moreover, the constituent then injects into
the quotient by the actor's fixed space.

Consequently, an outer-rank bound together with a fixed-codimension estimate
forces each sufficiently large faithful constituent to be invariant. The
rank-two corollary supplies this step for binary chief factors with a simple
normal subgroup whose nontrivial constituents have dimension greater than four.

Source: the quadratic-action convention of Aschbacher--Smith, *The
Classification of Quasithin Groups*, B.1.1--B.1.3, and the normal-constituent
conjugation in Clifford theory (Isaacs, *Character Theory*, Theorem 6.2).
-/

public section

namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Faithfulness on one invariant subspace suffices for a disjoint translate
to force trivial intersection with the subgroup acting on that subspace. -/
theorem quadratic_inf_eq_bot_of_disjoint_constituent
    (K A : Subgroup G) (J : Subrepresentation (ρ.comp K.subtype))
    (hfaith : Function.Injective J.toRepresentation) (hq : IsQuadratic ρ A)
    {a : G} (ha : a ∈ A)
    (hdis : Disjoint J.toSubmodule (J.toSubmodule.map (ρ a))) :
    A ⊓ K = ⊥ := by
  apply bot_unique
  rintro b ⟨hb, hbK⟩
  have hfix := quadratic_fixes_disjoint_summand ρ J.toSubmodule hq ha hb hdis
    (fun v hv => J.apply_mem_toSubmodule (⟨b, hbK⟩ : K) hv)
  have he : (⟨b, hbK⟩ : K) = 1 := by
    apply hfaith
    rw [map_one]
    ext v
    exact hfix v v.property
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)

private theorem constituent_disjoint_of_moving
    (K : Subgroup G) [K.Normal] (J : Subrepresentation (ρ.comp K.subtype))
    (hJ : J.toRepresentation.IsIrreducible) {a : G}
    (hne : J.toSubmodule.map (ρ a) ≠ J.toSubmodule) :
    Disjoint J.toSubmodule (J.toSubmodule.map (ρ a)) := by
  let c := conjugateSubrepresentationOrderIso ρ K a
  have hJa : IsAtom J := (Subrepresentation.irreducible_iff_isAtom J).mp hJ
  have hca : IsAtom (c J) := (c.isAtom_iff J).mpr hJa
  have hne' : c J ≠ J := by
    intro he
    apply hne
    simpa only [c, conjugateSubrepresentationOrderIso_toSubmodule] using
      congrArg Subrepresentation.toSubmodule he
  have hd := hca.disjoint_of_ne hJa hne'
  rw [disjoint_iff]
  have he := congrArg Subrepresentation.toSubmodule hd.symm.eq_bot
  change J.toSubmodule ⊓ (c J).toSubmodule = ⊥ at he
  simpa only [c, conjugateSubrepresentationOrderIso_toSubmodule] using he

/-- If a quadratic actor moves a faithful simple constituent of a normal
subgroup, its intersection with that subgroup is trivial. -/
theorem quadratic_inf_eq_bot_of_moving_constituent
    (K A : Subgroup G) [K.Normal] (J : Subrepresentation (ρ.comp K.subtype))
    (hJ : J.toRepresentation.IsIrreducible) (hfaith : Function.Injective J.toRepresentation)
    (hq : IsQuadratic ρ A) {a : G} (ha : a ∈ A)
    (hne : J.toSubmodule.map (ρ a) ≠ J.toSubmodule) : A ⊓ K = ⊥ :=
  quadratic_inf_eq_bot_of_disjoint_constituent ρ K A J hfaith hq ha
    (constituent_disjoint_of_moving ρ K J hJ hne)

/-- A subspace disjoint from one actor translate injects into the quotient
by all actor-fixed vectors. No quadraticity assumption is needed. -/
theorem finrank_le_fixedCodim_of_disjoint_map [FiniteDimensional (ZMod 2) V]
    (I : Submodule (ZMod 2) V) {A : Subgroup G} {a : G} (ha : a ∈ A)
    (hdis : Disjoint I (I.map (ρ a))) :
    Module.finrank (ZMod 2) I ≤ fixedCodim ρ A := by
  let f := (fixedSpace ρ A).mkQ.comp I.subtype
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  have hf : (v : V) ∈ fixedSpace ρ A := (Submodule.Quotient.mk_eq_zero _).mp hv
  have hm : (v : V) ∈ I.map (ρ a) := ⟨v, v.property, hf ⟨a, ha⟩⟩
  exact Subtype.ext ((Submodule.disjoint_def.mp hdis) _ v.property hm)

/-- Quantitative outer control forces a quadratic actor to stabilize a
faithful normal constituent. The premises apply to the original actor. -/
theorem quadratic_constituent_stable_of_outer_rank_bound
    [FiniteDimensional (ZMod 2) V]
    (K A : Subgroup G) [K.Normal] (J : Subrepresentation (ρ.comp K.subtype))
    (hJ : J.toRepresentation.IsIrreducible) (hfaith : Function.Injective J.toRepresentation)
    (hq : IsQuadratic ρ A) (r : ℕ)
    (houter : A ⊓ K = ⊥ → rank A ≤ r)
    (hsmall : rank A ≤ r → fixedCodim ρ A < Module.finrank (ZMod 2) J.toSubmodule) :
    ∀ a ∈ A, J.toSubmodule.map (ρ a) = J.toSubmodule := by
  intro a ha
  by_contra hne
  have hd := constituent_disjoint_of_moving ρ K J hJ hne
  have hinf := quadratic_inf_eq_bot_of_disjoint_constituent ρ K A J hfaith hq ha hd
  exact (not_le_of_gt (hsmall (houter hinf)))
    (finrank_le_fixedCodim_of_disjoint_map ρ J.toSubmodule ha hd)

/-- For a simple normal subgroup with constituents of dimension at least five,
an outer binary rank at most two and fixed codimension at most twice the actor
rank force constituent stability. Faithfulness follows from simplicity. -/
theorem quadratic_constituent_stable_of_simple_of_outer_rank_two
    [FiniteDimensional (ZMod 2) V]
    (K A : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (J : Subrepresentation (ρ.comp K.subtype)) (hJ : J.toRepresentation.IsIrreducible)
    (hdim : 4 < Module.finrank (ZMod 2) J.toSubmodule)
    (hq : IsQuadratic ρ A) (houter : A ⊓ K = ⊥ → rank A ≤ 2)
    (hcodim : fixedCodim ρ A ≤ 2 * rank A) :
    ∀ a ∈ A, J.toSubmodule.map (ρ a) = J.toSubmodule := by
  let := hJ
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank J.toRepresentation
    (show 1 < Module.finrank (ZMod 2) J.toSubmodule by omega)
  exact quadratic_constituent_stable_of_outer_rank_bound ρ K A J hJ hf hq 2 houter
    (by intro hr; omega)

end Representation.BinaryOffender
