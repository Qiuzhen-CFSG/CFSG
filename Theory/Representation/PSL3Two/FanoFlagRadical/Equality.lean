module

public import Theory.Representation.PSL3Two.FanoFlagRadical.Basic
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# The radical of the binary Fano flag representation

The intersection of all maximal invariant subspaces of the flag permutation
module is exactly the transported sum of the point-core and line-core radicals.
Consequently its representation is natural plus dual-natural and its dimension
is six.

The subrepresentation/submodule order isomorphism identifies the literal
intersection with the group-algebra module's Jacobson radical. Functoriality
under the product projections and inclusions proves the product formula;
equivariant equivalences then transport it. Apply this to the actual four-factor
flag decomposition, using the proved core radicals and irreducibility of the
trivial and Steinberg factors.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.6.2(2),
printed p.387.
-/

@[expose] public section

open Representation
open scoped MonoidAlgebra

namespace BinaryLinearThree.FanoFlagRadical

section General
variable {k G V X : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G X}

private def radical (ρ : Representation k G V) : Subrepresentation ρ :=
  sInf {N : Subrepresentation ρ | IsCoatom N}

private theorem radical_asSubmodule (ρ : Representation k G V) :
    (radical ρ).asSubmodule = Module.jacobson k[G] ρ.asModule := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have hi : e '' {N | IsCoatom N} = {N | IsCoatom N} := by
    ext N
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (e.isCoatom_iff M).2 hM
    · intro hN
      exact ⟨e.symm N, (e.symm.isCoatom_iff N).2 hN, e.apply_symm_apply N⟩
  change e (sInf {N | IsCoatom N}) = sInf {N | IsCoatom N}
  rw [map_sInf e, hi]

private theorem map_mem_radical (f : ρ.IntertwiningMap σ) {v : V}
    (hv : v ∈ radical ρ) : f v ∈ radical σ := by
  change f v ∈ (radical σ).asSubmodule
  rw [radical_asSubmodule]
  apply Module.le_comap_jacobson (IntertwiningMap.equivLinearMapAsModule ρ σ f)
  change v ∈ (radical ρ).asSubmodule at hv
  rwa [radical_asSubmodule] at hv

private theorem mem_radical_prod (v : V × X) :
    v ∈ radical (ρ.prod σ) ↔ v.1 ∈ radical ρ ∧ v.2 ∈ radical σ := by
  constructor
  · intro hv
    exact ⟨map_mem_radical (IntertwiningMap.fst k ρ σ) hv,
      map_mem_radical (IntertwiningMap.snd k ρ σ) hv⟩
  · rintro ⟨hv, hx⟩
    have hl := map_mem_radical (IntertwiningMap.inl k ρ σ) hv
    have hr := map_mem_radical (IntertwiningMap.inr k ρ σ) hx
    change (v.1, 0) ∈ radical (ρ.prod σ) at hl
    change (0, v.2) ∈ radical (ρ.prod σ) at hr
    change v ∈ (radical (ρ.prod σ)).toSubmodule
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using
      (radical (ρ.prod σ)).toSubmodule.add_mem hl hr

private theorem mem_radical_equiv (e : ρ.Equiv σ) (v : V) :
    v ∈ radical ρ ↔ e v ∈ radical σ := by
  constructor
  · exact map_mem_radical e.toIntertwiningMap
  · intro hv
    simpa using map_mem_radical e.symm.toIntertwiningMap hv

private theorem radical_eq_bot (ρ : Representation k G V) [IsIrreducible ρ] :
    radical ρ = ⊥ :=
  le_antisymm (sInf_le isCoatom_bot) bot_le

private theorem mem_radical_irreducible (ρ : Representation k G V) [IsIrreducible ρ]
    (v : V) : v ∈ radical ρ ↔ v = 0 := by
  rw [radical_eq_bot]
  exact Submodule.mem_bot (R := k)

private theorem scalar_irreducible (ρ : Representation k G k) : IsIrreducible ρ where
  exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
  eq_bot_or_eq_top N := by
    rcases eq_bot_or_eq_top N.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end General

open FanoDecomposition FanoCoreStructure

set_option backward.isDefEq.respectTransparency false in
/-- The literal radical of the flag permutation module is the transported sum
of the point-core and line-core radicals. -/
theorem flagRadical_eq_transportedCoreRadicals :
    flagRadical = transportedCoreRadicals := by
  let : IsIrreducible (trivial (ZMod 2) Group (ZMod 2)) := scalar_irreducible _
  let : IsIrreducible S := IrreducibleCatalogue.steinberg_irreducible
  ext v
  change v ∈ flagRadical ↔ v ∈ transportedCoreRadicals
  rw [mem_transportedCoreRadicals_iff]
  change v ∈ radical flagRepresentation ↔ _
  rw [mem_radical_equiv (X := Target) (σ := targetRepresentation) flagDecomposition]
  change flagDecomposition v ∈ radical
    ((trivial (ZMod 2) Group (ZMod 2)).prod (U₂.prod (lineCoreRepresentation.prod S))) ↔ _
  have hp : radical U₂ = pointKernel := pointKernel_eq_radical.symm
  have hl : radical lineCoreRepresentation = lineKernel := lineKernel_eq_radical.symm
  rw [mem_radical_prod (V := ZMod 2) (X := Core × (LineCore × Steinberg))
    (ρ := trivial (ZMod 2) Group (ZMod 2)) (σ := U₂.prod (lineCoreRepresentation.prod S))]
  rw [mem_radical_prod (V := Core) (X := LineCore × Steinberg)
    (ρ := U₂) (σ := lineCoreRepresentation.prod S)]
  rw [mem_radical_prod (V := LineCore) (X := Steinberg)
    (ρ := lineCoreRepresentation) (σ := S)]
  simp only [hp, hl, mem_radical_irreducible]

/-- An actual equivalence from the literal flag radical to natural plus dual-natural. -/
noncomputable def flagRadicalEquiv : flagRadical.toRepresentation.Equiv (W.prod W.dual) := by
  rw [flagRadical_eq_transportedCoreRadicals]
  exact transportedCoreRadicalsEquiv.symm

/-- The literal radical of the twenty-one-dimensional flag module has dimension six. -/
theorem finrank_flagRadical : Module.finrank (ZMod 2) flagRadical.toSubmodule = 6 := by
  rw [flagRadical_eq_transportedCoreRadicals]
  exact finrank_transportedCoreRadicals

end BinaryLinearThree.FanoFlagRadical
