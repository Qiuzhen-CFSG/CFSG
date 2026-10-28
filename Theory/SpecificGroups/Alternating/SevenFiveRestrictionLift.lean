module
public import Theory.SpecificGroups.Alternating.SevenFiveRestriction
public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import Theory.GroupTheory.PerfectCentralModSolvable
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
/-!
# The A₇ intermediate restriction through the original central quotient

A perfect subgroup with A₅ two-core quotient has two-group kernel under
the O₂,Z projection: its solvable radical is precisely its two-core.
The existing seven-letter section theorem therefore identifies its actual
image as A₅. Both images inherit normalization by the same image Sylow,
so SevenFiveRestriction gives equal images or the full A₇ image.

PerfectCentralModSolvable lifts either alternative. The intrinsic two-core
lies in the supplied Sylow and hence normalizes both original subgroups.
No component membership in the containing group or removal of the central
cover is assumed.

Source: Aschbacher–Smith A.3.14(2), printed pp.49–50, as used in 12.3.12,
printed p.811. The literal Chapter 12 application is TerminalComponentA314.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.SevenFivePlacement
variable {G : Type*} [Group G] [Finite G]

/-- The finite restriction lifted through the literal O₂,Z kernel. -/
theorem perfect_overgroup_eq_or_top_of_centralPreimage [Group.IsPerfect G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hker : f.ker = centralPreimage (pCore 2 G))
    (B E : Subgroup G) [Group.IsPerfect B] [Group.IsPerfect E]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 G)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hBE : B ≤ E) : E = B ∨ E = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsSolvable f.ker := hker ▸ centralPreimage_pCore_isSolvable 2
  let j : (f.subgroupMap B).ker →* f.ker := {
    toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (f.subgroupMap B).ker :=
    Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : f.ker => (z : G)) h)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hkb : (f.subgroupMap B).ker ≤ pCore 2 B := by
    rw [← radical_eq_core_of_perfect_simple_core_quotient]
    exact le_solvableRadical _ inferInstance inferInstance
  have htwo : IsPGroup 2 (f.subgroupMap B).ker :=
    pCore_isPGroup.of_injective (inclusion hkb) (inclusion_injective hkb)
  let eB := alternatingGroup.SevenFiveSection.imageFiveEquiv f B htwo e
  let : Group.IsPerfect (E.map f) := Group.IsPerfect.map f
  have hSB' : ((S.mapSurjective hf) : Subgroup (alternatingGroup (Fin 7))) ≤
      normalizer (B.map f : Set (alternatingGroup (Fin 7))) :=
    (map_mono hSB).trans (le_normalizer_map f)
  have hSE' : ((S.mapSurjective hf) : Subgroup (alternatingGroup (Fin 7))) ≤
      normalizer (E.map f : Set (alternatingGroup (Fin 7))) :=
    (map_mono hSE).trans (le_normalizer_map f)
  have hcore : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hN : pCore 2 G ≤ f.ker := hker.symm ▸ le_centralPreimage (pCore 2 G)
  have hc : f.ker.map (QuotientGroup.mk' (pCore 2 G)) ≤ center (G ⧸ pCore 2 G) := by
    rw [hker]
    exact map_comap_le _ _
  rcases perfect_overgroup_eq_or_top (B.map f) (E.map f) eB
      (S.mapSurjective hf) hSB' hSE' (map_mono hBE) with he | he
  · exact Or.inl (le_antisymm
      (perfect_le_of_map_le_of_kernel_central_mod_solvable f (pCore 2 G) hN hc
        E B (hcore.trans hSB) he.le) hBE)
  · apply Or.inr
    apply top_unique
    apply perfect_le_of_map_le_of_kernel_central_mod_solvable f (pCore 2 G) hN hc
      ⊤ E (hcore.trans hSE)
    rw [he]
    exact le_top
end Theory.SpecificGroups.Alternating.SevenFivePlacement
