module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Reduction
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# Binary linear rank one and alternating degree five in B.1.13

The checked root-coordinate automorphism theorem gives the full pointwise
Sylow fixer for binary PSL₂. Faithfulness of the action on the central
quotient gives the same restriction for any perfect central cover. The
permutation automorphism calculation supplies A₅ independently. These are
applied to the literal K-action and local intersection from B.1.13.

For L isomorphic to A₅, every proper subgroup is solvable, so a quasisimple
K ≤ L must equal L. The order-three case is genuinely isomorphic to A₃.
The other alternating degrees and the proper-overgroup calculation in
higher-rank Lie type remain separate model inputs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.13,
printed p.74 (PDF p.85); the imported model calculations retain their
root-coordinate and permutation-group source references.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- All binary PSL₂ pointwise Sylow fixers are two-groups. -/
theorem linearTwo_fixer {F : Type*} [Field F] [Finite F] [CharP F 2] :
    SylowFixerIsTwoGroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
  fixer_twoGroup_of_inner Theory.PSL2.aut_fixing_sylow_inner

/-- The binary linear model identifies the actual component's central
quotient; this excludes the centralizing branch of the local alternative. -/
theorem linearTwo_le_component [Finite G] {F : Type*} [Field F] [Finite F] [CharP F 2]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L := by
  let := hL.2
  exact le_component_of_local_dichotomy K L T hL hLK hkind hKN hd
    (fixer_twoGroup_of_centralQuotient e linearTwo_fixer)

/-- The same intrinsic pointwise-fixer calculation for A₅. -/
theorem alternatingFive_fixer : SylowFixerIsTwoGroup (alternatingGroup (Fin 5)) :=
  fixer_twoGroup_of_inner Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner

/-- The source containment step for a component with central quotient A₅. -/
theorem alternatingFive_le_component [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* alternatingGroup (Fin 5))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L := by
  let := hL.2
  exact le_component_of_local_dichotomy K L T hL hLK hkind hKN hd
    (fixer_twoGroup_of_centralQuotient e alternatingFive_fixer)

/-- An actual quasisimple subgroup of an A₅ component is the entire component. -/
theorem quasisimple_eq_alternatingFive (K L : Subgroup G) [IsQuasisimple K]
    (hKL : K ≤ L) (e : L ≃* alternatingGroup (Fin 5)) : K = L := by
  by_contra hne
  let D := K.subgroupOf L
  let d : D ≃* K := subgroupOfEquivOfLe hKL
  have hD : D ≠ ⊤ := by
    intro h
    apply hne
    have hh := congrArg (Subgroup.map L.subtype) h
    simpa only [D, map_subgroupOf_eq_of_le hKL, ← MonoidHom.range_eq_map,
      range_subtype] using hh
  let : Group.IsSolvable D := alternatingGroup.isSolvable_subgroup_of_equiv_five e D hD
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := d.symm.toMonoidHom) d.symm.injective
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- The complete degree-five subgroup conclusion, with genuine A₃ or A₅
isomorphisms and the source bounds on the alternating degree. -/
theorem alternatingFive_subgroup_models (K L : Subgroup G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3) (hKL : K ≤ L)
    (e : L ≃* alternatingGroup (Fin 5)) :
    ∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ Nonempty (K ≃* alternatingGroup (Fin n)) := by
  rcases hkind with hq | hc
  · let := hq
    have he := quasisimple_eq_alternatingFive K L hKL e
    subst K
    exact ⟨5, by decide, le_rfl, ⟨e⟩⟩
  · refine ⟨3, le_rfl, by decide, ⟨mulEquivOfPrimeCardEq hc ?_⟩⟩
    rw [nat_card_alternatingGroup]
    norm_num [Nat.card_fin, Nat.factorial]

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
