module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.SylowCoordinates
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.FlagCores
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.RelativeOvergroups

/-!
# Constructing the binary invariant parabolic pairs

The central component involution has rank-one coordinates in the actual
linear model. Its incident image-line/fixed-hyperplane flag is invariant
under N_S(L), contains S ∩ L in its stabilizer, and has stabilizer C_L(t).
Every proper flag stabilizer containing S ∩ L has self-centralizing
intrinsic two-core containing t.

In degree five, or degree four without Dynkin action, the invariant geometry
constructs two flag stabilizers generating L. The component-orbit argument
puts each stabilizer joined with all of S in HeOver(S), including nontriviality
of its two-core. Their ambient joins generate ⟨L,S⟩. Applying the genuine
local block input therefore produces an escaping block in one of these
specific flag overgroups, for the independent block calculations to exclude.

This develops the binary part of Aschbacher–Smith 2.3.9(7), printed
pp.525–526. The invariant-parabolic convention is from the proof of E.2.2,
printed p.216. Only N_S(L) must preserve the flags; other elements of S may
permute components. The separate block obstructions and the degree-four
intersection calculation remain with the binary classification assembly.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
  {n : ℕ} [NeZero n]

/-- The projection canonically supplies its centralizer flag, including the
actual Sylow containment and invariance under the component normalizer in S. -/
theorem exists_projection_centralizer_flag (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ F : Flag n, F.types = {1, n - 1} ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F ∧
      flagStabilizer e F = centralizer ({t} : Set L) ∧
      flagOvergroup e F ((S : Subgroup H).map H.subtype) ≤ M := by
  obtain ⟨c⟩ := projection_transvectionCoordinates h hn e ht ht2
  have hn2 : 2 ≤ n := by omega
  refine ⟨c.flag hn2, c.flag_types hn2, c.flag_invariant hn2 h ht, ?_,
    (c.centralizer_eq_flag hn2).symm, c.flagOvergroup_le hn2 h ht⟩
  obtain ⟨T, hT⟩ := exists_component_sylow h
  rw [← c.centralizer_eq_flag hn2, ← hT]
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    ((projection_mem_center_component_sylow h e ht ht2 T hT).2 x hx)

/-- The binary invariant parabolic pair in the generation argument of
2.3.9(7). Both actual ambient overgroups have nontrivial self-centralizing
two-core and contain all of S; together they generate ⟨L,S⟩. -/
theorem exists_invariant_parabolic_pair
    (h : LocalSetup H L M S z) (e : L ≃* PSL n)
    (hn : n = 5 ∨ n = 4 ∧
      ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype))
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ F₁ F₂ : Flag n,
      ExcludedFlagShape F₁ ∧ ExcludedFlagShape F₂ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₁ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₂ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₁ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₂ ∧
      flagStabilizer e F₁ ⊔ flagStabilizer e F₂ = ⊤ ∧
      flagOvergroup e F₁ ((S : Subgroup H).map H.subtype) ∈
        Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      flagOvergroup e F₂ ((S : Subgroup H).map H.subtype) ∈
        Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      flagOvergroup e F₁ ((S : Subgroup H).map H.subtype) ⊔
        flagOvergroup e F₂ ((S : Subgroup H).map H.subtype) =
          L ⊔ (S : Subgroup H).map H.subtype := by
  obtain ⟨F₁, F₂, hs₁, hs₂, hi₁, hi₂, hS₁, hS₂, hgen⟩ :=
    exists_invariant_flag_pair h e hn ht ht2
  exact ⟨F₁, F₂, hs₁, hs₂, hi₁, hi₂, hS₁, hS₂, hgen,
    flagOvergroup_mem_HeOver h e ht ht2 F₁ hi₁ hS₁,
    flagOvergroup_mem_HeOver h e ht ht2 F₂ hi₂ hS₂,
    flagOvergroups_generate e F₁ F₂ _ hgen⟩

/-- Application to the source's local block input from 2.3.8(4): one of the
constructed flag overgroups contains an actual escaping block, subnormal
in that overgroup and moved by the specified Thompson subgroup.
The binary block-calculation consumer can use this witness directly. -/
theorem exists_escapingBlock_in_flagOvergroup
    (h : LocalSetup H L M S z) (e : L ≃* PSL n)
    (hn : n = 5 ∨ n = 4 ∧
      ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype))
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ F : Flag n, ExcludedFlagShape F ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F ∧
      flagOvergroup e F ((S : Subgroup H).map H.subtype) ∈
        Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      ∃ B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)),
        EscapingBlock M ((S : Subgroup H).map H.subtype)
          (flagOvergroup e F ((S : Subgroup H).map H.subtype)) B := by
  obtain ⟨F₁, F₂, hs₁, hs₂, hi₁, hi₂, hS₁, hS₂, _, he₁, he₂, hgen⟩ :=
    exists_invariant_parabolic_pair h e hn ht ht2
  have hL : L ≤ flagOvergroup e F₁ ((S : Subgroup H).map H.subtype) ⊔
      flagOvergroup e F₂ ((S : Subgroup H).map H.subtype) := by
    rw [hgen]
    exact le_sup_left
  rcases exists_escapingBlock_of_pair h.blocks h.outside hL
    (flagOvergroup_le e F₁ _) (flagOvergroup_le e F₂ _) he₁ he₂ with hB | hB
  · exact ⟨F₁, hs₁, hi₁, hS₁, he₁, hB⟩
  · exact ⟨F₂, hs₂, hi₂, hS₂, he₂, hB⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
