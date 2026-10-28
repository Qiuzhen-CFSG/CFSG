module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.SourceDecomposition
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.Outer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.SymmetricThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Algebra

/-!
# The complete solvable exclusion in 13.6.13

The adequate B.5 list and the five genuine earlier classification inputs
construct the original normal S₃ decomposition. The marked seed rules out
the hyperplane and singleton product choices; the surviving product uses
its literal two support planes. Minimality then makes the factors transitive,
and the actual cubic L_v projection forces one factor. Its plane bounds
[U_v,L_v], while its normal residual makes L_v* normal. The earlier local
module identity consequently makes V_v normal, contrary to 13.6.8.

The decomposition, movement, factor projection, moved-space bound, and
normality are all derived here. The universal earlier B.5/A.2/A.3 inputs
remain explicit and must be discharged by the final source assembly.
Source: Aschbacher--Smith, combined manuscript, 13.6.13, printed p.929.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
open Construction
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hT : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hV : IsPGroup 2 V)
    (hL : Lv L (A5Module.markedV s) ≤ normalizer (V : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hsplit : Vv L (A5Module.markedZ s) (A5Module.markedV s) =
      zpowers (A5Module.markedV s) ⊔ ⁅V, Lv L (A5Module.markedV s)⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L (A5Module.markedV s)⁆ : Subgroup G) = 4)
    (hnormal : ¬ ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal)

include S hS hfix hT hV hL hcubic hsplit hsmall hnormal

/-- The original decomposition is now constructed in every surviving
classification branch. The adequate classifier and genuine earlier source
statements retain their full universal contracts. -/
theorem normalS3Decomposition_of_earlier_source
    {𝒦 : GroupClass.{u}}
    (earlier : Exceptional.SourceAction.PreciseInputs.{u,u} 𝒦)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hlocal : IsSQTK 𝒦 (Gv (A5Module.markedV s)))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X) :
    Nonempty (NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) := by
  rcases Exceptional.minimalSolvable_remaining_source_alternatives
    s T S hS hfix hT hV hL hcubic hsplit hsmall hnormal hX earlier classification hlocal with
    c | c | c
  · obtain ⟨c⟩ := c
    exact normalS3Decomposition_of_symmetricThree L T _ _
      (A5Module.markedZ_mem_Gv s) S hS hX.1 c
  · obtain ⟨c⟩ := c
    exact Products.normalS3Decomposition_of_source_twoFactors s T S hS hfix hT hcubic hX c
  · obtain ⟨c⟩ := c
    exact (Products.source_hyperplane_excluded s T S hS hfix hT hcubic hX c).elim

/-- Any constructed normal-factor configuration contradicts the earlier
source nonnormality of V_v. All classification bounds are proved from the
literal supports, rather than supplied as extra premises. -/
theorem false_of_normalS3Decomposition
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) : False := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  obtain ⟨_, i, hi⟩ := FactorArgument.marked_factor_identification s T S hS hfix hT hcubic hX d
  have htrans := d.factorsTransitive L T hX S hS
  have hnorm := FactorArgument.starTv_normalizes_starLv L T z v hT
  have hcount := d.count_eq_one_of_transitive_invariant_residual T htrans _ hnorm i hi
  have he := d.eq_X_of_transitive_invariant_residual T htrans _ hnorm i hi
  have hcard : Nat.card (movedSubgroup z v d.H) = 4 := by
    rw [← Nat.card_congr d.space.toEquiv, Nat.card_pi]
    simp only [d.support_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hcount, pow_one]
  have hXH : X ≤ d.H := d.residual_eq.symm.le.trans (map_subtype_le _)
  have hLH : Lv L v ≤ starPreimage z v d.H := by
    intro a ha
    let a' : Gv v := ⟨a, Lv_le_Gv L v ha⟩
    refine ⟨a', hXH ?_, rfl⟩
    rw [← he]
    exact ⟨a', ha, rfl⟩
  have hlarge : Nat.card ↥(⁅Uv z v, Lv L v⁆ : Subgroup G) ≤ 4 := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective (inclusion (commutator_mono le_rfl hLH))
      (inclusion_injective _)
  have horbit : (normalizer (starImage z v (Lv L v) : Set (Gstar z v))).index ≤ 2 := by
    let : X.Normal := hX.1.2
    rw [he, normalizer_eq_top, index_top]
    decide
  exact Subnormal.contradiction_of_classification_bounds L V T z v S hS hT hV hL
    hsplit hsmall hlarge horbit hnormal

/-- Original 13.6.13: no member of the literal X-family is solvable.
Only the genuine earlier source configuration and classification theorems
are inputs; every intermediate factor and action conclusion is constructed. -/
theorem no_solvable_member_of_earlier_source
    {𝒦 : GroupClass.{u}}
    (earlier : Exceptional.SourceAction.PreciseInputs.{u,u} 𝒦)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hlocal : IsSQTK 𝒦 (Gv (A5Module.markedV s))) :
    ∀ X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s), ¬ Group.IsSolvable X := by
  intro X hX hs
  obtain ⟨Y, _, hY⟩ := exists_minimal_solvable L T _ _ hX hs
  obtain ⟨d⟩ := normalS3Decomposition_of_earlier_source s T S hS hfix hT hV hL hcubic
    hsplit hsmall hnormal earlier classification hlocal hY
  exact false_of_normalS3Decomposition s T S hS hfix hT hV hL hcubic hsplit hsmall hnormal hY d

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
