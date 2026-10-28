module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Module
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder
public import Stellmacher.BaumannTwoOvergroupTransport
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# Moving the mixed factors into the generated group

The ambient equality `C_G(Z)=T` and the prescribed Sylow subgroup of `I`
give the intrinsic equality `C_I(Z)=Tᵢ`. Baumann containment gives
`J(Tᵢ)=J(T)`, with the exact inclusion maps retained. Thus both factor
commutator identities transport into `I`, even though the second factor
need not belong to the full `T`-invariant Y-family. Nontrivial commutators
and the final normalizer containment are transported by the same inclusions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.18, printed pp.1162–1163.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open Subgroup Stellmacher
variable {G : Type*} [Group G]

/-- The specified local Sylow subgroup is the full centralizer of the seed inside I. -/
theorem centralizer_seed_subgroupOf (I T Z : Subgroup G)
    (P : Sylow 2 I) (hT : IsPGroup 2 T)
    (hPT : (P : Subgroup I).map I.subtype ≤ T) (hZI : Z ≤ I)
    (hCZ : centralizer (Z : Set G) = T) :
    centralizer (Z.subgroupOf I : Set I) = (P : Subgroup I) := by
  apply map_injective I.subtype_injective
  rw [map_centralizer_subtype, map_subgroupOf_eq_of_le hZI, hCZ, inf_comm,
    inf_eq_sylow_map P hT hPT]

/-- Containing the original Thompson subgroup preserves the maximum elementary order and Thompson subgroup. -/
theorem thompson_intermediate_eq [Finite G] (T Tᵢ : Subgroup G)
    (hTᵢ : Tᵢ ≤ T) (hJ : elementaryAbelianMaxJ T ≤ Tᵢ) :
    elementaryAbelianMaxJ Tᵢ = elementaryAbelianMaxJ T := by
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq Tᵢ T hTᵢ
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le T Tᵢ hJ
  have ho := le_antisymm hs.1 hl.1
  exact le_antisymm (hs.2 ho) (hl.2 ho.symm)

/-- The intrinsic Thompson subgroup maps onto the original one. -/
theorem thompson_sylow_image [Finite G] (I T : Subgroup G) (P : Sylow 2 I)
    (hPT : (P : Subgroup I).map I.subtype ≤ T)
    (hJ : elementaryAbelianMaxJ T ≤ (P : Subgroup I).map I.subtype) :
    (elementaryAbelianMaxJ (P : Subgroup I)).map I.subtype = elementaryAbelianMaxJ T := by
  rw [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective]
  exact thompson_intermediate_eq T _ hPT hJ

/-- The source Baumann containment supplies the exact Thompson image equality. -/
theorem thompson_sylow_image_of_baumann [Finite G] (I : Subgroup G)
    (T : Sylow 2 G) (P : Sylow 2 I)
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype) :
    (elementaryAbelianMaxJ (P : Subgroup I)).map I.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
  rw [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective]
  exact (twoSubgroup_thompson_baumann_eq T _ (P.isPGroup'.map I.subtype) hB).1

/-- Transport the raw factor commutator identity, without any family-membership claim. -/
theorem factor_commutator_subgroupOf (I Y J : Subgroup G) (Jᵢ : Subgroup I)
    (hYI : Y ≤ I) (hJ : Jᵢ.map I.subtype = J) (hY : Y = ⁅Y, J⁆) :
    Y.subgroupOf I = ⁅Y.subgroupOf I, Jᵢ⁆ := by
  apply map_injective I.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hYI, hJ]
  exact hY

/-- Nontrivial seed commutators remain nontrivial inside the generated group. -/
theorem seed_factor_commutator_ne_bot_subgroupOf (I Z Y : Subgroup G)
    (hZI : Z ≤ I) (hYI : Y ≤ I) (hZY : ⁅Z, Y⁆ ≠ ⊥) :
    ⁅Z.subgroupOf I, Y.subgroupOf I⁆ ≠ ⊥ := by
  intro hb
  have hm := congrArg (fun A : Subgroup I => A.map I.subtype) hb
  rw [map_commutator, map_subgroupOf_eq_of_le hZI,
    map_subgroupOf_eq_of_le hYI, Subgroup.map_bot] at hm
  exact hZY hm

/-- Intrinsic normalization lifts to the actual ambient factors. -/
theorem normalizer_subgroupOf_lift (I Y₁ Y₂ : Subgroup G)
    (h₁ : Y₁ ≤ I) (h₂ : Y₂ ≤ I)
    (hn : Y₂.subgroupOf I ≤ normalizer (Y₁.subgroupOf I : Set I)) :
    Y₂ ≤ normalizer (Y₁ : Set G) := by
  rw [← subgroupOf_normalizer_eq h₁] at hn
  intro x hx
  exact hn (show (⟨x, h₂ hx⟩ : I) ∈ Y₂.subgroupOf I from hx)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
