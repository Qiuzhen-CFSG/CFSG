module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Consequences
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Block
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Core
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.LocalReduction

/-!
# Source consequences of the order-32 block-core calculation at the original G,T

The actual intersection T∩L is Sylow in L, by normality inside LT. Its
order is64, so the original U has index two. Identifying V with O₂(L)
also makes N_G(L) normalize V. The source factorization of the seed
normalizer therefore applies to all of N_G(L), giving M=L(M∩H).

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem component_sylow (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ P : Sylow 2 L, (P : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let J := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer (show L ≤ J from le_sup_left)).mpr
    (sup_le L.le_normalizer hTL)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let e : N ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup N).map e.toMonoidHom = (T : Subgroup G).subgroupOf L
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

/-- The literal T∩L has order64 and U has index two in it. -/
theorem source_sylow_index (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 64 ∧
      F.U.relIndex ((T : Subgroup G) ⊓ L) = 2 := by
  let := setup.chosen.elementary
  let H := setup
  obtain ⟨hV, hUL⟩ := source_block_core d setup structural alternatives F hne hZ hcard
  obtain ⟨P, hP⟩ := component_sylow (H.sylow_normalizes_at structural)
  have hPc : Nat.card P = 64 := by
    apply DimensionFour.SplitImage.InvolutionSplitting.sylow_card_of_block_quotient (pCore 2 L)
    · have hh : Nat.card (L.pCoreIn 2) = Nat.card (pCore 2 L) :=
        card_map_of_injective L.subtype_injective
      rw [← hh, ← hV]
      simpa [F.last] using F.card 3 (by decide)
    · exact H.naturalMarking.quotientEquiv.trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
  have hTLc : Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 64 := by
    have he : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
      rw [hP, subgroupOf_map_subtype]
    rw [← he, card_map_of_injective L.subtype_injective]
    exact hPc
  refine ⟨hTLc, ?_⟩
  have hUT : F.U ≤ (T : Subgroup G) ⊓ L :=
    le_inf (source_closure_le_sylow d setup structural alternatives F) hUL
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) F.U ((T : Subgroup G) ⊓ L) bot_le hUT
  rw [relIndex_bot_left, relIndex_bot_left, hcard, hTLc] at hi
  omega

/-- The actual normalizer of L normalizes the now-identified seed. -/
theorem source_normalizer_le_seed_normalizer (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    normalizer (L : Set G) ≤ normalizer (V : Set G) := by
  have he := (source_block_core d setup structural alternatives F hne hZ hcard).1
  rw [he]
  exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
