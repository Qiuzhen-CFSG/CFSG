module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Block
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Core
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.LocalReduction
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Source consequences of the order-32 block-core calculation

The actual intersection T∩L is Sylow in L, by normality inside LT. Its
order is64, so the original U has index two. Identifying V with O₂(L)
also makes N_G(L) normalize V. The source factorization of the seed
normalizer therefore applies to all of N_G(L), giving M=L(M∩H).

The final theorem applies the proved seed-core equality to the existing
I.4.5 configuration consumer. Equality U=O₂(H), the order-eighteen
quotient and the actual generating inverter remain to be constructed by
qt-d-14414-g2-source through the nonsplit and fusion arguments. These are
explicit remaining source obligations, not hypotheses of the block-core
calculation. Universal I.4.5 remains with qt-i45-g2-recognition.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.3.7 and14.4.4(4–7), printed pp.992,1007–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
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
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 64 ∧
      F.U.relIndex ((T : Subgroup G) ⊓ L) = 2 := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨hV, hUL⟩ := source_block_core d earlier hq chosen structural alternatives F hne hZ hcard
  obtain ⟨P, hP⟩ := component_sylow (H.sylow_normalizes structural)
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
    le_inf (source_closure_le_sylow d earlier hq chosen structural alternatives F) hUL
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) F.U ((T : Subgroup G) ⊓ L) bot_le hUT
  rw [relIndex_bot_left, relIndex_bot_left, hcard, hTLc] at hi
  omega

/-- The actual normalizer of L normalizes the now-identified seed. -/
theorem source_normalizer_le_seed_normalizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    normalizer (L : Set G) ≤ normalizer (V : Set G) := by
  have he := (source_block_core d earlier hq chosen structural alternatives F hne hZ hcard).1
  rw [he]
  exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)

/-- The first factorization in the ambient normalizer argument, with the
source core equality supplied rather than assumed. -/
theorem source_normalizer_factorization (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    (normalizer (L : Set G) : Set G) =
      (L : Set G) * (normalizer (L : Set G) ⊓ F.H : Subgroup G) := by
  have he : seedNormalizer (normalizer (L : Set G)) V = normalizer (L : Set G) :=
    inf_eq_left.mpr (source_normalizer_le_seed_normalizer d earlier hq chosen structural
      alternatives F hne hZ hcard)
  simpa only [he] using point_normalizer_factorization d earlier hq chosen structural F

/-- The configuration consumer no longer needs the unproved seed-core equality.
The remaining local fields are retained here for the same source assembly owner. -/
theorem configuration_of_source_closure (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (hcore : F.U = F.H.pCoreIn 2) (hquotient : Nat.card (HStar F.H) = 18)
    (s : F.H) (hgen : pResidual 2 F.H ⊔ zpowers s = ⊤)
    (hinv : ∀ k : pResidual 2 F.H,
      QuotientGroup.mk' (pCore 2 F.H) (s * k * s⁻¹) =
        (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) := by
  apply configuration_of_source_local d earlier hq chosen structural alternatives F hne hZ hcard
  exact ⟨(source_block_core d earlier hq chosen structural alternatives F hne hZ hcard).1,
    hcore, hquotient, s, hgen, hinv⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
