module
public import Theory.SpecificGroups.Rudvalis.Model.ExtraspecialFive
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.Representation.BinaryCoprimeDegree

/-!
# Rudvalis local degree and automorphism-rank inputs to G.7

The actual extraspecial subgroup of order 125 restricts the original faithful
binary representation and proves degree at least twenty. The proved intrinsic
two-rank, stabilizer-class invariance, and permutation self-normalization give
the automorphism-rank bound. Simplicity is inherited from the source simple
group through its actual model isomorphism. Faithful descent transports that
bound to perfect covers through their literal central quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.7.2(6) and the
Ru branch of G.7.3(2), printed pp.347–348 (PDF pp.358–359).
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.SporadicLocal
open Subgroup Theory.GroupTheory

/-- The actual Rudvalis carrier contains an extraspecial subgroup of order 5³. -/
theorem ru_contains_extraspecial_five :
    ∃ P : Subgroup Rudvalis.Model, IsExtraspecial 5 P ∧ Nat.card P = 5 ^ 3 :=
  ⟨Rudvalis.ExtraspecialFive.subgroup, Rudvalis.ExtraspecialFive.subgroup_extraspecial,
    Rudvalis.ExtraspecialFive.card_subgroup⟩

/-- The Ru row of G.7.2(6) in the original ambient faithful binary representation. -/
theorem ru_finrank_ge_twenty
    {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ≃* Rudvalis.Model) :
    20 ≤ Module.finrank (ZMod 2) V := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := Rudvalis.ExtraspecialFive.subgroup
  let : IsExtraspecial 5 P := Rudvalis.ExtraspecialFive.subgroup_extraspecial
  have h := Representation.BinaryCoprimeDegree.extraspecial_finrank_le (by decide : 5 ≠ 2)
    ((ρ.comp L.subtype).comp (e.symm.toMonoidHom.comp P.subtype))
    (hρ.comp (Subtype.val_injective.comp (e.symm.injective.comp Subtype.val_injective)))
    Rudvalis.ExtraspecialFive.card_subgroup
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five, Nat.reduceMul] using h

private theorem ru_center_eq_bot [IsSimpleGroup Rudvalis.Model] :
    center Rudvalis.Model = ⊥ := by
  rcases (inferInstance : (center Rudvalis.Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let := center_eq_top_iff.mp h
    exact (Rudvalis.ExtraspecialFive.xy_ne_yx
      (IsMulCommutative.is_comm.comm _ _)).elim

/-- The G.7.3(2) rank reduction with stabilizer-class invariance explicit. -/
theorem ru_automorphism_twoRank_le_six_of_stabilizer [IsSimpleGroup Rudvalis.Model]
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y) :
    primeRank 2 (MulAut Rudvalis.Model) ≤ 6 := by
  let e : Rudvalis.Model ≃* MulAut Rudvalis.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot ru_center_eq_bot,
      Chapter1.XiEmbedding.OuterModels.rudvalis_conj_surjective_of_action
        hstable Rudvalis.outer_permutation_normalizer_eq⟩
  rw [← primeRank_equiv 2 e]
  exact Rudvalis.primeRank_le_six

/-- Faithful automorphism descent along the literal central quotient of a perfect cover. -/
theorem ru_centralQuotient_automorphism_twoRank_le_six_of_stabilizer
    [IsSimpleGroup Rudvalis.Model]
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y)
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Rudvalis.Model) : primeRank 2 (MulAut L) ≤ 6 := by
  have h := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at h
  exact h.trans (ru_automorphism_twoRank_le_six_of_stabilizer hstable)

/-- The Ru automorphism-rank input to G.7.3(2), using the proved invariance of
the actual degree-4060 point-stabilizer class. Only source simplicity is retained. -/
theorem ru_automorphism_twoRank_le_six [IsSimpleGroup Rudvalis.Model] :
    primeRank 2 (MulAut Rudvalis.Model) ≤ 6 :=
  ru_automorphism_twoRank_le_six_of_stabilizer Rudvalis.outer_stabilizer_map_eq

/-- Transport both simplicity and the automorphism-rank bound along the source
group's actual isomorphism with the Rudvalis carrier. -/
theorem ru_automorphism_twoRank_le_six_of_equiv
    {S : Type*} [Group S] [IsSimpleGroup S] (e : S ≃* Rudvalis.Model) :
    primeRank 2 (MulAut S) ≤ 6 := by
  let : Finite S := Finite.of_injective e e.injective
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact ru_automorphism_twoRank_le_six

/-- The Ru rank bound for a finite perfect cover, with simplicity supplied by
its literal central quotient as in the quasisimple source hypothesis. -/
theorem ru_centralQuotient_automorphism_twoRank_le_six
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    [IsSimpleGroup (L ⧸ center L)]
    (e : L ⧸ center L ≃* Rudvalis.Model) : primeRank 2 (MulAut L) ≤ 6 :=
  (automorphism_primeRank_le_quotient_center (E := L) 2).trans
    (ru_automorphism_twoRank_le_six_of_equiv e)

end CFSG.Quasithin.ChapterG.Section07.SporadicLocal
