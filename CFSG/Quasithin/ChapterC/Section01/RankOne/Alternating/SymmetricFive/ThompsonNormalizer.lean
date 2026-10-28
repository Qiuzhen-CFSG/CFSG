module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.IndexTwo
public import Theory.Representation.BinaryPermutation.FivePairFixedSpaces
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Cubic obstruction to the original S₅ Thompson normalizer

The source transposition four-group has normalizer of order eight, also
after conjugating the marking. A cubic injects through a two-group kernel,
so it cannot normalize that image. The genuine reduced S₅ quotient theorem
identifies the original J(T) image and supplies the source application.

Source: Aschbacher–Smith 5.1.13, printed p.637, symmetric-five branch,
using C.1.24 and E.2.3, printed pp.130–131,216–217.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.SymmetricFive

private theorem source_D_eq_pair : ChapterB.Offenders.D 5 =
    BinaryPermutation.FivePairFixedSpaces.pairClosure := by
  apply congrArg Subgroup.closure
  ext g
  constructor
  · rintro ⟨i, _, rfl⟩
    fin_cases i <;> simp [ChapterB.Offenders.pairSwap,
      BinaryPermutation.FivePairFixedSpaces.first, BinaryPermutation.FivePairFixedSpaces.second]
  · intro hg
    rcases hg with rfl | hg
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, hg⟩

/-- The actual transposition four-group has a two-group normalizer. -/
theorem source_thompson_image_normalizer_card (a : Equiv.Perm (Fin 5)) :
    Nat.card (normalizer (((ChapterB.Offenders.D 5).map
      (MulAut.conj a).toMonoidHom) : Set (Equiv.Perm (Fin 5)))) = 8 := by
  rw [← map_equiv_normalizer_eq, card_map_of_injective (MulAut.conj a).injective,
    source_D_eq_pair, BinaryPermutation.FivePairFixedSpaces.card_pairNormalizer]

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A cubic survives a two-kernel, so it cannot normalize the source S₅
Thompson image, whose full normalizer has order eight. -/
theorem cubic_not_normalizes_thompson_of_image
    (T : Sylow 2 G) (q : G →* Equiv.Perm (Fin 5))
    (hk : IsPGroup 2 q.ker) (D : Subgroup G) (hD : Nat.card D = 3)
    (a : Equiv.Perm (Fin 5))
    (hj : (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom) :
    ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hi : Function.Injective (q.subgroupMap D) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro d hd
    apply Subtype.ext
    exact mem_bot.mp ((hDp.disjoint_of_coprime hk (by decide)).le_bot
      ⟨d.property, show q d.val = 1 from congrArg Subtype.val hd⟩)
  have hc : Nat.card (D.map q) = 3 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap D)
      ⟨hi,q.subgroupMap_surjective D⟩).toEquiv).symm.trans hD
  intro hn
  have him : D.map q ≤ normalizer ((elementaryAbelianMaxJ (T : Subgroup G)).map q : Set _) :=
    (map_mono hn).trans (le_normalizer_map q)
  have hh := card_dvd_of_le him
  rw [hc,hj,source_thompson_image_normalizer_card] at hh
  norm_num at hh

/-- The original reduced S₅ action discharges the image premise above. -/
theorem source_cubic_not_normalizes_thompson
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hk : IsPGroup 2 q.ker)
    (f : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f v))
    (hfk : f.ker = fixedSpace (NormalElementaryQuotient.representation U q hq hker)
      ((pResidual 2 G).map q))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (D : Subgroup G) (hD : Nat.card D = 3) :
    ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hh := source_natural_quotient_conclusions T hP U hU q hq hker f hf he hJ hfk
  obtain ⟨a,ha⟩ := hh.2.2.1
  exact cubic_not_normalizes_thompson_of_image T q hk D hD a (hh.1.trans ha)
end CFSG.Quasithin.ChapterC.SymmetricFive
