module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import CFSG.Quasithin.Defs

/-!+# The full pushing-up input for the L₂ branch

`DistinguishedPairs` fixes the characteristic choices on the two-groups,
independently of their embeddings in overgroups. `C126Source` is an explicit
earlier-theorem hypothesis, not a proof of C.1.26. Its third alternative
retains the whole central product, the transitive Sylow action, and the
commutator condition on every factor. In particular it does not identify
the selected component with one of those factors.

The characteristic alternatives can be excluded using 15.3.29 when the
Sylow subgroup is S. Applying the same argument with R instead would
require a separate bridge: characteristic subgroups of R need not be
characteristic in S.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.18–20
and C.1.26, printed pp.126–127 and 132; 15.3.29–30, pp.1131–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

universe u

/-- Choices of the distinguished C₁ and C₂ on each nontrivial two-group.
The existence and universal properties come from the earlier pushing-up
theorems; the structural fields alone do not assert those theorems. -/
structure DistinguishedPairs where
  pair : ∀ (T : Type u) [Group T] [Finite T] [Nontrivial T], IsPGroup 2 T →
    ChapterC.RankOneCharacteristicPair (ChapterB.baumann (⊤ : Subgroup T))

/-- The complete third conclusion of C.1.26, with actual subgroups of H.
Pairwise commuting factors generating O²(H) express their internal central
product. Both invariance and transitivity under the given T are retained. -/
structure ResidualBlockProduct (H : Type u) [Group H] (T : Sylow 2 H) where
  factors : Set (Subgroup H)
  nonempty : factors.Nonempty
  block : ∀ K ∈ factors, ChapterC.IsBlock K ∧ ChapterC.IsChiZeroBlock K
  generate : sSup factors = pResidual 2 H
  commute : factors.Pairwise fun K L => ⁅K, L⁆ = ⊥
  invariant : ∀ K ∈ factors, ∀ t : T,
    K.map (MulAut.conj (t : H)).toMonoidHom ∈ factors
  transitive : ∀ K ∈ factors, ∀ L ∈ factors, ∃ t : T,
    K.map (MulAut.conj (t : H)).toMonoidHom = L
  commutator : ∀ K ∈ factors, K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup H)⁆

/-- C.1.26's three alternatives for a fixed distinguished pair. The
second member is embedded first from Baum(T) into T, then into H. -/
def C126Alternatives {H : Type u} [Group H] (T : Sylow 2 H)
    (C : ChapterC.RankOneCharacteristicPair (ChapterB.baumann (⊤ : Subgroup T))) : Prop :=
  C.first.map (T : Subgroup H).subtype ≤ center H ∨
    ((C.second.map (ChapterB.baumann (⊤ : Subgroup T)).subtype).map
      (T : Subgroup H).subtype).Normal ∨ Nonempty (ResidualBlockProduct H T)

/-- The universal earlier implication C.1.26, relative to the genuine
known-simple catalogue and the distinguished choices. Nontriviality of T
is forced by minimal parabolicity, as proved below. -/
def C126Source (𝒦 : GroupClass.{u}) (choices : DistinguishedPairs.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK 𝒦 H →
    Theory.GroupTheory.generalizedFitting H = pCore 2 H →
    ∀ (T : Sylow 2 H) [Nontrivial T], ChapterB.IsMinimalParabolicOver T ⊤ →
      C126Alternatives T (choices.pair T T.isPGroup')

/-- A Sylow subgroup in a minimal parabolic is nontrivial; otherwise it
would be normal, contrary to the second clause of B.6.1. -/
theorem sylow_nontrivial_of_minimalParabolic {H : Type*} [Group H]
    (T : Sylow 2 H) (h : ChapterB.IsMinimalParabolicOver T ⊤) : Nontrivial T := by
  apply (Subgroup.nontrivial_iff_ne_bot _).mpr
  intro he
  have hn : (T : Subgroup H).Normal := by rw [he]; infer_instance
  exact (ChapterB.isMinimalParabolicOver_top_iff T).mp h |>.2 hn

/-- Once minimal parabolicity is proved for the same Sylow subgroup,
the genuine nonnormality assertion excludes both characteristic branches.
This does not supply minimal parabolicity or select a factor of the product. -/
theorem blockProduct_of_characteristic_exclusion {H : Type u} [Group H]
    (T : Sylow 2 H)
    (C : ChapterC.RankOneCharacteristicPair (ChapterB.baumann (⊤ : Subgroup T)))
    (hC : C126Alternatives T C)
    (hpush : ∀ A : Subgroup T, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (T : Subgroup H).subtype).Normal) :
    Nonempty (ResidualBlockProduct H T) := by
  rcases hC with hcentral | hnormal | hblocks
  · have hn : (C.first.map (T : Subgroup H).subtype).Normal := by
      constructor
      intro x hx g
      rw [mem_center_iff.mp (hcentral hx) g, mul_inv_cancel_right]
      exact hx
    exact (hpush C.first C.first_characteristic C.first_ne_bot hn).elim
  · let : (ChapterB.baumann (⊤ : Subgroup T)).Characteristic :=
      ChapterB.baumann_characteristic
    exact (hpush _ C.second_image_characteristic C.second_image_ne_bot hnormal).elim
  · exact hblocks

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

end
