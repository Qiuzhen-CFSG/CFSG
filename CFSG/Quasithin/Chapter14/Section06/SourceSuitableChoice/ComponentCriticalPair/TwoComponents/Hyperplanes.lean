module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.Endpoints
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes

/-!
# The terminal natural/dual hyperplane step

The literal denominator D is the commutator preimage of the critical
point. Its index bounds the indices on both original supports. Genuine
natural and dual coordinates therefore force that point into one of the
supports when the induced actor has rank two. The point order, its
normalization, and the common commutator bound are obtained from the
original F.9 setup and the same critical conjugator.

Source: Aschbacher--Smith 14.6.24(3), printed p.1041. Establishing the
index-two denominator and the rank-two inner actor is the preceding
source argument, and remains explicit here. This theorem does not assert
the earlier placement in one of the two component supports on p.1040.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The rank-two inner-actor branch places the original critical point
inside a natural summand or its dual. No support placement or displacement
dimension is assumed. The preceding strict-rank argument supplies hindex
and hrank, and 14.6.22 supplies the two marked sections. -/
theorem source_point_in_natural_or_dual_of_index_two
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (A W Wdual : Subgroup G)
    (π : A →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (c : BinaryConjugationSection A W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π))
    (cdual : BinaryConjugationSection A Wdual (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π)))
    (hactor : i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ A)
    (hW : W ≤ conjugateSpanBy (localModule T M) Mc)
    (hWdual : Wdual ≤ conjugateSpanBy (localModule T M) Mc)
    (hindex : (commutatorPreimage (conjugateSpanBy (localModule T M) Mc)
        (i.conjugate (conjugateSpanBy (localModule T M) Mc))
        (i.conjugate (centralInvolutions T))).relIndex
        (conjugateSpanBy (localModule T M) Mc) = 2)
    (hrank : 2 ≤ rank (((i.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf A).map π)) :
    i.conjugate (centralInvolutions T) ≤ W ∨
      i.conjugate (centralInvolutions T) ≤ Wdual := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let Ug := i.conjugate U
  let Zg := i.conjugate Z
  let D := commutatorPreimage U Ug Zg
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  have hUgH : Ug ≤ Mc := i.large_le hb
  have hZU : Z ≤ U := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hZD : Z ≤ D := by
    apply le_commutatorPreimage hZU
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hUgH.trans h.H_centralizes))).le.trans bot_le
  have hUZg : U ≤ normalizer (Zg : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (i.reverse_le hb).trans hn
  have hc : ⁅Ug,D⁆ ≤ Zg := by
    rw [commutator_comm]
    exact commutator_commutatorPreimage_le U Ug Zg hUZg
  have hz : Nat.card Zg = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  let σ : Representation (ZMod 2) (BinaryLinear.GL (Fin 3 → ZMod 2)) (Fin 3 → ZMod 2) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hf : Function.Injective σ := by
    intro x y hxy
    exact LinearEquiv.toLinearMap_injective hxy
  let : Finite (BinaryLinear.GL (Fin 3 → ZMod 2)) :=
    Finite.of_injective (fun a : BinaryLinear.GL (Fin 3 → ZMod 2) =>
      (a : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective
  have hd : Representation.dual (σ.comp π) = σ.dual.comp π := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (σ (π a⁻¹) v) = f (σ ((π a)⁻¹) v)
    rw [map_inv]
  rw [hd] at cdual
  exact BinaryConjugationSection.line_le_one_of_dual_supports
    A U Z Ug D Zg W Wdual σ hf π c cdual hactor hW hWdual hZD hindex.le hrank hz hc

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
