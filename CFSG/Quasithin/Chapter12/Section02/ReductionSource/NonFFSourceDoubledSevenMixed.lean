module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenTwoImage
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenOddElements

/-!
# Odd and even actors at an unresolved small A₇ centralizer

E.6.27 excludes two-group images, and the proved maximal-obstruction
argument excludes odd images. Cauchy's theorem and the H.8 pair then
supply an involution and a cubic in the same original local image.
The odd-prime estimate also identifies that cubic as a double three-cycle
under the actual H.8 equivalence. Only original odd-normalizer control
is retained; the mixed-image exclusion remains a separate argument.

Source: Aschbacher--Smith, 7.5.5, p.701, E.6.11 and E.6.27.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_seven_small_escape_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hUW : U ≤ D.sourceOrbit) (hc : subgroupCorank D.sourceOrbit U < 6)
    (he : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    ∃ s : Automizer D.sourceOrbit,
      s ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ∧
      orderOf s = 3 := by
  have hU : U ≠ ⊥ := by
    intro hb
    rw [hb,Section06.corank_bot,D.sourceOrbit_seven_dimension h hd σ hmodel] at hc
    omega
  let I := inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G))
  have hn : ¬ IsPGroup 2 I := fun hh =>
    he (D.sourceOrbit_seven_two_image_centralizer h hd σ hσ hmodel hodd hU hUW hh)
  have hns : ¬ (Nat.card I).primeFactors ⊆ ({2} : Finset ℕ) := by
    intro hh
    apply hn
    exact (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr (by simpa only [Nat.prime_two.primeFactors] using hh)
  obtain ⟨p,hp,hp2⟩ := Finset.not_subset.mp hns
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  have hne : p ≠ 2 := by simpa using hp2
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hs' : orderOf (s : Automizer D.sourceOrbit) = p := (Subgroup.orderOf_coe s).trans hs
  obtain ⟨_,_,_,P,E,_,_⟩ := D.sourceOrbit_seven_H8_pair h hd σ hσ hmodel
  have hcodeq : fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers s.val) =
      fixedCodim P.representation (zpowers (E.groupEquiv s.val)) := by
    simpa only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom] using
      fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit) P.representation
        E.groupEquiv.toMonoidHom E.linearEquiv E.intertwines (zpowers s.val)
  have hbound : fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers s.val) ≤
      subgroupCorank D.sourceOrbit U := by
    apply (fixedCodim_mono (automizerRepresentation D.sourceOrbit) (zpowers_le.mpr s.property)).trans
    rw [fixedCodim_inducedAutomizer D.sourceOrbit _
      ((D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).localCentralizer_le_normalizer hU hUW)]
    exact Section06.subgroupCorank_antitone (le_inf hUW (le_centralizer_iff.mpr inf_le_right))
  have horder := (orderOf_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective s.val).trans hs'
  have hthree := (doubledSeven_small_odd_prime P (E.groupEquiv s.val)
    (horder ▸ hprime) (horder ▸ hne) (hcodeq ▸ hbound.trans_lt hc)).1
  exact ⟨s.val,s.property,hs'.trans (horder.symm.trans hthree)⟩

/-- Any unresolved small escaping centralizer has both an involution and
a cubic in its action on the same orbit; pure two-group and odd images
have already been excluded. -/
theorem sourceOrbit_seven_small_escape_mixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hUW : U ≤ D.sourceOrbit) (hc : subgroupCorank D.sourceOrbit U < 6)
    (he : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    ∃ t s : Automizer D.sourceOrbit,
      t ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ∧
      s ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ∧
      orderOf t = 2 ∧ orderOf s = 3 := by
  obtain ⟨t,ht,ht2,_⟩ := D.sourceOrbit_seven_small_escape_involution h hd σ hσ hmodel hUW hc he
  obtain ⟨s,hs,hs3⟩ := D.sourceOrbit_seven_small_escape_cubic h hd σ hσ hmodel hodd hUW hc he
  exact ⟨t,s,ht,hs,ht2,hs3⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
