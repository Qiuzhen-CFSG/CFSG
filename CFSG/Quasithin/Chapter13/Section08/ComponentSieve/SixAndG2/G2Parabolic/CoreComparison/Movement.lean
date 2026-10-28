module

public import Theory.GroupTheory.CentralLineCentralizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.FaithfulDisplacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.CoreMovement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Cover

/-!
# Movement on the actual core-comparison section

The central commutator pairing makes C_{Q_H}(A₁) have index at most two
in Q_H. Its coordinate image consequently has codimension at most one in
Q_H/H_C. A faithful rank-two G₂ actor has fixed codimension at least three,
so it cannot fix this entire image. The moved vector is constructed in the
literal source section, without assuming its movement or changing Dγ.

Faithfulness of the comparison is the earlier 13.7.4(1) input, transferred
by the contragredient pairing in 13.7.4(2). Source: Aschbacher–Smith 13.8.27,
printed p.963. Final source assembly belongs to qt-d-138-six-g2-source.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
variable {G : Type*} [Group G] [Finite G]
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry
variable {X W : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup W] [Module (ZMod 2) W]
  {L T H V V₃ V₁ K : Subgroup G}

/-- A faithful literal core comparison must move the line-centralizer image.
Its codimension is at most one by the central commutator pairing. -/
theorem core_movement_of_faithful_comparison
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) W)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcard : Nat.card V₁ = 2)
    (hUQ : Source.UH H V₃ ≤ Source.QH H)
    (hAone : c.Aone V₁ ≤ Source.UH H V₃)
    (hcomm : ⁅Source.QH H, Source.UH H V₃⁆ ≤ V₁)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 2)
    (τ : Representation (ZMod 2) (Source.Hstar H) X) (hτ : Function.Injective τ)
    (tQ : BinaryConjugationSection H (Source.QH H) (Source.HC H V₃)
      (τ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    ∃ a ∈ Source.starImage H (c.Ugamma V₃),
      ∃ v ∈ tQ.imageSpace (Source.QH H ⊓ centralizer (c.Aone V₁ : Set G)), τ a v ≠ v := by
  let : Finite X := Finite.of_surjective (fun q : Source.QH H => (tQ.coordinates q).toAdd)
    (Multiplicative.toAdd.surjective.comp tQ.onto)
  let R := Source.QH H ⊓ centralizer (c.Aone V₁ : Set G)
  have hcardA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj (c.gb : G)).injective, hcard]
  have hi : R.relIndex (Source.QH H) ≤ 2 :=
    line_centralizer_index_le_two (Source.QH H) V₁ (c.Aone V₁) hcard hcardA
      (hAone.trans hUQ) ((commutator_mono le_rfl hAone).trans hcomm)
      ((le_centralizer_iff.mp s.centralizes).trans (centralizer_le tQ.section_le))
  have hCR : Source.HC H V₃ ≤ R :=
    le_inf tQ.kernel_le (inf_le_right.trans (centralizer_le hAone))
  have hcod := faithful_fixedCodim_ge_three_of_fitting τ (Source.starImage H K) hfit hτ
    ((Components.componentStarEquiv H K hKH hK).symm.trans eK) hA hrank
  by_contra hn
  push Not at hn
  have hfix : tQ.imageSpace R ≤ fixedSpace τ (Source.starImage H (c.Ugamma V₃)) := by
    intro v hv a
    exact hn a a.property v hv
  have hdim := Submodule.finrank_mono hfix
  have hsum := fixedCodim_add_finrank τ (Source.starImage H (c.Ugamma V₃))
  have hpos : R.relIndex (Source.QH H) ≠ 0 := (R.subgroupOf (Source.QH H)).index_ne_zero_of_finite
  have hieq : R.relIndex (Source.QH H) = 1 ∨ R.relIndex (Source.QH H) = 2 := by omega
  rcases hieq with hh | hh
  · have hd := tQ.imageSpace_codimension_of_index R inf_le_left hCR 0 (by simpa using hh)
    omega
  · have hd := tQ.imageSpace_codimension_of_index R inf_le_left hCR 1 (by simpa using hh)
    omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
