module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.Projection

/-!
# The critical line in the whole-star natural quotient

The strict inclusion Uγ* < Vγ* and the actual two-rank of G₂(2) give
rank Uγ* < 3. The recognized component section supplies the compatible
whole-star projection, including in the Weyl case. The strict natural
offender ratio and the selected critical-pair inequality then force A₁≤U_H.

Source: Aschbacher–Smith 13.8.27, printed p.963, using 13.8.18(2),
13.8.11(1), and B.4.6(13).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry Atlas.G2

/-- A proper elementary overgroup gives the strict rank bound on the
original actor, through its injective embedding in the concrete model. -/
theorem rank_lt_three_of_proper_elementary
    {D : Type*} [Group D] [Finite D]
    (f : D →* Model (ZMod 2)) (hf : Function.Injective f)
    {A B : Subgroup D} (hA : IsElementaryTwo A)
    (hB : IsElementaryAbelian 2 B) (hproper : A < B) : rank A < 3 := by
  let := hB
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hbound := (primeRank_le_iff_elementary_card_le (Model (ZMod 2))).mp
    (show primeRank 2 (Model (ZMod 2)) ≤ 3 by
      simpa using (EvenTwoRank.two_rank (ZMod 2) (n := 1) (by norm_num)).le)
      (B.map f) inferInstance
  rw [card_map_of_injective hf] at hbound
  by_contra! hn
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  rw [← hA.card_eq_two_pow_rank] at hp
  exact hproper.ne (eq_of_le_of_card_ge hproper.le (hbound.trans hp))

variable {G : Type*} [Group G] [Finite G] {H K L T V V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Produce the whole-star marking and place the actual conjugate source
line in U_H. No full-module natural identification or rank callback is used. -/
theorem projection_and_line_of_section
    (c : CriticalPair L T H V)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Natural.OrthogonalCover.binaryNatural (ZMod 2)) eK)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hB : IsElementaryAbelian 2 (Source.starImage H c.Vgamma))
    (hproper : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma) :
    rank (Source.starImage H (c.Ugamma V₃)) < 3 ∧
    c.Aone V₁ ≤ Source.UH H V₃ ∧
    ∃ (f : Source.Hstar H →* Model (ZMod 2))
      (p : Additive (Source.Utilde H V₃ V₁) →ₗ[ZMod 2] Natural.Space (ZMod 2)),
      Function.Injective f ∧ Function.Surjective p ∧
      (∀ a : Source.starImage H K,
        f a = ((Components.componentStarEquiv H K hKH hK).symm.trans eK a : Model (ZMod 2))) ∧
      (∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v)) ∧
      p.ker = fixedSpace ρ (Source.starImage H K) := by
  obtain ⟨f, p, hf, hp, hfK, he, hk⟩ :=
    whole_star_projection_of_section hKH hK hfit ρ hρ hgen eK hs
  have hr := rank_lt_three_of_proper_elementary f hf hA hB hproper
  exact ⟨hr, Aone_le_of_natural_projection c s hUg hreverse hcard hcompare
    f hf p hp he hA hr, f, p, hf, hp, hfK, he, hk⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
