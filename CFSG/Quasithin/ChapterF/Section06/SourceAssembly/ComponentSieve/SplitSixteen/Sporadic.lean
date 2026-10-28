module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Sporadic
public import Theory.GroupTheory.ExponentFourSylowSections
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne

/-!
# Sporadic exclusion for the split Sylow sixteen branch

All source Theorem C sporadic models except M₁₁ and J₁ have order divisible
by thirty-two. The actual M₁₁ model has an order-eight Sylow element, whereas
C₂ × D₈ and every Sylow subgroup of one of its sections have exponent four.
For J₁, the certified inner-automorphism theorem forces the perfect generalized
Fitting component to equal the ambient group. Its odd center then preserves
the two-part eight of the J₁ quotient, contradicting the ambient Sylow order
sixteen. Every model premise concerns the literal component central quotient.

Source: Aschbacher--Smith, F.6.18, printed p.310; Theorem C's source sporadic
list A.2.4. Concrete order, Sylow, and automorphism certificates are cited by
the imported carrier modules.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ClassificationModels CFSG.Quasithin.ChapterA.Section02
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen

/-- All named sporadic alternatives other than M₁₁ have a thirty-two factor. -/
theorem thirty_two_dvd_sporadic_name (name : SporadicName) (hne : name ≠ .j3)
    (hm : name ≠ .m11) :
    32 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 => exact (hm rfl).elim
  | m12 =>
      change 32 ∣ Nat.card Sporadic.Mathieu.M12
      rw [Sporadic.Mathieu.m12_order]
      norm_num
  | m22 =>
      change 32 ∣ Nat.card Sporadic.Mathieu.M22
      rw [Sporadic.Mathieu.m22_order]
      norm_num
  | m23 =>
      change 32 ∣ Nat.card Sporadic.Mathieu.M23
      rw [Sporadic.Mathieu.m23_order]
      norm_num
  | m24 =>
      change 32 ∣ Nat.card Sporadic.Mathieu.M24
      rw [Sporadic.Mathieu.m24_order]
      norm_num
  | j2 =>
      change 32 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
      norm_num
  | j3 => exact (hne rfl).elim
  | j4 =>
      change 32 ∣ Nat.card Janko4.Model
      let hA := Janko4.matrixA_mul_self
      let hB := Janko4.matrixB_pow_four
      have hk := (Janko4.Cardinality.localKernel hA hB).card_subgroup_dvd_card
      rw [Janko4.Cardinality.localKernel_card hA hB] at hk
      exact (show 32 ∣ 2048 by norm_num).trans
        (hk.trans (Janko4.Cardinality.max1Subgroup hA hB).card_subgroup_dvd_card)
  | hs =>
      change 32 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      norm_num
  | he =>
      change 32 ∣ Nat.card Held.He
      let K : Subgroup Held.He := Subgroup.closure
        (Set.range Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two.input)
      have hK : Nat.card K = 1024 :=
        Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two.order
      have hd := K.card_subgroup_dvd_card
      rw [hK] at hd
      exact (show 32 ∣ 1024 by norm_num).trans hd
  | ru =>
      change 32 ∣ Nat.card Rudvalis.Model
      rw [Rudvalis.model_card]
      norm_num

/-- The actual M₁₁ model cannot be a quotient of a subgroup below C₂ × D₈. -/
theorem not_mathieu_eleven_section
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (f : K →* Sporadic.Mathieu.M11) (hf : Function.Surjective f) : False := by
  obtain ⟨P,a,b,ha,hb,hconj,hgen⟩ := Sporadic.Mathieu.m11_exists_semidihedral_sylow
  have hp := split_sixteen_sylow_section_pow_four T eT K f hf P a
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [ha] at hd
  norm_num at hd

/-- J₁ cannot be the central quotient of the generalized Fitting component
when the center is odd and the ambient Sylow has order sixteen. -/
theorem not_janko_one_component
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (hT : Nat.card T = 16)
    (K : Subgroup G) (hF : generalizedFitting G = K)
    (hK : IsComponent G K) (hZ : Odd (Nat.card (center K)))
    (eK : (K ⧸ center K) ≃* Janko1.Model) : False := by
  subst K
  let _ : IsQuasisimple (generalizedFitting G) := hK.2
  have htop : generalizedFitting G = ⊤ :=
    generalizedFitting_eq_top_of_inner_centralQuotient eK Janko1.OuterCertificate.aut_inner
  have hcard : Nat.card (generalizedFitting G) = Nat.card G := by
    rw [htop, card_top]
  have hprod := (center (generalizedFitting G)).card_mul_index
  change Nat.card (center (generalizedFitting G)) *
    Nat.card (generalizedFitting G ⧸ center (generalizedFitting G)) =
      Nat.card (generalizedFitting G) at hprod
  rw [Nat.card_congr eK.toEquiv, Janko1.card_model, hcard] at hprod
  have hdiv : 16 ∣ Nat.card G := hT ▸ (T : Subgroup G).card_subgroup_dvd_card
  have hcop : Nat.Coprime 16 (Nat.card (center (generalizedFitting G))) :=
    hZ.coprime_two_left.pow_left 4
  have hbad : 16 ∣ 175560 := hcop.dvd_mul_left.mp (hprod.symm ▸ hdiv)
  norm_num at hbad

/-- Complete sporadic component sieve for the split Sylow sixteen branch. -/
theorem not_sporadic_component
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (hF : generalizedFitting G = K)
    (hK : IsComponent G K) (hZ : Odd (Nat.card (center K)))
    (hmodel : IsTheoremCSporadicModel (K ⧸ center K)) : False := by
  have hT : Nat.card T = 16 := (Nat.card_congr eT.toEquiv).trans split_sixteen_card
  rcases hmodel with ⟨name,hne,⟨e⟩⟩ | hJ
  · by_cases hm : name = .m11
    · subst name
      exact not_mathieu_eleven_section T eT K
        (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
        (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
    · let _ : Finite name.Carrier := Finite.of_surjective e e.surjective
      exact not_thirty_two_dvd_card_section_of_sylow_le_sixteen T hT.le K
        (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
        (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
        (thirty_two_dvd_sporadic_name name hne hm)
  · exact not_janko_one_component T hT K hF hK hZ hJ.some

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
