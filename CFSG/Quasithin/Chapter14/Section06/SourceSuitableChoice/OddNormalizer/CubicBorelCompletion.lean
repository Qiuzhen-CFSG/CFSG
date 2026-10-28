module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.CubicBorelDetector

/-!
# Original odd-prime closure and suitable involution from earlier 14.6.12

The cubic Borel construction provides a primitive minimal outside subgroup
for the unchanged T and M. Earlier 14.6.12 gives its residual order nine and
its two-core quotient order 72. The former identifies it with the Borel
join; the latter forces order eight in the actual cubic detector. The
Frattini lift then excludes the sole small-image obstruction to 14.6.14.
The already proved 14.6.15 and cubic normalizer/support theorems provide
p = 3, original 14.6.16 and the actual suitable involution in UH,1.

Only the earlier exchanged-factor orders are explicit here. They belong to
qt-e-14612-singleton, and final suitable-choice assembly belongs to
qt-e-suitable-existence. In particular, no later 14.6.15 implication supplies
an earlier factor-join index, and no suitability or normalizer premise is added.

Source: Aschbacher--Smith 14.6.12--17, printed pp.1031--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The two numerical consequences of earlier 14.6.12 used on a fresh
primitive cubic outside subgroup. This is an explicit earlier-source input,
not a claimed construction from the definition of primitivity. -/
@[expose] def EarlierCubicFactorOrders (T M : Subgroup G) : Prop :=
  ∀ J : Subgroup G, J ∈ Chapter3.HStar T M → PrimitiveResidual J 3 →
    pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ →
    Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧ Nat.card (J ⧸ pCore 2 J) = 72

omit [Finite G] in
/-- Literal exchanged factors supply exactly the earlier orders consumed
by the auxiliary subgroup argument. -/
theorem cubic_orders_of_exchanged_factors
    (T : Subgroup G) (J U Z J0 J1 J2 : Subgroup G) [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction J U Z) (d : ExchangedFactorSetup a T 3 J0 J1 J2) :
    Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧ Nat.card (J ⧸ pCore 2 J) = 72 := by
  exact ⟨by simpa using d.residual_card,
    by simpa using OddCriticalPair.exchanged_actor_card a T 3 J0 J1 J2 d⟩

omit [Finite G] in
/-- A producer of literal 14.6.12 factors on the fresh cubic subgroups
supplies the numerical earlier-source interface used below. -/
theorem earlier_cubic_orders_of_exchanged_family
    (T M : Subgroup G)
    (h12 : ∀ J : Subgroup G, J ∈ Chapter3.HStar T M → PrimitiveResidual J 3 →
      pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ →
      ∃ (U Z : Subgroup G) (_ : IsElementaryAbelian 2 U)
        (a : LocalQuotientAction J U Z) (J0 J1 J2 : Subgroup G),
        ExchangedFactorSetup a T 3 J0 J1 J2) : EarlierCubicFactorOrders T M := by
  intro J hJ hp hne
  obtain ⟨U,Z,hU,a,J0,J1,J2,d⟩ := h12 J hJ hp hne
  let := hU
  exact cubic_orders_of_exchanged_factors T J U Z J0 J1 J2 a d

/-- The constructed Borel rules out the small marked cubic image as soon
as earlier 14.6.12 is available for its selected primitive outside subgroup. -/
theorem no_small_sixteen_image_of_cubic_borel
    (T : Sylow 2 G) (M Mc H Kz L : Subgroup G) (s : Mc)
    (hTMc : (T : Subgroup G) ≤ Mc)
    (hlayer : StrictClosureLayer Mc Kz)
    (hsmall : SmallSixteenCubicImage Mc Kz L s)
    (hBorel : CubicBorelOutside (T : Subgroup G) M Mc H Kz)
    (h12 : EarlierCubicFactorOrders (T : Subgroup G) M) : False := by
  obtain ⟨B,X,P,J,hBdef,hBMc,_hHB,_hmodel,hX,_hXB,_hXK,hn,hp,_he,hc,_hout,
    _hindex,_hPX,_hSyl,_hPc,_hPe,_hPT,hJX,hJ,_hs,hprim,hne⟩ := hBorel
  obtain ⟨h9,h72⟩ := h12 J hJ hprim hne
  have hJdef := cubic_borel_eq_of_residual_card T X J hn hc hJ.1.1.2 hJX h9
  have hprim' : PrimitiveResidual (X ⊔ (T : Subgroup G)) 3 := hJdef ▸ hprim
  have h72' : Nat.card ((X ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) = 72 := hJdef ▸ h72
  let N := (Kz.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  let : N.Normal := by
    change ((Kz.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))).Normal
    rw [hlayer.image_eq_generalizedFitting]
    infer_instance
  obtain ⟨_e,k,_hl,_hr,ρ,_hi,_hinner,hact,hsmall⟩ := hsmall
  have h8 := cubic_borel_detector_card T Mc hTMc N k ρ hact B X hBdef hBMc hX hn hp hc hprim' h72'
  omega

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.14 from the explicit earlier 14.6.12 input. All strict
model quotients and generalized-Fitting/normal-closure branches are proved. -/
theorem source_closure_alternatives_of_earlier_cubic_orders
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (h12 : EarlierCubicFactorOrders (T : Subgroup G) M) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p := by
  rcases source_closure_alternatives_or_small_sixteen_cubic_image
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with
    hc | ⟨hp,L,s,_hL,_hcomp,_hq,_hs,_hsn,_hprod,_hgen,_hr,hr3,hlayer,hsmall⟩
  · exact hc
  · have hB := source_small_sixteen_cubic_borel hG T hempty hM hunique hmany hcard e hab
      H hH (hp ▸ hprim) (residualClosure H Mc) L s hr3 hlayer hsmall
    have hHMc : H ≤ Mc :=
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
        (InitialSource.centralizer_le_partner T hunique)
    exact (no_small_sixteen_image_of_cubic_borel T M Mc H (residualClosure H Mc) L s
      (hH.1.2.trans hHMc) hlayer hsmall hB h12).elim

/-- Original 14.6.15--16, with the source closure premise now discharged. -/
theorem source_prime_normalizer_of_earlier_cubic_orders
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (h12 : EarlierCubicFactorOrders (T : Subgroup G) M) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    p = 3 ∧ S.relIndex (T : Subgroup G) = 2 ∧
      Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  exact source_prime_and_normalizer_of_closure_alternatives
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax
      (source_closure_alternatives_of_earlier_cubic_orders
        hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax h12)

/-- The suitable involution lies in the original first support and satisfies
all original local and ambient Sylow and inverse-conjugation clauses. -/
theorem source_exists_suitable_of_earlier_cubic_orders
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (h12 : EarlierCubicFactorOrders (T : Subgroup G) M) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    ∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G) := by
  exact source_exists_suitable_of_closure_alternatives
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax
      (source_closure_alternatives_of_earlier_cubic_orders
        hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax h12)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
