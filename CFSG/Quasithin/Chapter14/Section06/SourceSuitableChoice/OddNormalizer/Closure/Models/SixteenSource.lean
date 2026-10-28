module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.LinearThreeSource
public import Theory.SpecificGroups.PSL2.SixteenCubicWreath

/-!
# The remaining exchanged closure is detected on its actual cubic torus

Apply the Frattini lift to the faithful action of Mc/O₂(Mc) on the marked
PSL₂(16) square. An order-eight cubic image gives the entire automorphism
wreath quotient of original 14.6.14(4). Otherwise its order divides eight
and is at most four. Both inner coordinates, the original inverse exchanger,
the relative component, residual identities and generalized-Fitting layer
remain in the surviving source branch.

The outstanding source step is to construct the cubic Borel outside subgroup
and use earlier 14.6.12 to exclude this small image. This module does not
assert the unrestricted 14.6.14 theorem. The normalizer and suitable-choice
consumer is in OddNormalizer.SixteenChoice; final source choice remains with
qt-e-suitable-existence. Earlier exchanged factors retain qt-e-14612-singleton.

Source: Aschbacher--Smith 14.6.14, last paragraph, printed p.1033.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open WreathTwoElementaryRank AutomorphismSquare
variable {G : Type*} [Group G]
local notation "F16" => GaloisField 2 4
local notation "L16" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) F16
local notation "W16" => W (MulAut L16)

/-- A precise remaining obstruction: the faithful action on the original
component square induces at most four automorphisms of its cubic torus pair.
Both component markings and conjugation by the original inverse exchanger
are retained. This is not asserted for any source group without proof. -/
def SmallSixteenCubicImage (Mc K L : Subgroup G) (s : Mc) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let A := (L.subgroupOf Mc).map q
  let B := (K.subgroupOf Mc).map q
  ∃ e : A ≃* L16, ∃ k : B ≃* L16 × L16,
    (∀ x : A, (k.symm (e x,1) : Mc ⧸ pCore 2 Mc) = x) ∧
    (∀ x : A, (k.symm (1,e x) : Mc ⧸ pCore 2 Mc) = q s⁻¹ * x * (q s⁻¹)⁻¹) ∧
    ∃ ρ : (Mc ⧸ pCore 2 Mc) →* W16,
      Function.Injective ρ ∧
      (∀ x : B, ρ x = baseHom (MulAut.conj (k x).1,MulAut.conj (k x).2)) ∧
      (∀ g (x : B), (k.symm (wreathHom (ρ g) (k x)) : Mc ⧸ pCore 2 Mc) =
        g * x * g⁻¹) ∧
      Nat.card ((Theory.PSL2.SixteenCubicWreath.cubicWreathAction F16).comp ρ).range ≤ 4

/-- The marked source action fills the actual wreath quotient as soon as
its cubic torus image has order eight. Otherwise that image has order at most four. -/
theorem marked_sixteen_full_or_small_cubic_image
    {Mc K L : Subgroup G} {s : Mc} (ha : MarkedExchangedWreath Mc K L s L16) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* W16) ∨ SmallSixteenCubicImage Mc K L s := by
  obtain ⟨e,k,hl,hr,ρ,hi,hinner,hact⟩ := ha
  let f := (Theory.PSL2.SixteenCubicWreath.cubicWreathAction F16).comp ρ
  have hF : Nat.card F16 = 16 := GaloisField.card 2 4 (by decide)
  by_cases h8 : Nat.card f.range = 8
  · have hs := Theory.PSL2.SixteenCubicWreath.full_of_cubic_image_card F16 hF ρ (fun x y => by
      refine ⟨(k.symm (x,y) : Mc ⧸ pCore 2 Mc),?_⟩
      rw [hinner,k.apply_symm_apply]) h8
    exact Or.inl ⟨MulEquiv.ofBijective ρ ⟨hi,hs⟩⟩
  · refine Or.inr ⟨e,k,hl,hr,ρ,hi,hinner,hact,?_⟩
    have hd : Nat.card f.range ∣ 2^3 := by
      rw [show (2 : ℕ)^3 = 8 by decide]
      simpa only [Theory.PSL2.SixteenCubicWreath.cubic_target_card F16 hF] using
        f.range.card_subgroup_dvd_card
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    change Nat.card f.range ≤ 4
    have hn2 : n ≤ 2 := by
      by_contra h
      have hn3 : n = 3 := by omega
      exact h8 (by rw [he,hn3]; decide)
    calc
      Nat.card f.range = 2^n := he
      _ ≤ 2^2 := Nat.pow_le_pow_right (by decide) hn2
      _ = 4 := by decide

variable [Finite G]
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- The remaining original 14.6.14 branch has a deficient cubic Borel action.
The full quotient is now proved whenever the literal cubic image has order eight. -/
theorem source_closure_alternatives_or_small_sixteen_cubic_image
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p ∨
      (p = 5 ∧ ∃ (L : Subgroup G) (s : Mc), L ≤ Mc ∧
        (L.subgroupOf Mc).IsCComponent ∧ IsQuasisimple (XiQuotient L) ∧
        (s : G) ∈ (T : Subgroup G) ∧ (s : G) ∉ normalizer (L : Set G) ∧
        (residualClosure H Mc : Set G) = (L : Set G) *
          (L.map (MulAut.conj (s : G)⁻¹).toMonoidHom : Set G) ∧
        Mc = residualClosure H Mc ⊔ (T : Subgroup G) ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc) ∧
        SmallSixteenCubicImage Mc (residualClosure H Mc) L s) := by
  rcases source_closure_alternatives_or_sixteen
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with
    hc | ⟨hp,L,hL,hcomp,hq,_hm,_hb,hgen,ha,hr,hr3,hlayer⟩
  · exact Or.inl hc
  · obtain ⟨s,hs,hsn,hprod,ha⟩ := ha
    rcases ha with ⟨h3,_⟩ | ⟨_,ha⟩ | ⟨h3,_⟩
    · omega
    · rcases marked_sixteen_full_or_small_cubic_image ha with hw | hsmall
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hp,⟨L,hL,hcomp,s,hs,hsn,hprod⟩,hw⟩)))
      · exact Or.inr ⟨hp,L,s,hL,hcomp,hq,hs,hsn,hprod,hgen,hr,hr3,hlayer,hsmall⟩
    · omega

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
