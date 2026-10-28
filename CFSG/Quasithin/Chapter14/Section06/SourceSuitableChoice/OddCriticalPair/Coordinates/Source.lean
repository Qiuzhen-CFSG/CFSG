module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.Seed
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.Generation
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.Terminal

/-!
# Completing the orthogonal residual coordinates and terminal application

The actual seed is v=b₁*b₂*c, with nonzero projections on both exchanged
planes and c in the full fixed preimage. Set W equal to the second covering
plane and a=b₁*c. The literal residual O²(C_H(u mod Z)) fixes a, while its
commutators with b₂ generate W modulo Z. This constructs every field of the
residual-coordinate record, retaining the same previously selected u.

The source consumer then chooses a suitable vector in the marked first plane
and applies the proved parabolic, crossing and rank bounds. The existence of
the original 14.6.13 critical pair remains with qt-e-suitable-orthogonal-marking;
the explicit fitting and normalizer inputs are the genuine 14.6.14--16 outputs,
whose ultimate discharge remains with qt-e-suitable-existence. No critical-pair
existence or complete source classification is asserted here.

Source: Aschbacher--Smith 14.6.17, printed pp.1035--1036.
-/

@[expose] public section



public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 OddNormalizer OrthogonalSource
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

/-- Construct every residual-coordinate field from the actual two supports
and the original seed. The selected u remains unchanged throughout. -/
theorem orthogonal_residual_coordinates (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (hplus : D.Vplus = D.V) (hcard : Nat.card D.V = 4)
    (a : LocalQuotientAction D.H D.UH D.V₁) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (D.T : Subgroup G) 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu : (u : G) ∈ o.plane i) (huz : (u : G) ∉ D.V₁)
    (hcover : D.UH = o.plane i ⊔ o.plane j ⊔ fixedSupport a) :
    Nonempty (SourceResidualSpanCoordinates D.V D.V₁
      ((pResidual 2 (h.kernel (zpowers (u : G)))).map (h.kernel (zpowers (u : G))).subtype)) := by
  let P := h.kernel (zpowers (u : G))
  let R := (pResidual 2 P).map P.subtype
  have hKU : ⁅D.UH,D.H⁆ ≤ D.UH := le_normalizer_iff_commutator_le_left.mp o.normalized
  have hVU : D.V ≤ D.UH := by
    rw [←hplus]
    exact le_conjugateSpanBy _ _
  have hgen : conjugateSpanBy D.V D.H = D.UH := by
    change conjugateSpanBy D.V D.H = conjugateSpanBy D.Vplus D.H
    rw [hplus]
  obtain ⟨v,hv,hvz,b₁,hb₁,hb₁z,b₂,hb₂,hb₂z,c,hc,he⟩ :=
    orthogonal_seed_decomposition a (D.T : Subgroup G) D.V H0 H1 H2 h.T_le_H d o
      h.point_card i j hji hi hVU (h.point_lt.le.trans h.plus_le) hcard
      h.T_normalizes_V hgen hcover
  have haU : b₁*c ∈ D.UH := D.UH.mul_mem (hKU (o.plane_le i hb₁))
    (supportPreimage_le a _ hc)
  have haW : b₁*c ∉ o.plane j := by
    intro ha
    have hfirst : b₁ ∈ o.plane j ⊔ fixedSupport a := by
      have hh := (o.plane j ⊔ fixedSupport a).mul_mem
        ((le_sup_left : o.plane j ≤ o.plane j ⊔ fixedSupport a) ha)
        ((le_sup_right : fixedSupport a ≤ o.plane j ⊔ fixedSupport a) ((fixedSupport a).inv_mem hc))
      simpa only [mul_inv_cancel_right] using hh
    exact hb₁z (first_plane_separated_fixed a o i j hji ⟨hb₁,hfirst⟩)
  have hA : R ≤ centralizer (o.plane i : Set G) :=
    original_residual_centralizes_first_support h a H0 H1 H2 d o i hi u hu huz
  have hC : R ≤ centralizer (fixedSupport a : Set G) :=
    residual_centralizes_fixedSupport h a u (hKU u.property)
  have haR : b₁*c ∈ centralizer (R : Set G) := (centralizer (R : Set G)).mul_mem
    (le_centralizer_iff.mp hA hb₁) (le_centralizer_iff.mp hC hc)
  have hcomm : D.UH ≤ centralizer (D.UH : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hbc : b₂*c=c*b₂ := hcomm (supportPreimage_le a _ hc) b₂ (hKU (o.plane_le j hb₂))
  have hseed : D.V = D.V₁ ⊔ zpowers ((b₁*c)*b₂) := by
    rw [ComponentCriticalPair.plane_eq_line_sup_zpowers hcard h.point_card
      (h.point_lt.le.trans h.plus_le) v hv hvz,he,mul_assoc b₁ b₂ c,hbc,←mul_assoc]
  exact ⟨{
    W := o.plane j
    elementary := IsElementaryAbelian.of_le ((o.plane_le j).trans hKU)
    card := o.card_plane h.point_card j
    a := b₁*c
    b := b₂
    order := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ haU)
      (fun he => haW (he ▸ (o.plane j).one_mem))
    independent := haW
    seed := hseed
    line := o.point_le_plane j
    second := hb₂
    normalizes := (map_subtype_le _).trans (suitable_kernel_normalizes_planes h o i j u hu huz)
    fixed := haR
    commutes := (hcomm.trans (centralizer_le ((o.plane_le j).trans hKU))) haU
    generated := suitable_second_plane_generated h o i j hji u hu huz b₂ hb₂ hb₂z }⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair


public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- All residual seed coordinates for the original orthogonal four-space.
The fixed supplement, both nonzero projections, residual action and generation
are conclusions for the same full quotient centralizer of u. -/
theorem source_orthogonal_residual_coordinates
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1)
    (u : G) (hu : u ∈ o.plane i) (huz : u ∉ centralInvolutions T) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    Nonempty (SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hc := (source_orthogonal_fixed_factor_data hG T hempty hM hunique hmany hcard e hab
    H hH a H0 H1 H2 d o i j hji hi u hu huz).1
  exact orthogonal_residual_coordinates (D := D) h rfl hcard a H0 H1 H2 d o i j hji hi
    ⟨u,o.plane_le i hu⟩ hu huz hc

/-- Original 14.6.17(5) on the literal full quotient-centralizer residual. -/
theorem source_orthogonal_residual_span_rank_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1)
    (u : G) (hu : u ∈ o.plane i) (huz : u ∉ centralInvolutions T) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    primeRank 2 (conjugateSpanBy (localModule T M)
      ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype)) = 4 := by
  obtain ⟨coordinates⟩ := source_orthogonal_residual_coordinates hG T hempty hM hunique
    hmany hcard e hab H hH a H0 H1 H2 d o i j hji hi u hu huz
  exact coordinates.rank_four

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 OddNormalizer OddCriticalPair
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (critical : SourceOrthogonalCriticalPair d Mc)
    (u : G) (hu : u ∈ d.plane critical.first) (huz : u ∉ centralInvolutions T)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))

include hG hempty hM hunique hmany hcard e hab hH hu huz hindex hmove hproduct hU3

/-- The literal terminal application, with the parabolic, crossing, rank and
residual coordinates all proved from the marked orthogonal critical pair.
The original 14.6.13 critical pair and earlier normalizer conclusions remain
with their source assembly owners. -/
theorem source_terminal_witness_of_orthogonal_marking
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (H0 H1 H2 : Subgroup G)
    (factors : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hi : d.plane critical.first = firstSupport a H1) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  let j : OrthogonalPlaneIndex := critical.first * Multiplicative.ofAdd (1 : ZMod 2)
  have hji : j ≠ critical.first := by
    have hh : ∀ i : OrthogonalPlaneIndex, i*Multiplicative.ofAdd (1 : ZMod 2) ≠ i := by decide
    exact hh critical.first
  obtain ⟨coordinates⟩ := source_orthogonal_residual_coordinates hG T hempty hM hunique hmany
    hcard e hab H hH a H0 H1 H2 factors d critical.first j hji hi u hu huz
  exact source_terminal_witness_of_orthogonal_coordinates hG T hempty hM hunique hmany
    hcard e hab H hH d critical u hu huz hindex hmove hproduct hU3 coordinates

end CFSG.Quasithin.Chapter14.Section06

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 OddNormalizer OddCriticalPair
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (critical : SourceOrthogonalCriticalPair d Mc)

include hG hempty hM hunique hmany hcard e hab hH

/-- Choose the suitable vector and complete the orthogonal terminal branch
from the marked critical pair. Only the genuine 14.6.14--16 fitting and
normalizer conclusions remain explicit earlier-source inputs. -/
theorem source_terminal_witness_of_marked_orthogonal_pair
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (H0 H1 H2 : Subgroup G)
    (factors : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hi : d.plane critical.first = firstSupport a H1)
    (hF : residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) = (T : Subgroup G)) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  obtain ⟨hWU,hZW,hKW,_hSW,hindex,hsep,_hff⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 factors
  obtain ⟨u,hu,_hu2,_hun,hfixed,hmoved⟩ := source_exists_fixed_moving_in_support
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 factors
  have huz : u ∉ centralInvolutions T := by
    intro hz
    obtain ⟨k,hk,hkz⟩ := hmoved
    apply hkz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (h.H_centralizes ((map_subtype_le _) hk) u hz)]
    exact one_mem _
  obtain ⟨heq,hmove,hproduct,_hlocal⟩ := source_suitable_of_separated_support
    hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
    ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hF hWU hZW.le hKW inf_le_left
    hindex hN hsep u hu hfixed hmoved
  exact source_terminal_witness_of_orthogonal_marking hG T hempty hM hunique hmany hcard
    e hab H hH d critical u (hi.symm ▸ hu) huz (by rwa [heq]) hmove hproduct
    (by rwa [heq]) a H0 H1 H2 factors hi

end CFSG.Quasithin.Chapter14.Section06
