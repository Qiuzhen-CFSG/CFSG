module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Section
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeCommutant

/-!
# The original M24 cocode section and its joint centralizer

On the same selected pair I and original fixed three-space U, put
P=O2(I), B=V intersect P and R=localResidual L U. The native trio marking
of B/U transports through its original I-conjugate, giving four natural
three-dimensional coordinates on P/U. The original actions of R and I
commute and I has its exact two-core kernel. Their joint commutant has
no nontrivial operator whose fifth power is one.

The twelve-dimensional action and every marking are constructed here;
there is no tensor or scalar-recognition callback. The following Five
module uses this bound on the actual order-five actor from H/O2(H).
Unitary torus placement, T-normalization, other Mathieu rows and ambient
J4 recognition remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith, H.15.6(3), E.2.14, 8.2.8(4,5), pp.401,228,718--719,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original cocode pair section is four copies of the natural
three-space for the same residual quotient, with literal conjugation. -/
theorem sourceOrbit_m24_pair_four_natural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := localResidual L U
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          ∃ hel : IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)), letI := hel
            let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
            f.ker = pCore 2 Y ∧ (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
            (∀ r : R, ∀ j : I, Commute (f (inclusion le_sup_left r)) (f (inclusion le_sup_right j))) ∧
            ∃ (e : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
                (Fin 2 × Fin 2 → Vector)) (π : R →* BinaryLinear.GL Vector),
              Function.Surjective π ∧
              ∀ (r : R) (z : I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
                e (Additive.ofMul (f (inclusion le_sup_left r) z)) =
                  fun j => π r (e (Additive.ofMul z) j) := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  let R := localResidual L U
  let P := I.pCoreIn 2
  let B := W ⊓ P
  let Y := R ⊔ I
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (p := 2)
    (show B ≤ W from inf_le_left)
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,_,_,_,_,hc,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  have hcRI : ⁅R,I⁆ ≤ R.pCoreIn 2 := (commutator_mono le_rfl hIC).trans hc
  obtain ⟨hYP,hYU,hUP,hker,_,hR,hI,_,_⟩ :=
    D.sourceOrbit_m24_pair_joint_section h hmany hV hq hnon a E hE hg hAT s hUZ
  let := hUP
  have hdim : rank W = 11 :=
    (Chapter7.log_card_eq_finrank W).trans (E.finrank_eq.trans MathieuCode.finrank_cocode)
  obtain ⟨_,_,_,_,_,_,_,_,hu,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE hg
  have hid := selected_actor_rank_identity s
  rw [←hUZ,hu,hdim] at hid
  change 3 + 2 + rank (inducedAutomizer W
    (W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = 11 at hid
  have ha : rank (inducedAutomizer W
      (W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = 6 := by omega
  obtain ⟨_,hel,hcard,_⟩ := MathieuPair.selected_two_core_section s hUZ hIC hu ha
  let := hel
  obtain ⟨_,hRB,hRU,hUN,eB,π,hπ,_,heB⟩ :=
    D.sourceOrbit_m24_pair_section_natural h hmany hV hq hnon a E hE hg hAT s hUZ
  let := hUN
  let f := sectionAction Y P U hYP hYU
  have hcomm (r : R) (j : I) : Commute (f (inclusion le_sup_left r))
      (f (inclusion le_sup_right j)) :=
    MathieuPair.commuting_pair_images R I Y le_sup_left le_sup_right f hR hcRI r j
  have hIP : I ≤ normalizer (P : Set G) := le_sup_right.trans hYP
  have hPi : P.map (MulAut.conj i.val⁻¹).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (hIP (I.inv_mem i.property))
  have hP : B ⊔ B.map (MulAut.conj i.val⁻¹).toMonoidHom = P := by
    rw [map_inf _ _ _ (MulAut.conj i.val⁻¹).injective,hPi]
    exact (MathieuPair.selected_two_core_product s).symm
  have hBc : Nat.card (B ⧸ U.subgroupOf B) = 2^6 := by
    calc
      _ = Nat.card (Vector × Vector) := Nat.card_congr eB.toEquiv
      _ = 2^6 := by norm_num [M24LocalGeometry.PairOvergroups.QuotientConstruction.Vector,
        Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  obtain ⟨e,he⟩ := MathieuPair.section_four_coordinates Y R P B U le_sup_left inf_le_right
    hYP hYU hRB (inclusion le_sup_right i⁻¹) hP
    (by rw [hBc,hcard]; norm_num) (fun r => hcomm r i⁻¹) eB π heB
  exact ⟨hYP,hYU,hUP,hel,hker,hI,hcomm,e,π,hπ,he⟩

/-- The joint action on the actual cocode section has no commuting
operator of order five. There is no tensor or scalar-recognition premise. -/
theorem sourceOrbit_m24_pair_joint_no_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hYP : (localResidual L (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) ⊔ I) ≤ normalizer (I.pCoreIn 2 : Set G))
    (hYU : (localResidual L (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) ⊔ I) ≤ normalizer ((D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) : Set G))
    [hUP : ((D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)).subgroupOf (I.pCoreIn 2)).Normal] :
    let U := (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G))
    let Y := localResidual L U ⊔ I
    ∀ z : MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
      (∀ y : Y, Commute z (sectionAction Y (I.pCoreIn 2) U hYP hYU y)) →
      z ^ 5 = 1 → z = 1 := by
  let U := (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G))
  let R := localResidual L U
  let Y := R ⊔ I
  let P := I.pCoreIn 2
  obtain ⟨_,_,_,hel,rest⟩ :=
    D.sourceOrbit_m24_pair_four_natural h hmany hV hq hnon a E hE hg hAT s hUZ
  let : IsElementaryAbelian 2 (P ⧸ U.subgroupOf P) := hel
  let f : Y →* MulAut (P ⧸ U.subgroupOf P) := sectionAction Y P U hYP hYU
  obtain ⟨_,hI,hcomm,e,π,hπ,he⟩ := rest
  have hEven : 2 ∣ Nat.card (f.comp (inclusion (show I ≤ Y from le_sup_right))).range :=
    MathieuPair.selected_two_image_even s _ hI
  change ∀ z : MulAut (P ⧸ U.subgroupOf P),
    (∀ y : Y, Commute z (f y)) → z ^ 5 = 1 → z = 1
  intro z hz hz5
  exact MathieuMultiplicity.section_joint_no_five_of_four_copies
    (f.comp (inclusion (show R ≤ Y from le_sup_left)))
    (f.comp (inclusion (show I ≤ Y from le_sup_right))) π hπ e he hEven hcomm z
    (fun r => hz (inclusion le_sup_left r)) (fun j => hz (inclusion le_sup_right j)) hz5

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
