module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Local

/-!
# M24 point control and fixed-space geometry with the cover input discharged

The two-primary rigidity theorem for the actual J4 model applies to the entire
center of the escaping perfect component. It discharges the retained cover
premise in every point-control, equality, marked-offender, normalizer and local
consumer. The original conditional APIs are preserved. These source results
retain the same full automizer, code/cocode marking and original Sylow subgroup.

Canonical pair construction, component recognition and the final ambient J4
isomorphism remain with qt-d-1222-nonff-mathieu. Source: Aschbacher--Smith
8.1.1--3 and 8.2.5--6, printed pp.712--717, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.TrioCalculation
open CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original source conclusion with the J4 covering premise proved. -/
theorem sourceOrbit_m24_pair_control_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
  exact D.sourceOrbit_m24_pair_control_of_janko_two_cover
    (fun _ _ _ _ e hp => Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)
    h hmany hV hq hnon a E hE x hx

/-- The original source conclusion with the J4 covering premise proved. -/
theorem sourceOrbit_m24_cocode_geometry_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    globalR D.sourceOrbit = 8 ∧ globalW D.sourceOrbit (T : Subgroup G) = 2 ∧
      rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 6 ∧
      rank (offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G)) = 3 ∧
      (∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        generationParameter H = 2) ∧
      ∃ c : M24,
        ((inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)).map
          a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
            trioKernel PairOvergroups.standardTrio ∧
        ((fixedSpace (automizerRepresentation D.sourceOrbit)
          (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g))).map
            E.toLinearMap).map (cocodeRepresentation c) = TrioCalculation.standardPlaneMap.range ∧
        rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) = 3 ∧
        D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
          D.sourceOrbit ⊓ centralizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) := by
  exact D.sourceOrbit_m24_cocode_geometry_of_janko_two_cover
    (fun _ _ _ _ e hp => Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)
    h hmany hV hq hnon a E hE hg

/-- The original source conclusion with the J4 covering premise proved. -/
theorem sourceOrbit_m24_cocode_marked_offender_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    ∃ (g : G) (c : M24), IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      ((inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)).map
        a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
          trioKernel PairOvergroups.standardTrio ∧
      ((fixedSpace (automizerRepresentation D.sourceOrbit)
        (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g))).map
          E.toLinearMap).map (cocodeRepresentation c) = TrioCalculation.standardPlaneMap.range ∧
      rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) = 3 := by
  exact D.sourceOrbit_m24_cocode_marked_offender_of_janko_two_cover
    (fun _ _ _ _ e hp => Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)
    h hmany hV hq hnon a E hE

/-- The original source conclusion with the J4 covering premise proved. -/
theorem sourceOrbit_m24_fixedPlane_normalizer_action_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ (c : M24) (e : U ≃* Multiplicative Vector)
      (π : (L ⊓ normalizer (U : Set G) : Subgroup G) →* BinaryLinear.GL Vector),
      Function.Surjective π ∧
      Function.Surjective (π.comp (solvableResidual
        (L ⊓ normalizer (U : Set G) : Subgroup G)).subtype) ∧
      π.ker = (centralizer (U : Set G)).subgroupOf (L ⊓ normalizer (U : Set G)) ∧
      (∀ u : U, standardPlaneMap (e u).toAdd =
        cocodeRepresentation c (E (Additive.ofMul (inclusion inf_le_left u)))) ∧
      (∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (u : U),
        (e (U.normalizerMonoidHom ⟨l,l.property.2⟩ u)).toAdd = π l (e u).toAdd) ∧
      ∀ B : Subgroup G, B ≤ U → B ≠ ⊥ →
        conjugateSpanBy B ((solvableResidual
          (L ⊓ normalizer (U : Set G) : Subgroup G)).map
            (L ⊓ normalizer (U : Set G) : Subgroup G).subtype) = U := by
  exact D.sourceOrbit_m24_fixedPlane_normalizer_action
    (fun _ _ _ _ e hp => Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)
    h hmany hV hq hnon a E hE hg

/-- The original source conclusion with the J4 covering premise proved. -/
theorem sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    rank U = 3 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsTwoLocal (normalizer (U : Set G)) ∧
      HasCharacteristicTwo (normalizer (U : Set G)) ∧
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) ∧
      ∃ H : Subgroup G,
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
        H ≤ normalizer (U : Set G) ∧
        (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
        generationParameter H = 2 := by
  exact D.sourceOrbit_m24_fixedPlane_local_of_offender
    (fun _ _ _ _ e hp => Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)
    h hmany hV hq hnon a E hE hg hAT

/-- The original source conclusion with the J4 covering premise proved. -/
theorem sourceOrbit_m24_exists_fixedPlane_local_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v)) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      offenderNormalizer D.sourceOrbit g ≤ T ∧
      let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
      let N := normalizer (U : Set G)
      rank U = 3 ∧ (T : Subgroup G) ≤ N ∧ IsTwoLocal N ∧ HasCharacteristicTwo N ∧
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) ∧
      (∃ H : Subgroup G,
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧ H ≤ N ∧
        (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧ generationParameter H = 2) ∧
      ∃ (c : M24) (e : U ≃* Multiplicative Vector) (qN : N →* BinaryLinear.GL Vector),
        Function.Surjective qN ∧
        qN.ker = (centralizer (U : Set G)).subgroupOf N ∧
        (∀ u : U, MathieuCode.TrioCalculation.standardPlaneMap (e u).toAdd =
          MathieuCode.cocodeRepresentation c (E (Additive.ofMul (inclusion inf_le_left u)))) ∧
        (∀ (n : N) (u : U),
          (e (U.normalizerMonoidHom n u)).toAdd = qN n (e u).toAdd) ∧
        N = centralizer (U : Set G) ⊔ (L ⊓ N) ∧
        U ≤ N.pCoreIn 2 ∧ N.pCoreIn 2 ≤ centralizer (U : Set G) ∧
        ∀ B : Subgroup G, B ≤ U → B ≠ ⊥ →
          conjugateSpanBy B ((solvableResidual (L ⊓ N : Subgroup G)).map
            (L ⊓ N : Subgroup G).subtype) = U := by
  exact D.sourceOrbit_m24_exists_fixedPlane_local
    (fun _ _ _ _ e hp => Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)
    h hmany hV hq hnon a E hE

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
