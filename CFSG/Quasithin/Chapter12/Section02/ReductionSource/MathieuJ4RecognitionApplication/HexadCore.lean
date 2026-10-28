module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.Thompson
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.PlaneOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadElementary

/-!
# The original Mathieu hexad two-core construction

The unchanged marked Mathieu data identify the actual point-plane overlap
with the full preimage of a native hexad stabilizer under the original cubic
quotient. Its rank-five cubic-central factor and whole two-core are then
constructed by the general type-J4 calculation. The literal E₁ is the full
preimage of the two-core fixed space, and the whole overlap normalizes it.

The general product construction yields an elementary normal subgroup E of
order 2048 once E₁ is elementary of order 128. These last two native module
facts remain explicit here; this application does not claim the general
Thompson equality or the full normalizer/module recognition.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (4.6), p.598,
DOI 10.1007/BF01232280; Aschbacher–Smith 8.2.12–14.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- Construct the literal AS91 (4.6) subgroups at the actual original
point-plane overlap. The two native fixed-space facts remain explicit only
in the last implication constructing the elementary order-2048 product. -/
theorem sourceOrbit_m24_hexad_construction :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ (B : Finset (Fin 22)), B ∈ m22Blocks ∧
        let I := (normalizer (D.sourceOrbit : Set G)).subgroupOf
          (centralizer ({(z : G)} : Set G))
        let P := originalHexadCore ht cubic X B
        let E1 := originalHexadFixedCore ht cubic X B
        I = originalPlaneHexad cubic B ∧
        P = I.pCoreIn 2 ⊓ fullCubicCentralizer cubic X ∧
        IsElementaryAbelian 2 P ∧ Nat.card P = 32 ∧
        center (centralizer ({(z : G)} : Set G)) ≤ P ∧
        I.pCoreIn 2 = Recognition.JankoFour.core (z : G) ⊔ P ∧
        Nat.card (I.pCoreIn 2) = 131072 ∧
        E1 = commutatorPreimage (Recognition.JankoFour.core (z : G))
          (I.pCoreIn 2) (center (centralizer ({(z : G)} : Set G))) ∧
        E1 = Recognition.JankoFour.core (z : G) ⊓
          centralizer (P : Set (centralizer ({(z : G)} : Set G))) ∧
        I ≤ normalizer (E1 : Set (centralizer ({(z : G)} : Set G))) ∧
        (IsElementaryAbelian 2 E1 → Nat.card E1 = 128 →
          IsElementaryAbelian 2 (originalHexadElementary ht cubic X B) ∧
          Nat.card (originalHexadElementary ht cubic X B) = 2048 ∧
          I ≤ normalizer (originalHexadElementary ht cubic X B :
            Set (centralizer ({(z : G)} : Set G)))) := by
  intro ht cubic X
  let W := D.sourceOrbit
  let f := a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hc := sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hc]
  have hF : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)) := by
    intro n v
    exact hE (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul v)
  have hWc : Nat.card W = 2048 := by
    change Nat.card (Additive W) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  have hplane := marked_cocode_plane_card W f hf hk hWc E hF z S hS
  obtain ⟨B,hB,_,hpre⟩ := marked_pointPlane_hexad ht cubic (normalizer (W : Set G)) hplane
  refine ⟨B,hB,?_⟩
  change (normalizer (D.sourceOrbit : Set G)).subgroupOf
    (centralizer ({(z : G)} : Set G)) = originalPlaneHexad cubic B at hpre
  dsimp only
  rw [hpre]
  obtain ⟨hP,hPc,hZP⟩ := originalHexadCore_data ht cubic X hB
  refine ⟨rfl,originalHexadCore_eq_source ht cubic X B,hP,hPc,hZP,
    originalPlaneHexad_twoCore ht cubic X B,originalPlaneHexad_twoCore_card ht cubic X hB,
    originalHexadFixedCore_source ht cubic X B,originalHexadFixedCore_eq ht cubic X B,
    originalHexadFixedCore_normalized ht cubic X B,?_⟩
  intro hE1 hE1c
  let := hE1
  exact ⟨originalHexadElementary_elementary ht cubic X hB,
    originalHexadElementary_card ht cubic X hB hE1c,
    originalHexadElementary_normalized ht cubic X hE1c⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
