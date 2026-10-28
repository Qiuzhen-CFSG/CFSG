module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.FullCubicPerfect
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadComplement
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps

/-!
# The original Mathieu hexad complement to the marker line

For every choice of the original cubic quotient and its Sylow three-subgroup,
the marked Mathieu inputs identify the actual point–plane overlap as the
full inverse image of a native hexad stabilizer. The specified A₆ section
of that hexad lifts to a subgroup of order 1080 in the original C_H(X),
inside the same overlap. It contains X and is disjoint from the original
marker line; adjoining that line recovers the full A₆ preimage. The already
proved perfectness of the full cubic centralizer makes this order-1080
subgroup perfect, and identifies it exactly with that preimage’s derived
subgroup. Every map retains the same original cubic marking.

All hypotheses are the original marked Mathieu arguments and hquot.
Neither Todd splitting nor LocalData-dependent fusion is used. The invariant
core complement, full Todd splitting, general/native LocalData and final
recognition remain separate obligations of the recognition family.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), (4.8), p.599,
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

/-- The actual point–plane overlap contains a complement to the marker
inside the original preimage of the native hexad A₆ section. -/
theorem sourceOrbit_m24_full_cubic_hexad_complement :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ (B : Finset (Fin 22)) (hB : B ∈ m22Blocks),
        (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) =
          (Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer B).comap
            (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) ∧
        ∃ A : Subgroup (fullCubicCentralizer cubic X),
          Nat.card A = 1080 ∧ fullCubicScalar cubic X ≤ A ∧
          Disjoint (fullCubicProjection ht cubic X).ker A ∧
          A.map (fullCubicSimpleProjection ht cubic X) =
            ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range ∧
          (fullCubicProjection ht cubic X).ker ⊔ A =
            (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
              (fullCubicSimpleProjection ht cubic X) ∧
          A.map (fullCubicCentralizer cubic X).subtype ≤
            (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) := by
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
  exact ⟨B,hB,hpre,fullCubic_hexad_overlap_complement ht cubic X hB _ hpre⟩


/-- The same original inputs make the local complement perfect and identify
it canonically as the derived subgroup of the full native A₆ preimage. -/
theorem sourceOrbit_m24_full_cubic_hexad_perfect :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ (B : Finset (Fin 22)) (hB : B ∈ m22Blocks),
        (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) =
          (Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer B).comap
            (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) ∧
        ∃ A : Subgroup (fullCubicCentralizer cubic X),
          Nat.card A = 1080 ∧ fullCubicScalar cubic X ≤ A ∧
          Disjoint (fullCubicProjection ht cubic X).ker A ∧
          A.map (fullCubicSimpleProjection ht cubic X) =
            ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range ∧
          (fullCubicProjection ht cubic X).ker ⊔ A =
            (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
              (fullCubicSimpleProjection ht cubic X) ∧
          A.map (fullCubicCentralizer cubic X).subtype ≤
            (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
          Group.IsPerfect A ∧
          (_root_.commutator
            ((((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
              (fullCubicSimpleProjection ht cubic X))).map
            ((((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
              (fullCubicSimpleProjection ht cubic X)).subtype = A := by
  intro ht cubic X
  obtain ⟨B,hB,hpre,A,hAc,hscalar,hdis,him,hgen,hle⟩ :=
    D.sourceOrbit_m24_full_cubic_hexad_complement h hmany hV hq hnon a E hE z hz hne hquot cubic X
  let := (D.sourceOrbit_m24_full_cubic_perfect h hmany hV hq hnon a E hE z hz hne hquot cubic X).2.1
  exact ⟨B,hB,hpre,A,hAc,hscalar,hdis,him,hgen,hle,
    fullCubic_hexad_subgroup_perfect ht cubic X hB A hAc hscalar him,
    fullCubic_hexad_subgroup_derived ht cubic X hB A hAc hscalar him hgen⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
