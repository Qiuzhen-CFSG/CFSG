module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceEndpointRanks
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectionCenter
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceActorRankGap

/-!
# Strict actor ranks on the literal chosen Hermitian tensor

The selected pair has actor rank greater than k, and the actual Hermitian
automizer bounds k strictly below 4n. At k = 2n, the torus supplied by the
remaining E.2.14(9) clause forces actor rank 3n and intersection rank 4n.
All actions, quotient maps and conjugators are the original chosen ones;
local setup and TI are derived from the original hypotheses. The argument
includes half-degree one and does not assume the E.2.14 rank clause.

The endpoint still requires its linear-module or scalar-torus exclusion.
Witness selection, symplectic exclusion, the source torus identity and the
field-four normalizer/centralizer endgame through 8.2.13 remain unfinished.

Source: Aschbacher–Smith E.2.14(5,7,9), pp.226–228, H.4.4, p.381,
and 8.2.2–4, pp.714–716 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The original half-field tensor has a strict selected actor-rank gap,
including half-degree one. No E.2.14 rank or torus input is used. -/
theorem sourceOrbit_hermitian_tensor_selected_actor_rank_gap
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    k < rank (inducedAutomizer D.sourceOrbit A) ∧ k < 4*n := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  obtain ⟨j,hj,_,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  let W := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A) :=
    inducedAutomizer_elementary D.sourceOrbit A (actor_normalizes s)
  have hu : rank (inducedAutomizer D.sourceOrbit A) ≤ 4*n :=
    (offender_rank_le_primeRank _).trans ((Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩))
  exact ⟨selected_actor_rank_gt_parameter s,(selected_actor_rank_gt_parameter s).trans_le hu⟩

/-- At the endpoint the original tensor has actor rank 3n and its literal
intersection has rank 4n. Local setup and TI are derived from the original
chosen-module assumptions. Only selection and the E.2.14 torus clause remain
explicit; no rank clause or replacement action is used. -/
theorem sourceOrbit_hermitian_tensor_endpoint_rank_three_mul
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hkn : k = 2*n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let Z := D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom
    rank (inducedAutomizer D.sourceOrbit A) = 3*n ∧ rank Z = 4*n ∧
      ∃ x : Automizer D.sourceOrbit,
        x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
        orderOf x = 2^(2*n)-1 ∧
        x ∈ normalizer (inducedAutomizer D.sourceOrbit A : Set (Automizer D.sourceOrbit)) ∧
        automizerFixedGroup D.sourceOrbit (zpowers x) = Z := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_tensor_hstar_setup
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel
  have hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit := by
    intro g hg
    exact (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti g hg.1
  obtain ⟨x,hx,ho,hn,hf⟩ := D.sourceOrbit_hermitian_selected_torus_fixed
    eT h28 hchar hTI s (by have hp := NeZero.pos n; omega)
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  obtain ⟨ha,_⟩ := selected_endpoint_actor_rank_three_mul s n hkn
    (D.hermitianOrbitCoordinates n d) j hj he x ho hx hf
  have hvr : rank D.sourceOrbit = 9*n := by
    rw [rank,show Nat.card D.sourceOrbit = Nat.card (Additive D.sourceOrbit) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      (D.hermitianOrbitCoordinates n d).finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hid := selected_actor_rank_identity s
  dsimp only at hid
  rw [ha,hkn,hvr] at hid
  exact ⟨ha,by omega,x,hx,by simpa only [hkn] using ho,hn,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
