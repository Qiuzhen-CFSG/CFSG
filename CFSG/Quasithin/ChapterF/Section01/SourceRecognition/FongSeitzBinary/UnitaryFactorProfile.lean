module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OriginalActorQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CombinedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryProfileCoordinates

/-!
# Unitary-five inputs from the original factor profile

The original PSL₂ and SU₃-or-PSU₃ quotient markings determine the full-Borel
indices q²+1 and q³+1 on the same marked quotient. The PSL₂ marking extends
to the whole original actor with its exact two-core kernel and makes the
original Sylow quotient elementary. The unitary core order q⁷ then proves
both remainder/kernel containments. The generic SU₃ cover and canonical
root reflections complete the existing FiveProfile input, including q=2.

The linear actor retains its prescribed original quotient map. Applying
the proved natural-section theorem preserves the unitary factor square,
root-actor square and scalar kernel. The original quotient application uses
literal Q.q representatives, and the Chapter 12 application retains the
full KnownSimple and proper-K hypotheses through its actual preparation.

Only the original factor markings, special core data, marked split quotient
and rotation order four are assumed. The source profile producer is
qt-dgs85-commuting-one-profile; the quotient producer is
qt-dgs85-apartment-exchange. Common labels and whole-root equations stay
with the unitary-five source owner. Neither the profile construction nor
the natural-section application asserts a full U₅ amalgam comparison or
exhaustive source selection.

Sources: DGS (11.8)(a)--(f), pp.175--176; Fong--Seitz I (5B)--(5C),
(6A)(c), pp.25--26,37--38; II (8.13)--(8.15), pp.203--204; AS 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))

include mark h split hn hE hconj in
/-- Either original unitary quotient gives the full original Borel index,
without a perfectness or local-kernel containment premise. -/
theorem unitary_factor_borel_index (j : Fin 2)
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1 := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  have hc : Nat.card (simpleRoot Q split j) = (2^n)^3 := by
    rcases hfactor with hs | hp
    · obtain ⟨a⟩ := hs
      exact MarkedLocal.specialUnitary_simpleRoot_card Q mark h split j T hT J hn hE hconj a
    · obtain ⟨a⟩ := hp
      exact MarkedLocal.projectiveUnitary_simpleRoot_card Q mark h split j T hT J hn hE hconj a
  rw [marked_commonBorel_root_index Q mark h split j,hc,Nat.add_comm]

variable (hK : Nat.card K = (2^n)^2)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
  (hQj : Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7)
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))

include mark h split hn hE hconj hK hJ hm hij μi hfactor hQj hderived hfrattini in
/-- Construct every auxiliary input to (6A)(c) from the original factor and
special-core profile, retaining the prescribed linear quotient map. -/
theorem marked_unitary_factor_profile :
    ∃ d : UnitarySource.Combined.FiveProfile L S Q split K E n i j,
      d.form = J ∧
      (∀ a : L i, d.linear_actor (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic L S k) := by
  obtain ⟨f,hf,hker,hfactors⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μi
  have hQi := MarkedLocal.sylow_core_elementary_of_linear_actor h i f hker
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1 := by
    rw [marked_commonBorel_root_index Q mark h split i,
      MarkedLocal.simpleRoot_card_linear Q mark h split i T hT μi,hK,Nat.add_comm]
  have hindexj := unitary_factor_borel_index Q mark h split J hn hE hconj j hfactor
  have hr := marked_unitary_profile_regularity Q mark h split hm i j hij (2^n)
    (pow_pos (by decide) n) hindexi hindexj hQi hQj
  obtain ⟨ν,π,hπ,hπν⟩ := MarkedLocal.regular_unitary_cover_of_factor Q mark h split
    J hn hE hconj j (hr j).1 hfactor
  refine ⟨{
    form := J
    linear_card := hK
    unitary_card := hE
    fixed_card := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
    matrix := hJ
    conjugation := hconj
    linear_remainder := (hr i).1
    unitary_remainder := (hr j).1
    linear_reflection := Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.actorReflection Q split i
    unitary_reflection := Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.actorReflection Q split j
    linear_actor := f
    linear_surjective := hf
    linear_kernel := hker
    unitary_panel := ν
    cover := π
    cover_surjective := hπ
    cover_square := hπν
    linear_index := hindexi
    unitary_index := hindexj
    linear_sylow_elementary := hQi
    unitary_derived := hderived
    unitary_frattini := hfrattini },rfl,hfactors,hr⟩

variable [CharP E 2]

include mark h split hn hE hconj hK hJ hm hij μi hfactor hQj hderived hfrattini in
/-- The actual factor profile constructs natural coordinates on the same unitary
Frattini section and preserves both original actor markings and scalar squares. -/
theorem marked_unitary_factor_coordinates :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
        pCore 2 (parabolic L S k),
    ∃ (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
      (ξ : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
      (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      Function.Surjective f ∧
      f.ker = (pCore 2 (parabolic L S i)).subgroupOf
        ((S ⊔ L i).subgroupOf (parabolic L S i)) ∧
      (∀ a : L i, f (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q mark h split j l) =
        J.specialToProjective (ξ l)) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      (RootLocalCover.projection Q split j).ker = center (rankOne Q split j) ∧
      ∀ r v, c (elementaryRepresentation (p := 2)
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainderFrattiniAction
          Q split j (hr j).1) r v) = Matrix.mulVec (κ r).val.val (c v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨d,_,hfactors,_⟩ := marked_unitary_factor_profile Q mark h split J hn hE hconj
    hK hJ hm i j hij μi hfactor hQj hderived hfrattini
  obtain ⟨hr,ξ,ν,κ,γ,c,hpanel,hfactorSquare,hker,_,_,hc⟩ :=
    UnitaryFiveSource.marked_unitary_profile_coordinates Q split mark h J hn hE hJ hconj
      hm i j hij hfactor d.linear_index d.unitary_index d.linear_sylow_elementary
      hQj hderived hfrattini
  exact ⟨hr,d.linear_actor,ξ,ν,κ,c,d.linear_surjective,d.linear_kernel,
    hfactors,hfactorSquare,hpanel,hker,hc⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure


namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G K E : Type*} [Group G] [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hK : Nat.card K = (2^n)^2)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
  (hQj : Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7)
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
include h hn hE hJ hconj hm hij hfactor hK μi hQj hderived hfrattini

/-- The same natural action on literal source quotient representatives, with
both original core preimages and the original factor's projective square. -/
theorem original_unitary_factor_representatives :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ _hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q (originalMarkedIso Q) k) =
        pCore 2 (parabolic L S k),
    ∃ (ξ : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
      (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q (originalMarkedIso Q) h split j l) =
        J.specialToProjective (ξ l)) ∧
      (RootLocalCover.projection Q split j).ker = center (rankOne Q split j) ∧
      ∀ (a v : generated L S) (ha : Q.q a ∈ rankOne Q split j)
        (hv : Q.q v ∈ simpleRemainder Q split j),
        ∃ w : simpleRemainder Q split j,
          (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
          c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w)) =
            Matrix.mulVec (κ ⟨Q.q a,ha⟩).val.val
              (c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j))
                ⟨Q.q v,hv⟩))) := by
  obtain ⟨d,_,_,_⟩ := marked_unitary_factor_profile Q (originalMarkedIso Q) h split
    J hn hE hconj hK hJ hm i j hij μi hfactor hQj hderived hfrattini
  exact UnitaryFiveSource.original_unitary_profile_representatives Q split h J hn hE hJ hconj
    hm i j hij hfactor d.linear_index d.unitary_index d.linear_sylow_elementary
    hQj hderived hfrattini
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X K E : Type*} [Group G] [Finite G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The selected Chapter 12 factors give the full U5 profile, including all
kernel, actor, index, reflection and cover inputs. The earlier source core
profile and the same marked split quotient remain explicit. -/
theorem rankOne_global_unitary_factor_profile
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m)
    (hK : Nat.card K = (2^m)^2) (hE : Nat.card E = (2^m)^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^m))
    (μ : (L ⧸ pCore 2 L) ≃* PSL(2,K))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hQ : Nat.card ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) = (2^m)^7)
    (hderived : _root_.commutator ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
      center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2))
    (hfrattini : frattini ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
      center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2)) :
    ∃ profile : UnitarySource.Combined.FiveProfile ![L,R] (Global.sourceS L H)
      Q split K E m 0 1,
      profile.form = J ∧
      (∀ a : L, profile.linear_actor (MarkedLocal.originalFactorIntoActor 0 a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μ (QuotientGroup.mk' _ a))) ∧
      ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic ![L,R] (Global.sourceS L H) k) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact QuadrangleStructure.marked_unitary_factor_profile Q mark hf split J hmpos
    hE hconj hK hJ hm 0 1 (by decide) μ hfactor hQ hderived hfrattini

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
