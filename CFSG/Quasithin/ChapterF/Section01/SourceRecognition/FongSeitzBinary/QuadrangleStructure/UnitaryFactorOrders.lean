module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryFactorOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorProfile

/-!
# The full unitary-five profile from the original mixed factors

The original PSL2 and SU3-or-PSU3 quotients construct the actual linear
actor and unitary cover. Their Frattini degree bounds force the quadratic
field relation. The root product gives the original unitary core order
q^7, and the previous Frattini theorem then proves its two specialness
equalities. Consequently the full FiveProfile and natural coordinates
follow without independent field-ratio, core-order or specialness inputs.

Both orientations and unitary parameter two are retained. Only that binary
unitary endpoint still needs its remainder/kernel containment; for larger
parameters the original unitary factor proves it internally. The marked
quotient, full Borel, both endpoint squares, rotation four and actual factor
quotients remain genuine earlier source inputs. The original application
retains literal Q.q representatives and the full scalar/projective square.
The independent U5 source owner retains the common labels and remaining
Cartan/Weyl equations; no seven-row comparison is asserted here.

Source: Fong--Seitz I (4B), (4D), (6A)(c), pp.19--23,37; II (8C);
DGS (11.8), pp.175--176; AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))

include mark h split hn hE hconj hJ hm hij μi hfactor in
/-- The actual mixed factor quotients force their quadratic field relation,
without perfectness or original core structure. -/
theorem marked_unitary_factor_orders
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    Nat.card K = (2^n)^2 := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hVi := MarkedLocal.linear_remainder_le_kernel Q mark h split i Ti hTi μi
  obtain ⟨f,hf,hk,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μi
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    marked_sylow_factor_normal Q mark h split i
  obtain ⟨μ,_,_,_⟩ := marked_linear_localGroup Q mark h split i
    (UnitarySource.actorReflection Q split i) hVi _ (subgroupOf_mono _ le_sup_left) f hf hk
  obtain ⟨ν,π,hπ,hπν⟩ := MarkedLocal.regular_unitary_cover_of_factor Q mark h split
    J hn hE hconj j hVj hfactor
  have hrj : Nat.card (simpleRoot Q split j) = (2^n)^3 := by
    rcases hfactor with hs | hp
    · exact MarkedLocal.specialUnitary_simpleRoot_card Q mark h split j Tj hTj J hn hE hconj hs.some
    · exact MarkedLocal.projectiveUnitary_simpleRoot_card Q mark h split j Tj hTj J hn hE hconj hp.some
  exact mixed_unitary_field_order Q split J hn hE hconj hJ hm i j hij hVi hVj μ
    (MarkedLocal.parabolic_core_selfCentralizing Q mark h j) ν π hπ hπν hrj

include mark h split hn hE hconj hJ hm hij μi hfactor in
/-- The field relation, original core order and both specialness equations
are consequences of the regular mixed factors on the same quotient. -/
theorem marked_unitary_factor_core
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    Nat.card K = (2^n)^2 ∧
      Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7 ∧
      _root_.commutator ((parabolic L S j).pCoreIn 2) = center ((parabolic L S j).pCoreIn 2) ∧
      frattini ((parabolic L S j).pCoreIn 2) = center ((parabolic L S j).pCoreIn 2) := by
  have hK := marked_unitary_factor_orders Q mark h split J hn hE hconj hJ hm i j hij μi hfactor hVj
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hVi := MarkedLocal.linear_remainder_le_kernel Q mark h split i T hT μi
  have hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1 := by
    rw [marked_commonBorel_root_index Q mark h split i,
      MarkedLocal.simpleRoot_card_linear Q mark h split i T hT μi,hK,Nat.add_comm]
  have hindexj := unitary_factor_borel_index Q mark h split J hn hE hconj j hfactor
  have hcard := (marked_unitary_root_orders Q mark h split hm i j hij (2^n)
    (pow_pos (by decide) n) hindexi hindexj).2.2.2.1
  have hc : Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7 :=
    (Nat.card_congr (markedCoreEquiv Q mark h split j hVj).toEquiv).trans hcard
  obtain ⟨hd,hphi,_⟩ := marked_unitary_core_special_of_factor Q mark h split J hn hE hconj hJ
    hm i j hij hVi hVj hindexi hfactor
  exact ⟨hK,hc,hd,hphi⟩

include mark h split hn hE hconj hJ hm hij μi hfactor in
/-- All auxiliary U5 profile premises follow from the regular original
mixed factors. The linear quotient map is the prescribed original map. -/
theorem marked_unitary_factor_profile_of_regular
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    ∃ d : UnitarySource.Combined.FiveProfile L S Q split K E n i j,
      d.form = J ∧
      (∀ a : L i, d.linear_actor (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic L S k) := by
  obtain ⟨hK,hcard,hd,hphi⟩ := marked_unitary_factor_core Q mark h split J hn hE hconj hJ
    hm i j hij μi hfactor hVj
  exact marked_unitary_factor_profile Q mark h split J hn hE hconj hK hJ hm i j hij
    μi hfactor hcard hd hphi

omit [CharP E 2] in
include mark h split hE hconj hfactor in
private theorem unitary_factor_regularity_of_nonbinary (hn2 : 2 ≤ n) :
    simpleRemainder Q split j ≤ localKernel Q j := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hfactor with hs | hp
  · exact MarkedLocal.specialUnitary_remainder_le_kernel Q mark h split j T hT J hn2 hE hconj hs.some
  · exact MarkedLocal.projectiveUnitary_remainder_le_kernel Q mark h split j T hT J hn2 hE hconj hp.some

include mark h split hE hconj hJ hm hij μi hfactor in
/-- Every nonbinary original mixed quadrangle constructs the full U5
profile without field, core-order, specialness or regularity hypotheses. -/
theorem marked_unitary_factor_profile_of_nonbinary (hn2 : 2 ≤ n) :
    ∃ d : UnitarySource.Combined.FiveProfile L S Q split K E n i j,
      d.form = J ∧
      (∀ a : L i, d.linear_actor (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic L S k) :=
  marked_unitary_factor_profile_of_regular Q mark h split J (by omega) hE hconj hJ
    hm i j hij μi hfactor
    (unitary_factor_regularity_of_nonbinary Q mark h split J hE hconj j hfactor hn2)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G K E : Type*} [Group G] [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
include h hn hE hJ hconj hm hij hfactor μi hVj

/-- The same natural action on literal source quotient representatives, with
both original core preimages and the original factor's projective square. -/
theorem original_unitary_factor_representatives_of_regular :
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
  obtain ⟨hK,hQj,hderived,hfrattini⟩ := marked_unitary_factor_core Q (originalMarkedIso Q) h split
    J hn hE hconj hJ hm i j hij μi hfactor hVj
  exact original_unitary_factor_representatives Q split h J hn hE hK hJ hconj hm i j hij
    μi hfactor hQj hderived hfrattini
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
