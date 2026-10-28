module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RadicalDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalMixedBounds

/-!
# Effective Ree radical modules on the original endpoint

F.1.1 supplies local characteristic two on the same marked finite quotient.
The natural Suzuki marking supplies the remainder-to-panel-kernel inclusion.
Together they make the actual source rank-one action faithful on both the
radical Frattini quotient and its abelianization, for every m including zero.
The faithful full-endpoint image supplies the q^4 lower bound. With the
linear marking at the other endpoint, the original Frattini and derived
radicals have order at most q_Suz^2 q_lin^4, before field synchronization.

The original endpoint action has kernel exactly its actual two-core. The
constructed two-core and Frattini equivalences use that same endpoint map,
intertwine actual conjugation, and retain the literal Q.q representatives
and source right-conjugation convention. No original ambient finiteness,
perfectness, synchronized field, or natural radical-module premise is added.

Source: Fong--Seitz I (1973), (5F)(a), pp.27--28, and the effective-module
estimates preceding (6.1), p.52; Aschbacher--Smith F.1.1 supplies the stronger
local-characteristic-two input. The derived-radical action, (6.1)/(6.4),
nonzero commutator equality, remaining (6H), Section 10 coordinates and final
marked Chapter12 comparison remain obligations of this source family.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

def originalEndpointFrattiniAction : parabolic L S i →*
    MulAut ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) :=
  (endpointFrattiniAction Q split i hV).comp (endpoint Q e i).toMonoidHom

include h in
theorem originalEndpointFrattiniAction_ker :
    (originalEndpointFrattiniAction Q e split i hV).ker = pCore 2 (parabolic L S i) := by
  change (endpointFrattiniAction Q split i hV).ker.comap (endpoint Q e i).toMonoidHom = _
  rw [endpointFrattiniAction_ker Q split i hV (parabolic_core_selfCentralizing Q e h i)]
  exact remainder_comap_of_containment Q e split i hV

/-- The actual two-core equivalence is induced by the original endpoint map. -/
def originalRadicalEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) : pCore 2 (parabolic L S i) ≃* simpleRemainder Q split i := by
  let f := endpointMap Q e i
  have hf : Function.Injective f :=
    (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have hrange : f.range = Endpoint Q i := by
    dsimp only [f]
    rw [endpointMap, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ← MonoidHom.range_eq_map,range_subtype]
  have he : (pCore 2 (parabolic L S i)).map f = simpleRemainder Q split i := by
    rw [← remainder_comap_of_containment Q e split i hV, map_comap_eq, hrange]
    exact inf_eq_right.mpr (inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _)))
  exact ((pCore 2 (parabolic L S i)).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he)

@[simp] theorem originalRadicalEquiv_apply (v : pCore 2 (parabolic L S i)) :
    (originalRadicalEquiv Q e split i hV v : X ⧸ Q.D) = endpointMap Q e i v := rfl

def originalRadicalFrattiniEquiv :
    (pCore 2 (parabolic L S i) ⧸ frattini (pCore 2 (parabolic L S i))) ≃*
      ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) :=
  QuotientGroup.congr _ _ (originalRadicalEquiv Q e split i hV) (frattini_map_equiv _)

@[simp] theorem originalRadicalFrattiniEquiv_mk (v : pCore 2 (parabolic L S i)) :
    originalRadicalFrattiniEquiv Q e split i hV (QuotientGroup.mk v) =
      QuotientGroup.mk (originalRadicalEquiv Q e split i hV v) := rfl

/-- The full original endpoint acts by its actual conjugation on core representatives. -/
theorem originalEndpointFrattiniAction_conjugation (g : parabolic L S i)
    (v : pCore 2 (parabolic L S i)) :
    originalEndpointFrattiniAction Q e split i hV g
      (originalRadicalFrattiniEquiv Q e split i hV (QuotientGroup.mk v)) =
        originalRadicalFrattiniEquiv Q e split i hV
          (QuotientGroup.mk (MulAut.conjNormal g v)) := by
  rw [originalRadicalFrattiniEquiv_mk, originalRadicalFrattiniEquiv_mk]
  change endpointFrattiniAction Q split i hV (endpoint Q e i g)
    (QuotientGroup.mk (originalRadicalEquiv Q e split i hV v)) = _
  rw [endpointFrattiniAction_mk]
  congr 1
  apply Subtype.ext
  simp only [endpointRadicalAction_apply, originalRadicalEquiv_apply]
  change endpointMap Q e i g * endpointMap Q e i v * (endpointMap Q e i g)⁻¹ =
    endpointMap Q e i (g*v*g⁻¹)
  rw [map_mul,map_mul,map_inv]

variable (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include e h in
/-- The actual Suzuki radical's effective representation is faithful, at every parameter. -/
theorem original_suzuki_effective_radical :
    let d := radicalSection Q split i (marked_suzuki_remainder_le_kernel Q split i m μ hB)
    d.IsEffective ∧ Function.Injective d.effectiveRepresentation ∧
      Function.Injective (radicalQuotientAction Q split i
        (marked_suzuki_remainder_le_kernel Q split i m μ hB)) := by
  have hc := parabolic_core_selfCentralizing Q e h i
  exact ⟨radical_isEffective Q split i _ hc,
    radical_effectiveRepresentation_injective Q split i _ hc,
    radical_abelianizationAction_injective Q split i _ hc⟩

include e h split hB in
/-- The actual original endpoint two-core has Frattini section of order at least q^4. -/
theorem original_suzuki_radical_frattini_card_ge :
    (2^(2*m+1))^4 ≤ Nat.card
      (pCore 2 (parabolic L S i) ⧸ frattini (pCore 2 (parabolic L S i))) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  rw [Nat.card_congr (originalRadicalFrattiniEquiv Q e split i hV).toEquiv]
  exact suzuki_radical_frattini_card_ge Q split i hV
    (parabolic_core_selfCentralizing Q e h i) m μ

include e h split hB in
theorem original_suzuki_radical_frattini_finrank_ge :
    4*(2*m+1) ≤ Module.finrank (ZMod 2) (UnitarySource.CoreSpace Q split i) :=
  suzuki_radical_frattini_finrank_ge Q split i
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)
    (parabolic_core_selfCentralizing Q e h i) m μ

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include e h split hB ν hC in
/-- The original Frattini and derived radicals satisfy the p.52 upper bound
with both still-independent rank-one fields retained. -/
theorem original_suzuki_radical_small_subgroups
    (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (frattini (pCore 2 (parabolic L S i))) ≤
        (2^(2*m+1))^2 * (Nat.card F)^4 ∧
      Nat.card (commutator (pCore 2 (parabolic L S i))) ≤
        (2^(2*m+1))^2 * (Nat.card F)^4 := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let a := originalRadicalEquiv Q e split i hV
  have hlo := suzuki_radical_frattini_card_le Q split i j m μ hB hV
    (parabolic_core_selfCentralizing Q e h i) hm hij
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hlo
  have hphi : Nat.card (frattini (pCore 2 (parabolic L S i))) ≤
      (2^(2*m+1))^2 * (Nat.card F)^4 := by
    rw [← card_map_of_injective (f := a.toMonoidHom) a.injective, frattini_map_equiv]
    exact hlo
  let := h.finite_parabolic i
  let : Fact (IsPGroup 2 (pCore 2 (parabolic L S i))) := ⟨pCore_isPGroup⟩
  exact ⟨hphi,(Nat.le_of_dvd Nat.card_pos
    (card_dvd_of_le (commutator_le_frattini_of_isPGroup (p := 2)))).trans hphi⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource


@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

/-- The core equivalence uses the literal original generated-carrier quotient. -/
theorem originalRadicalEquiv_quotient (v : pCore 2 (parabolic L S i)) :
    (originalRadicalEquiv Q (originalMarkedIso Q) split i hV v : (generated L S) ⧸ Q.D) =
      Q.q ⟨v,parabolic_le_generated i v.val.property⟩ := by
  rw [originalRadicalEquiv_apply]
  fin_cases i
  · exact originalMarkedIso_left_apply Q v.val
  · exact originalMarkedIso_right_apply Q v.val

/-- Right conjugation on the actual effective section retains both Q.q representatives. -/
theorem original_endpoint_frattini_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ Endpoint Q i)
    (hv : Q.q v ∈ simpleRemainder Q split i) :
    ∃ w : simpleRemainder Q split i,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      endpointFrattiniAction Q split i hV (⟨Q.q g,hg⟩ : Endpoint Q i)⁻¹
        (QuotientGroup.mk (⟨Q.q v,hv⟩ : simpleRemainder Q split i)) = QuotientGroup.mk w := by
  let w := endpointRadicalAction Q split i hV (⟨Q.q g,hg⟩ : Endpoint Q i)⁻¹ ⟨Q.q v,hv⟩
  refine ⟨w,?_,endpointFrattiniAction_mk Q split i hV _ _⟩
  rw [endpointRadicalAction_apply, coe_inv, inv_inv, map_mul,map_mul,map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
