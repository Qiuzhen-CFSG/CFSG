module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FrattiniRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalEffectiveRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.CommonField

/-!
# Frattini-radical source bounds at the original endpoints

The marked endpoint equivalence identifies Φ(O₂(P_i)) with the ambient
image of Φ(U ∩ U^s). Its Frattini quotient intertwines actual conjugation,
and the original generated-carrier specialization retains the literal Q.q
formula. The existing source (6.3), proved from the two independent natural
panel markings, supplies the centralization needed for the moving-square
argument. Thus the effective Frattini action is faithful for every m,
including Sz(2), and its quotient has order at least q_Suz⁴.

Original local characteristic two gives
|Φ²(O₂(P_i))| q_Suz² ≤ q_lin⁴. An order-four element of Φ(O₂(P_i))
in the indicated shifted Suzuki root would force q_Suz⁶ ≤ q_lin⁴.
The final source corollary applies the existing common-field theorem to
exclude such elements, retaining its explicit odd-linear-degree hypothesis.
No field equality or mixed-commutator premise remains in that corollary.

Source: Fong--Seitz I (1973), (5D) and the effective-section size arguments
in (6H), pp.26--27,52--53. These bounds do not identify Φ(V) with [V,V]
or establish (6.1)/(6.4). Rank-one pairing and odd degree, the remaining
(6H) assertions, synchronized §10 coordinates and relations, and the final
Chapter12 marked comparison remain in the same source-construction task.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

def originalPhiRadicalEquiv : frattini (pCore 2 (parabolic L S i)) ≃*
    (frattiniRadicalSection Q split i hV).numerator := by
  let a := originalRadicalEquiv Q e split i hV
  let V := simpleRemainder Q split i
  exact ((a.subgroupMap _).trans (MulEquiv.subgroupCongr (frattini_map_equiv a))).trans
    ((frattini V).equivMapOfInjective V.subtype V.subtype_injective)

@[simp] theorem originalPhiRadicalEquiv_apply (v : frattini (pCore 2 (parabolic L S i))) :
    (originalPhiRadicalEquiv Q e split i hV v : X ⧸ Q.D) = endpointMap Q e i v.val.val := rfl

def originalPhiFrattiniEquiv :
    (frattini (pCore 2 (parabolic L S i)) ⧸ frattini (frattini (pCore 2 (parabolic L S i)))) ≃*
      ((frattiniRadicalSection Q split i hV).numerator ⧸
        frattini (frattiniRadicalSection Q split i hV).numerator) :=
  QuotientGroup.congr _ _ (originalPhiRadicalEquiv Q e split i hV) (frattini_map_equiv _)

@[simp] theorem originalPhiFrattiniEquiv_mk (v : frattini (pCore 2 (parabolic L S i))) :
    originalPhiFrattiniEquiv Q e split i hV (QuotientGroup.mk v) =
      QuotientGroup.mk (originalPhiRadicalEquiv Q e split i hV v) := rfl

/-- Restriction to the original Frattini core retains the actual conjugation. -/
theorem originalPhiRadicalEquiv_conjugation
    (g : parabolic L S i) (hg : endpointMap Q e i g ∈ rankOne Q split i)
    (v : frattini (pCore 2 (parabolic L S i))) :
    (frattiniRadicalSection Q split i hV).numeratorAction ⟨endpointMap Q e i g,hg⟩
      (originalPhiRadicalEquiv Q e split i hV v) =
      originalPhiRadicalEquiv Q e split i hV
        (MulAut.characteristic (frattini (pCore 2 (parabolic L S i))) (MulAut.conjNormal g) v) := by
  apply Subtype.ext
  change endpointMap Q e i g * endpointMap Q e i v.val.val * (endpointMap Q e i g)⁻¹ =
    endpointMap Q e i (g*v.val.val*g⁻¹)
  rw [map_mul,map_mul,map_inv]

theorem originalPhiFrattiniEquiv_conjugation
    (g : parabolic L S i) (hg : endpointMap Q e i g ∈ rankOne Q split i)
    (v : frattini (pCore 2 (parabolic L S i))) :
    quotientAut (frattini (frattiniRadicalSection Q split i hV).numerator)
      ((frattiniRadicalSection Q split i hV).numeratorAction ⟨endpointMap Q e i g,hg⟩)
        (originalPhiFrattiniEquiv Q e split i hV (QuotientGroup.mk v)) =
      originalPhiFrattiniEquiv Q e split i hV
        (QuotientGroup.mk
          (MulAut.characteristic (frattini (pCore 2 (parabolic L S i))) (MulAut.conjNormal g) v)) := by
  simp only [originalPhiFrattiniEquiv_mk]
  exact (quotientAut_apply_mk (frattini
    (frattiniRadicalSection Q split i hV).numerator)
      ((frattiniRadicalSection Q split i hV).numeratorAction ⟨endpointMap Q e i g,hg⟩)
      (originalPhiRadicalEquiv Q e split i hV v)).trans
    (congrArg (QuotientGroup.mk' (frattini
      (frattiniRadicalSection Q split i hV).numerator))
      (originalPhiRadicalEquiv_conjugation Q e split i hV g hg v))

variable (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include e hB ν hC in
/-- The existing source (6.3) discharges the movement premise on the original Frattini core. -/
theorem original_suzuki_frattini_radical_effective (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
    (frattiniRadicalSection Q split i hVi).IsEffective ∧
      Function.Injective (frattiniRadicalSection Q split i hVi).effectiveRepresentation ∧
      Function.Injective (suzukiFrattiniRadicalRepresentation Q split i hVi m μ hB) ∧
      (2^(2*m+1))^4 ≤ Nat.card
        (frattini (pCore 2 (parabolic L S i)) ⧸
          frattini (frattini (pCore 2 (parabolic L S i)))) := by
  dsimp only
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hc := (source_six_three Q split i j m μ hB ν T hC hm hij).2
  have hf := frattiniRadical_effectiveAction_injective Q split i hVi m μ hB hm j hij hc
  refine ⟨?_, (frattiniRadicalSection Q split i hVi).effectiveRepresentation_injective hf,
    suzukiFrattiniRadicalRepresentation_injective Q split i hVi m μ hB hm j hij hc,?_⟩
  · unfold RootSection.IsEffective
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
    exact bot_le
  · rw [Nat.card_congr (originalPhiFrattiniEquiv Q e split i hVi).toEquiv]
    exact frattiniRadical_frattini_card_ge Q split i hVi m μ hB hm j hij hc

include e split hB ν hC in
/-- The bound on Φ² of the original two-core includes Sz(2), retaining independent fields. -/
theorem original_suzuki_frattini_frattini_weighted_card_le
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (frattini (frattini (pCore 2 (parabolic L S i)))) * (2^(2*m+1))^2 ≤
      (Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let a := originalRadicalEquiv Q e split i hVi
  let b := (a.subgroupMap (frattini (pCore 2 (parabolic L S i)))).trans
    (MulEquiv.subgroupCongr (frattini_map_equiv a))
  have hh := suzuki_frattini_frattini_weighted_card_le Q split i hVi m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm j hij
    (source_six_three Q split i j m μ hB ν T hC hm hij).2
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hh
  rw [←card_map_of_injective (f := b.toMonoidHom) b.injective, frattini_map_equiv]
  exact hh


include e split hB ν hC in
/-- The third-degree obstruction on an element of the original Frattini core. -/
theorem original_frattini_root_order_four_forces_card
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (a : frattini (pCore 2 (parabolic L S i)))
    (ha : endpointMap Q e i a.val.val ∈ rootAt Q split i (Q.simple j*Q.simple i))
    (han : a^2 ≠ 1) : (2^(2*m+1))^6 ≤ (Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let b := originalPhiRadicalEquiv Q e split i hVi a
  have hb : (b : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j*Q.simple i) := ha
  have hbn : (b : X ⧸ Q.D)^2 ≠ 1 := by
    intro hz
    apply han
    apply (originalPhiRadicalEquiv Q e split i hVi).injective
    rw [map_pow,map_one]
    exact Subtype.ext hz
  have hh := frattini_root_order_four_forces_card Q split i hVi m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm j hij
    (source_six_three Q split i j m μ hB ν T hC hm hij).2 ⟨b,hb⟩ b.property hbn
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hh
  exact hh

omit i hV m μ hB j ν T hC in
/-- With the existing odd-degree source hypothesis, common-field recognition
excludes order four in this root intersection with the original Frattini core.
The field equality and the source commutator premise are both discharged. -/
theorem original_frattini_root_square_of_odd_degree
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hcore : Q.tits.B.normalCore = ⊥)
    (a : frattini (pCore 2 (parabolic L S 1)))
    (ha : endpointMap Q e 1 a.val.val ∈ rootAt Q split 1 (Q.simple 0*Q.simple 1)) :
    a^2 = 1 := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  by_contra han
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  have hh := original_frattini_root_order_four_forces_card Q e split 1 m μ hB 0 ν T hC h hm
    (by decide) a ha han
  have hc : Nat.card (BinaryGaloisField n) = 2^n := GaloisField.card 2 n hn.pos.ne'
  rw [hc,he] at hh
  have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
  exact (Nat.pow_lt_pow_right hq (by decide : 4 < 6)).not_ge hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

theorem originalPhiRadicalEquiv_quotient (v : frattini (pCore 2 (parabolic L S i))) :
    (originalPhiRadicalEquiv Q (originalMarkedIso Q) split i hV v :
      (generated L S) ⧸ Q.D) =
      Q.q ⟨v.val.val,parabolic_le_generated i v.val.val.property⟩ :=
  originalRadicalEquiv_quotient Q split i hV v.val

/-- The actual Frattini-section action retains both literal Q.q representatives. -/
theorem original_frattini_effective_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split i)
    (hv : Q.q v ∈ (frattiniRadicalSection Q split i hV).numerator) :
    let d := frattiniRadicalSection Q split i hV
    ∃ w : d.numerator,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      d.effectiveAction (⟨Q.q g,hg⟩ : rankOne Q split i)⁻¹
        (QuotientGroup.mk (⟨Q.q v,hv⟩ : d.numerator)) = QuotientGroup.mk w := by
  let d := frattiniRadicalSection Q split i hV
  let w := d.numeratorAction (⟨Q.q g,hg⟩ : rankOne Q split i)⁻¹ ⟨Q.q v,hv⟩
  refine ⟨w,?_,d.effectiveAction_mk _ _⟩
  rw [RootSection.numeratorAction_apply,coe_inv,inv_inv,map_mul,map_mul,map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
