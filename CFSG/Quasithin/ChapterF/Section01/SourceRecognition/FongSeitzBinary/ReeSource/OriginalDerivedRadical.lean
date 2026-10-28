module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.DerivedRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalEffectiveRadical

/-!
# Derived-radical modules on the original marked endpoints

The actual endpoint map restricts to an isomorphism between the derived
subgroup of the original two-core and [U ∩ U^s,U ∩ U^s] in the same finite
quotient. Its Frattini quotient intertwines original conjugation, and the
source right-conjugation formula retains both literal Q.q representatives.

The natural Suzuki marking lifts to the full original root actor for every
m, including Sz(2). For m>0 the source reflection gives an effective derived
module; its actual Suzuki representation is faithful and its Frattini
quotient has order at least q^4. Together with F.1.1 local characteristic
two, this bounds the next original Frattini layer by
|Φ([O₂(P_i),O₂(P_i)])| q_Suz^2 ≤ q_lin^4, with the fields still independent.
The actor is the preimage of the root-generated subgroup, not the entire
original endpoint. No ambient finiteness or unknown-group simplicity is used.

Source: Fong--Seitz I (1973), (5C) and the effective modules in the proof of
(6H), pp.25--26,52. The binary derived-module argument, (6.1)/(6.4), the
nonzero mixed commutator, field pairing and odd degree, remaining (6H),
Section 10 coordinates, and final Chapter12 comparison remain in this family.
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
  (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

def originalDerivedRadicalEquiv : commutator (pCore 2 (parabolic L S i)) ≃*
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) := by
  let a := originalRadicalEquiv Q e split i hV
  let V := simpleRemainder Q split i
  have ha : (commutator (pCore 2 (parabolic L S i))).map a.toMonoidHom = commutator V := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.surjective]
    rfl
  exact (((a.subgroupMap _).trans (MulEquiv.subgroupCongr ha)).trans
    ((commutator V).equivMapOfInjective V.subtype V.subtype_injective)).trans
      (MulEquiv.subgroupCongr (map_subtype_commutator V))

@[simp] theorem originalDerivedRadicalEquiv_apply (v : commutator (pCore 2 (parabolic L S i))) :
    (originalDerivedRadicalEquiv Q e split i hV v : X ⧸ Q.D) = endpointMap Q e i v.val.val := rfl

def originalDerivedFrattiniEquiv :
    (commutator (pCore 2 (parabolic L S i)) ⧸ frattini (commutator (pCore 2 (parabolic L S i)))) ≃*
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⧸
        frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) :=
  QuotientGroup.congr _ _ (originalDerivedRadicalEquiv Q e split i hV) (frattini_map_equiv _)

@[simp] theorem originalDerivedFrattiniEquiv_mk (v : commutator (pCore 2 (parabolic L S i))) :
    originalDerivedFrattiniEquiv Q e split i hV (QuotientGroup.mk v) =
      QuotientGroup.mk (originalDerivedRadicalEquiv Q e split i hV v) := rfl

/-- Restriction to the original derived core retains the actual conjugation. -/
theorem originalDerivedRadicalEquiv_conjugation
    (g : parabolic L S i) (hg : endpointMap Q e i g ∈ rankOne Q split i)
    (v : commutator (pCore 2 (parabolic L S i))) :
    (derivedRadicalSection Q split i hV).numeratorAction ⟨endpointMap Q e i g,hg⟩
      (originalDerivedRadicalEquiv Q e split i hV v) =
      originalDerivedRadicalEquiv Q e split i hV
        (MulAut.characteristic (commutator (pCore 2 (parabolic L S i))) (MulAut.conjNormal g) v) := by
  apply Subtype.ext
  change endpointMap Q e i g * endpointMap Q e i v.val.val * (endpointMap Q e i g)⁻¹ =
    endpointMap Q e i (g*v.val.val*g⁻¹)
  rw [map_mul,map_mul,map_inv]

theorem originalDerivedFrattiniEquiv_conjugation
    (g : parabolic L S i) (hg : endpointMap Q e i g ∈ rankOne Q split i)
    (v : commutator (pCore 2 (parabolic L S i))) :
    quotientAut (frattini (derivedRadicalSection Q split i hV).numerator)
      ((derivedRadicalSection Q split i hV).numeratorAction ⟨endpointMap Q e i g,hg⟩)
        (originalDerivedFrattiniEquiv Q e split i hV (QuotientGroup.mk v)) =
      originalDerivedFrattiniEquiv Q e split i hV
        (QuotientGroup.mk
          (MulAut.characteristic (commutator (pCore 2 (parabolic L S i))) (MulAut.conjNormal g) v)) := by
  simp only [originalDerivedFrattiniEquiv_mk]
  exact (quotientAut_apply_mk (frattini
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)))
      ((derivedRadicalSection Q split i hV).numeratorAction ⟨endpointMap Q e i g,hg⟩)
      (originalDerivedRadicalEquiv Q e split i hV v)).trans
    (congrArg (QuotientGroup.mk' (frattini
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))))
      (originalDerivedRadicalEquiv_conjugation Q e split i hV g hg v))

variable (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The full source rank-one actor inside the original endpoint, including Sz(2). -/
def originalSuzukiActorEquiv : (rankOne Q split i).comap (endpointMap Q e i) ≃*
    SuzukiMatrixGroup m := by
  let f := endpointMap Q e i
  have hf : Function.Injective f := (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have hr : f.range = Endpoint Q i := by
    dsimp only [f]
    rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have he : ((rankOne Q split i).comap f).map f = rankOne Q split i := by
    rw [map_comap_eq,hr]
    exact inf_eq_right.mpr (rankOne_le_parabolic Q split i)
  exact ((((rankOne Q split i).comap f).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr he)).trans (suzukiActorEquiv Q split i m μ hB)

@[simp] theorem originalSuzukiActorEquiv_apply
    (r : (rankOne Q split i).comap (endpointMap Q e i)) :
    originalSuzukiActorEquiv Q e split i m μ hB r =
      μ (QuotientGroup.mk' (panelKernel Q i) (endpoint Q e i r.val)) := rfl

include e hB in
/-- The effective derived module is constructed on the same original core. -/
theorem original_suzuki_derived_radical_effective (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
    (derivedRadicalSection Q split i hVi).IsEffective ∧
      Function.Injective (derivedRadicalSection Q split i hVi).effectiveRepresentation ∧
      Function.Injective (suzukiDerivedRepresentation Q split i hVi m μ hB) ∧
      (2^(2*m+1))^4 ≤ Nat.card
        (commutator (pCore 2 (parabolic L S i)) ⧸
          frattini (commutator (pCore 2 (parabolic L S i)))) := by
  dsimp only
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  refine ⟨derivedRadical_isEffective Q split i hVi m μ hB hm hmpos,
    derivedRadical_effectiveRepresentation_injective Q split i hVi m μ hB hm hmpos,
    suzukiDerivedRepresentation_injective Q split i hVi m μ hB hm hmpos,?_⟩
  rw [Nat.card_congr (originalDerivedFrattiniEquiv Q e split i hVi).toEquiv]
  exact derivedRadical_frattini_card_ge Q split i hVi m μ hB hm hmpos

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include e split hB ν hC in
/-- The next original Frattini layer is bounded while both source fields stay independent. -/
theorem original_suzuki_derived_frattini_weighted_card_le
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hmpos : 0 < m) (hij : i ≠ j) :
    Nat.card (frattini (commutator (pCore 2 (parabolic L S i)))) * (2^(2*m+1))^2 ≤
      (Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let a := originalDerivedRadicalEquiv Q e split i hVi
  have hh := suzuki_derived_frattini_weighted_card_le Q split i hVi m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hmpos j hij
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hh
  rw [←card_map_of_injective (f := a.toMonoidHom) a.injective, frattini_map_equiv]
  exact hh

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

theorem originalDerivedRadicalEquiv_quotient (v : commutator (pCore 2 (parabolic L S i))) :
    (originalDerivedRadicalEquiv Q (originalMarkedIso Q) split i hV v :
      (generated L S) ⧸ Q.D) =
      Q.q ⟨v.val.val,parabolic_le_generated i v.val.val.property⟩ :=
  originalRadicalEquiv_quotient Q split i hV v.val

/-- Right conjugation in the effective derived section retains the literal original quotient. -/
theorem original_derived_effective_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split i)
    (hv : Q.q v ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆) :
    let d := derivedRadicalSection Q split i hV
    ∃ w : d.numerator,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      d.effectiveAction (⟨Q.q g,hg⟩ : rankOne Q split i)⁻¹
        (QuotientGroup.mk (⟨Q.q v,hv⟩ : d.numerator)) = QuotientGroup.mk w := by
  let d := derivedRadicalSection Q split i hV
  let w := d.numeratorAction (⟨Q.q g,hg⟩ : rankOne Q split i)⁻¹ ⟨Q.q v,hv⟩
  refine ⟨w,?_,d.effectiveAction_mk _ _⟩
  rw [RootSection.numeratorAction_apply,coe_inv,inv_inv,map_mul,map_mul,map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
