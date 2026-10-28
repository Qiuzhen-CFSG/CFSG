module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SmallCharacteristic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalFrattiniRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedRadical

/-!
# Original small characteristic subgroups and literal quotient representatives

The endpoint marking identifies the original Φ²(O₂(P_i)) and
Φ([O₂(P_i),O₂(P_i)]) with their actual source subgroups. The positive
Suzuki actor centralizes both, and the binary quintic mover centralizes
both. The original F.1.1 hypothesis discharges self-centralization of the
endpoint two-core. The final specializations retain Q.q on original
representatives; the original ambient group need not be finite.

Source: Fong--Seitz I (1973), pp.52--53. This supplies valid small-section
centralization for the support argument. It does not make a whole
positive-parameter Suzuki root abelian or finish the remaining near
commutator, field pairing or (6H) clauses.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
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

/-- The actual original second Frattini subgroup, embedded in the same quotient. -/
def originalSecondPhiEquiv : frattini (frattini (pCore 2 (parabolic L S i))) ≃*
    (secondFrattiniRadicalSection Q split i hV).numerator := by
  let a := originalPhiRadicalEquiv Q e split i hV
  let V := (frattiniRadicalSection Q split i hV).numerator
  exact ((a.subgroupMap _).trans (MulEquiv.subgroupCongr (frattini_map_equiv a))).trans
    ((frattini V).equivMapOfInjective V.subtype V.subtype_injective)

@[simp] theorem originalSecondPhiEquiv_apply (v : frattini (frattini (pCore 2 (parabolic L S i)))) :
    (originalSecondPhiEquiv Q e split i hV v : X ⧸ Q.D) = endpointMap Q e i v.val.val.val := rfl

/-- The original derived-core Frattini subgroup retains its literal ambient inclusion. -/
def originalDerivedPhiEquiv : frattini (commutator (pCore 2 (parabolic L S i))) ≃*
    ((frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))).map
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype) := by
  let a := originalDerivedRadicalEquiv Q e split i hV
  let V : Subgroup (X ⧸ Q.D) := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
  exact ((a.subgroupMap _).trans (MulEquiv.subgroupCongr (frattini_map_equiv a))).trans
    ((frattini V).equivMapOfInjective V.subtype V.subtype_injective)

@[simp] theorem originalDerivedPhiEquiv_apply (v : frattini (commutator (pCore 2 (parabolic L S i)))) :
    (originalDerivedPhiEquiv Q e split i hV v : X ⧸ Q.D) = endpointMap Q e i v.val.val.val := rfl

variable {F : Type*} [Field F] [Finite F] [CharP F 2] (j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

omit hV in
include ν hC in
/-- The actual positive-parameter rank-one preimage centralizes both original small subgroups. -/
theorem original_positive_small_characteristic_centralizes
    (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hmpos : 0 < m) (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)
    (g : parabolic L S i) (hg : endpointMap Q e i g ∈ rankOne Q split i) :
    (∀ v : frattini (frattini (pCore 2 (parabolic L S i))), Commute g v.val.val.val) ∧
      (∀ v : frattini (commutator (pCore 2 (parabolic L S i))), Commute g v.val.val.val) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hh := source_positive_small_characteristic_centralizes Q split i j ν T hC m μ hB hmpos
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize
  have hf : Function.Injective (endpointMap Q e i) :=
    (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  constructor
  · intro v
    apply hf
    simpa only [map_mul,originalSecondPhiEquiv_apply] using mem_centralizer_iff.mp
      (hh.1 (originalSecondPhiEquiv Q e split i hV v).property) _ hg
  · intro v
    apply hf
    simpa only [map_mul,originalDerivedPhiEquiv_apply] using mem_centralizer_iff.mp
      (hh.2 (originalDerivedPhiEquiv Q e split i hV v).property) _ hg

omit hV in
include ν hC in
/-- Every original lift of the binary quintic mover centralizes both original small subgroups. -/
theorem original_binary_small_characteristic_centralizes
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < 64)
    (g : parabolic L S i) (hg : endpointMap Q e i g = frattiniMover Q split i 0 μ hB) :
    (∀ v : frattini (frattini (pCore 2 (parabolic L S i))), Commute g v.val.val.val) ∧
      (∀ v : frattini (commutator (pCore 2 (parabolic L S i))), Commute g v.val.val.val) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  have hh := source_binary_small_characteristic_centralizes Q split i j ν T hC μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize
  have hf : Function.Injective (endpointMap Q e i) :=
    (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  constructor
  · intro v
    apply hf
    simpa only [map_mul,hg,originalSecondPhiEquiv_apply] using mem_centralizer_iff.mp
      (hh.1 (originalSecondPhiEquiv Q e split i hV v).property) _ (Set.mem_singleton _)
  · intro v
    apply hf
    simpa only [map_mul,hg,originalDerivedPhiEquiv_apply] using mem_centralizer_iff.mp
      (hh.2 (originalDerivedPhiEquiv Q e split i hV v).property) _ (Set.mem_singleton _)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

theorem originalSecondPhiEquiv_quotient (v : frattini (frattini (pCore 2 (parabolic L S i)))) :
    (originalSecondPhiEquiv Q (originalMarkedIso Q) split i hV v : (generated L S) ⧸ Q.D) =
      Q.q ⟨v.val.val.val,parabolic_le_generated i v.val.val.val.property⟩ :=
  originalPhiRadicalEquiv_quotient Q split i hV v.val

theorem originalDerivedPhiEquiv_quotient (v : frattini (commutator (pCore 2 (parabolic L S i)))) :
    (originalDerivedPhiEquiv Q (originalMarkedIso Q) split i hV v : (generated L S) ⧸ Q.D) =
      Q.q ⟨v.val.val.val,parabolic_le_generated i v.val.val.val.property⟩ :=
  originalDerivedRadicalEquiv_quotient Q split i hV v.val

variable {F : Type*} [Field F] [Finite F] [CharP F 2] (j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

omit hV in
include ν hC in
/-- Literal Q.q commutation on both original small characteristic subgroups. -/
theorem original_positive_small_characteristic_quotient
    (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hmpos : 0 < m) (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)
    (g : generated L S) (hg : Q.q g ∈ rankOne Q split i) :
    (∀ v : frattini (frattini (pCore 2 (parabolic L S i))),
      Commute (Q.q g) (Q.q ⟨v.val.val.val,parabolic_le_generated i v.val.val.val.property⟩)) ∧
    (∀ v : frattini (commutator (pCore 2 (parabolic L S i))),
      Commute (Q.q g) (Q.q ⟨v.val.val.val,parabolic_le_generated i v.val.val.val.property⟩)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hh := source_positive_small_characteristic_centralizes Q split i j ν T hC m μ hB hmpos
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i) hm hij hsize
  constructor
  · intro v
    rw [←originalSecondPhiEquiv_quotient Q split i hV v]
    exact mem_centralizer_iff.mp
      (hh.1 (originalSecondPhiEquiv Q (originalMarkedIso Q) split i hV v).property) _ hg
  · intro v
    rw [←originalDerivedPhiEquiv_quotient Q split i hV v]
    exact mem_centralizer_iff.mp
      (hh.2 (originalDerivedPhiEquiv Q (originalMarkedIso Q) split i hV v).property) _ hg

omit hV in
include ν hC in
/-- The binary specialization uses the actual quintic lift and the same Q.q. -/
theorem original_binary_small_characteristic_quotient
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < 64)
    (g : generated L S) (hg : Q.q g = frattiniMover Q split i 0 μ hB) :
    (∀ v : frattini (frattini (pCore 2 (parabolic L S i))),
      Commute (Q.q g) (Q.q ⟨v.val.val.val,parabolic_le_generated i v.val.val.val.property⟩)) ∧
    (∀ v : frattini (commutator (pCore 2 (parabolic L S i))),
      Commute (Q.q g) (Q.q ⟨v.val.val.val,parabolic_le_generated i v.val.val.val.property⟩)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  have hh := source_binary_small_characteristic_centralizes Q split i j ν T hC μ hB
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i) hm hij hsize
  constructor
  · intro v
    rw [←originalSecondPhiEquiv_quotient Q split i hV v,hg]
    exact mem_centralizer_iff.mp
      (hh.1 (originalSecondPhiEquiv Q (originalMarkedIso Q) split i hV v).property) _ (Set.mem_singleton _)
  · intro v
    rw [←originalDerivedPhiEquiv_quotient Q split i hV v,hg]
    exact mem_centralizer_iff.mp
      (hh.2 (originalDerivedPhiEquiv Q (originalMarkedIso Q) split i hV v).property) _ (Set.mem_singleton _)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

