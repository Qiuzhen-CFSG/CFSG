module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiAllLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiCartan
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# Mixed Suzuki exclusions on the original marked quotient

For an actual Suzuki original quotient of positive parameter, identify both
its canonical root actor and its root Sylow using the all-parameter local
cover. At the opposite unitary endpoint the earlier (1J) square profile
forces even field degree. The regular cover identifies the actual actor;
for SU₃ the canonical special-to-projective map is an isomorphism in this
even degree, proved with its scalar kernel retained. The source three-core
then fixes no nonidentity element of any unitary root and centralizes all
Suzuki roots. The literal original-S centralizer is exactly the product
of the two Suzuki roots with words s_i and s_i s_j. Its actual action and
incompatible Frattini bounds exclude the branch.

The same regular cover removes both original-factor perfectness premises
from the previously proved mixed linear/Suzuki exclusion. All supplied
linear fields are accepted, including two and four. The unitary input
accepts every positive degree and both special and projective quotients;
the square profile itself excludes its degree-one case here. Both endpoint
orientations and arbitrary supplied original/geometric amalgam markings
are supported, with separate literal Q.q applications.

Source: Fong--Seitz I (6C), printed pp.39--40. The square profile (1J),
finite split quotient and marking remain earlier source inputs. Sz(2),
equal-Suzuki, pure unitary and the exhaustive hexagon dichotomy remain
separate obligations. These theorems assume no original-factor perfectness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal HermitianForm
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- Root coordinates from the actual local image, for all Suzuki parameters
and without original-factor perfectness. -/
def originalSuzukiAllRootEquiv (j : Fin 2) [Finite (L j)]
    (T : Sylow 2 (L j)) (hT : (T : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) :
    simpleRoot Q split j ≃* SuzukiRootSubgroup m := by
  let a := suzukiAllLocalEquiv Q e h split j T hT μ
  let R := (GTwoSource.localSylow Q split j).mapSurjective (f := a.toMonoidHom) a.surjective
  let b : GTwoSource.localSylow Q split j ≃* R :=
    (GTwoSource.localSylow Q split j : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  exact (GTwoSource.simpleRootLocalSylowEquiv Q split j
    (suzuki_remainder_le_kernel_all Q e h split j T hT μ)).trans
    (b.trans ((R.equiv (ReeSource.matrixRootSylow m)).trans
      (MulEquiv.subgroupCongr (ReeSource.matrixRootSylow_carrier m))))

include e h in
/-- The mixed linear/Suzuki exclusion with both original-factor perfectness
premises removed. The actual regular cover and local projection identify
the linear actor, including the binary and field-four endpoints. -/
theorem original_mixed_linear_suzuki_exclusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hKi := linear_remainder_le_kernel Q e h split i Ti hTi μi
  have hKj := suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow Ti) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi μi]
    exact ((Nat.card_congr (linearSylowEquiv i Ti μi).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i Ti μi)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μi hz
    change μi z ∈ center PSL(2,F) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μi.injective (hh.trans μi.map_one.symm)
  let μlocal := (regularFactorLocalEquiv Q e h split i Ti hTi hKi hc hz).trans μi
  exact no_mixed_suzuki_of_square_profile Q split hhex i j hij hKi hKj μlocal
    (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
    hm (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj) hsquare

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

include e h hn hcard hconj in
private theorem original_unitary_root_order (i : Fin 2)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)) :
    Nat.card (simpleRoot Q split i) = (2^n)^3 := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · exact projectiveUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ
  · exact specialUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ

include e h hn hcard hconj in
/-- The same canonical actor is projective unitary at even degree. In the
special case the scalar kernel vanishes by its actual determinant and norm
identities; no central quotient is silently discarded. -/
private theorem original_even_unitary_actor (heven : Even n) (i : Fin 2)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hn2 : 2 ≤ n := by have := Nat.even_iff.mp heven; omega
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hV := projectiveUnitary_remainder_le_kernel Q e h split i T hT J hn2 hcard hconj μ
    exact ⟨hV,⟨(regularFactorRootEquiv Q e h split i T hT hV
      (projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj μ)).trans μ⟩⟩
  · have hV := specialUnitary_remainder_le_kernel Q e h split i T hT J hn2 hcard hconj μ
    exact ⟨hV,⟨((regularFactorRootEquiv Q e h split i T hT hV
      (specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj μ)).trans μ).trans
      (EvenProjectiveComparison.specialProjectiveEquiv J heven hconj)⟩⟩

include e h hn hcard hconj in
/-- Source Z(O₃(H)) acts without fixed points on the actual unitary roots,
for both special and projective original factors, without perfectness. -/
theorem original_unitary_threeCartan_fixedFree (heven : Even n) (i : Fin 2)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)) :
    threeCartan Q ⊓ rankOne Q split i ≠ ⊥ ∧
      ∀ w, rootAt Q split i w ⊓ centralizer (threeCartan Q : Set (X ⧸ Q.D)) = ⊥ := by
  obtain ⟨hKi,⟨μ⟩⟩ := original_even_unitary_actor Q e h split J hn hcard hconj heven i hmodel
  have hn2 : 2 ≤ n := by have := Nat.even_iff.mp heven; omega
  exact unitary_threeCartan_nontrivial_fixedFree J Q split hn2 hcard hconj heven i hKi μ
    (original_unitary_root_order Q e h split J hn hcard hconj i hmodel)
    (UnitarySource.actorReflection Q split i)

include e h hn hcard hconj in
/-- The literal original-S centralizer product used in the mixed (6C) proof. -/
theorem original_mixed_unitary_suzuki_centralizer_product
    (heven : Even n) (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) :
    (((sylowMap Q e h).range ⊓
        rightConjugate (sylowMap Q e h).range
          ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)) ⊓
      centralizer (threeCartan Q : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (rightConjugate (simpleRoot Q split j)
        ((UnitarySource.actorReflection Q split i).val : X ⧸ Q.D) : Set (X ⧸ Q.D)) *
      (rightConjugate (simpleRoot Q split j)
        (((UnitarySource.actorReflection Q split i).val : X ⧸ Q.D)*
          (UnitarySource.actorReflection Q split j).val) : Set (X ⧸ Q.D)) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  let sj := UnitarySource.actorReflection Q split j
  let si := UnitarySource.actorReflection Q split i
  have hKj := suzuki_remainder_le_kernel_all Q e h split j T hT μj
  have hh := radical_centralizer_product Q split hhex i j hij (threeCartan Q)
    (threeCartan_le_cartan Q)
    (original_unitary_threeCartan_fixedFree Q e h split J hn hcard hconj heven i hmodel).2
    (threeCartan_centralizes_suzuki_roots Q split j hKj hm
      (suzukiAllRankOneEquiv Q e h split j T hT μj)
      (originalSuzukiAllRootEquiv Q e h split j T hT μj) sj)
  rw [marked_radical_eq h Q e split j sj.val sj.class_eq] at hh
  rw [rootAt_eq Q split j (Q.simple i) si.val si.class_eq,
    rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul,si.class_eq,sj.class_eq])] at hh
  exact hh

include e h hn hcard hconj in
/-- The mixed unitary/Suzuki exclusion from the original source models and
(1J). Positivity of the unitary degree allows q=2 as an input; (1J) rules
it out here. Neither original factor is assumed perfect. -/
theorem original_mixed_unitary_suzuki_exclusion
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  let νj := originalSuzukiAllRootEquiv Q e h split j T hT μj
  have hc := original_unitary_root_order Q e h split J hn hcard hconj i hmodel
  have heven := unitary_even_of_suzuki_square_profile Q split i j hc νj hsquare
  obtain ⟨hKi,⟨μi⟩⟩ := original_even_unitary_actor Q e h split J hn hcard hconj heven i hmodel
  exact no_mixed_unitary_suzuki_of_square_profile J Q split hn hcard hconj hhex i j hij
    hKi (suzuki_remainder_le_kernel_all Q e h split j T hT μj) μi hc
    (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
    hm (suzukiAllRankOneEquiv Q e h split j T hT μj) νj hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal HermitianForm
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The fixed subgroup in the original finite source quotient uses precisely
Q.q(S), with both right-conjugation words retained. -/
theorem quotient_mixed_unitary_suzuki_centralizer_product
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n)) (heven : Even n)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) :
    ((((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)) ⊓
      centralizer (threeCartan Q : Set ((generated L S) ⧸ Q.D)) : Set ((generated L S) ⧸ Q.D)) =
      (rightConjugate (simpleRoot Q split j)
        ((UnitarySource.actorReflection Q split i).val : (generated L S) ⧸ Q.D) : Set _) *
      (rightConjugate (simpleRoot Q split j)
        (((UnitarySource.actorReflection Q split i).val : (generated L S) ⧸ Q.D)*
          (UnitarySource.actorReflection Q split j).val) : Set _) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_mixed_unitary_suzuki_centralizer_product Q (originalMarkedIso Q)
    h split J hn hcard hconj heven hhex i j hij hmodel hm μj
  rw [sylow_range Q (originalMarkedIso Q) h split] at hh
  exact hh

/-- The full original quotient-map application of the mixed unitary/Suzuki
exclusion. The earlier source (1J) premise remains with source assembly. -/
theorem quotient_mixed_unitary_suzuki_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_mixed_unitary_suzuki_exclusion Q (originalMarkedIso Q) h split
    J hn hcard hconj hhex i j hij hmodel hm μj hsquare

/-- The literal original quotient application of the mixed linear exclusion,
without a perfectness restriction on either original factor. -/
theorem quotient_mixed_linear_suzuki_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_mixed_linear_suzuki_exclusion Q (originalMarkedIso Q) h split hhex i j hij μi hm μj hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
