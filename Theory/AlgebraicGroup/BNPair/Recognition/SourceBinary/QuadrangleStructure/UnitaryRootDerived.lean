module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryRootCenter
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates
public import Theory.SpecificGroups.SU3.BinaryRootFrattini

/-!
# The actual unitary simple root and its derived layer

The canonical simple root maps isomorphically onto the full Sylow subgroup
of its faithful local permutation image. Sylow conjugacy in the actual
PSU3 model therefore supplies Hermitian root coordinates on this same
subgroup. The coordinate first projection places the derived subgroup
inside the elementary fixed-field center of order q. It is nonzero because
the root has order q cubed and its center has order q.

All arguments include q = 2. These are coordinates on a single root, not a
realization of the radical module or an identification of the full actor
with its projective image. The local marking and kernel containment are
the earlier section 5 inputs. UnitaryOppositeCommutator uses this small
nonzero layer to rule out commuting unitary roots.

Source: Fong--Seitz I (5C), (6A)(c), pp.26,37; Huppert II.10.12.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelTorus.EvenCenterAction
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
private def derivedEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    _root_.commutator A ≃* _root_.commutator B :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [commutator_def,Subgroup.map_commutator,Subgroup.map_top_of_surjective _ e.surjective]
    rfl))

variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

include hn hcard hfixed hJ in
private theorem coord_derived_data :
    IsElementaryAbelian 2 (_root_.commutator (hermitianUnipotentCoord J)) ∧
      Nat.card (_root_.commutator (hermitianUnipotentCoord J)) ≤ 2^n ∧
      _root_.commutator (hermitianUnipotentCoord J) ≠ ⊥ := by
  let C := hermitianUnipotentCoord J
  let z : center C ≃* Multiplicative (fixedField J) :=
    (MulEquiv.subgroupCongr (binary_coord_center J hn hcard hfixed)).trans
      (MonoidHom.ofInjective (centralCoord_injective J)).symm
  let : IsElementaryAbelian 2 (Multiplicative (fixedField J)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      change (2 : ℕ) • x.toAdd = 0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _) }
  let : IsElementaryAbelian 2 (center C) := IsElementaryAbelian.of_injective z.toMonoidHom z.injective
  have hcz : Nat.card (center C) = 2^n :=
    (Nat.card_congr z.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans hfixed)
  have hle : _root_.commutator C ≤ center C :=
    (Abelianization.commutator_subset_ker (BinaryRootFrattini.firstCoordinate J)).trans
      (BinaryRootFrattini.first_kernel_central J)
  let d := inclusion hle
  refine ⟨IsElementaryAbelian.of_injective d (inclusion_injective hle),
    (Nat.card_le_card_of_injective d (inclusion_injective hle)).trans_eq hcz,?_⟩
  intro hz
  have hz' := (commutator_eq_bot_iff_center_eq_top C).mp hz
  have hc : Nat.card C = (2^n)^3 := by
    exact (Nat.card_congr (MonoidHom.ofInjective (EvenInner.root_injective J hJ)).toEquiv).trans
      (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ (2^n) hcard hfixed)
  rw [hz',Nat.card_congr (topEquiv (G := C)).toEquiv,hc] at hcz
  have hq := Nat.one_lt_two_pow (show n ≠ 0 by omega)
  nlinarith [sq_nonneg ((2^n : ℕ)-1)]

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual canonical unitary root has the full Hermitian coordinates, including q=2. -/
def simpleRootUnitaryEquiv (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    simpleRoot Q split i ≃* hermitianUnipotentCoord J := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let T := (GTwoSource.localSylow Q split i).mapSurjective (f := μ.toMonoidHom) μ.surjective
  let t : GTwoSource.localSylow Q split i ≃* T :=
    (GTwoSource.localSylow Q split i : Subgroup (localGroup Q split i)).equivMapOfInjective
      μ.toMonoidHom μ.injective
  exact (GTwoSource.simpleRootLocalSylowEquiv Q split i hV).trans
    (t.trans ((T.equiv (EvenTwoRank.rootSylow J hJ hn hcard hfixed)).trans
      (MonoidHom.ofInjective (EvenInner.root_injective J hJ)).symm))

include hn hcard hfixed hJ in
/-- The unitary root-derived layer is nonzero, elementary and of order at most the fixed-field order. -/
theorem simpleRoot_unitary_derived (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    IsElementaryAbelian 2 (⁅simpleRoot Q split i,simpleRoot Q split i⁆ : Subgroup (X ⧸ Q.D)) ∧
      Nat.card (⁅simpleRoot Q split i,simpleRoot Q split i⁆ : Subgroup (X ⧸ Q.D)) ≤ 2^n ∧
      ⁅simpleRoot Q split i,simpleRoot Q split i⁆ ≠ ⊥ := by
  let e := derivedEquiv (simpleRootUnitaryEquiv J Q split hn hcard hfixed hJ i hV μ)
  obtain ⟨he,hc,hne⟩ := coord_derived_data J hn hcard hfixed hJ
  have ht : IsElementaryAbelian 2 (_root_.commutator (simpleRoot Q split i)) :=
    by
      let := he
      exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  constructor
  · rw [←map_subtype_commutator]
    let := ht
    exact IsElementaryAbelian.map _
  · constructor
    · rw [←map_subtype_commutator,card_map_of_injective (simpleRoot Q split i).subtype_injective]
      exact (Nat.card_congr e.toEquiv).le.trans hc
    · intro hz
      have ht' : _root_.commutator (simpleRoot Q split i) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ (simpleRoot Q split i).subtype_injective).mp
          ((map_subtype_commutator _).trans hz)
      have hc' : Nat.card (_root_.commutator (hermitianUnipotentCoord J)) = 1 := by
        rw [←Nat.card_congr e.toEquiv,ht',card_bot]
      exact hne (card_eq_one.mp hc')
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
