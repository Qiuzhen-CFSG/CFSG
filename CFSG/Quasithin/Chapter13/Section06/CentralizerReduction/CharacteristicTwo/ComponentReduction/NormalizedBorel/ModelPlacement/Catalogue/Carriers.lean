module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry

/-!
# Concrete Borel carriers for the large-field catalogue

This catalogue retains the defining exponent and specifies actual groups,
positive root subgroups and matrix/root Borels. The unitary constructor uses
an antidiagonal Hermitian form over the quadratic matrix field, together with
its specified Frobenius involution. Changing to that form uses a matrix
isometry. Symplectic central quotients are identified through the actual
quotient equivalence in characteristic two; triality uses the genuine
D₄ graph-field carrier; Ree uses the fixed-root model equivalence.

Every exponent-one constructor of `BinaryModelAt` is explicitly excluded by
`1 < m`. No simplicity or order certification is required here.

Source: Aschbacher–Smith A.2.3–4, 1.1.5(3a,b), and proof of 13.6.6,
printed p.927.
-/

@[expose] public section
noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped MatrixGroups Matrix
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.Catalogue
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.Unitary

/-- A concrete standard presentation, including its actual defining field.
The associated carrier, root subgroup and Borel are defined below. -/
inductive StandardModel : ℕ → Type 1
  | linearTwo (F : Type) [Field F] [Finite F] [CharP F 2]
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m) : StandardModel m
  | unitaryThree (F : Type) [Field F] [Finite F]
      (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = (2 ^ m) ^ 2)
      (hconj : ∀ x, J.conj x = x ^ (2 ^ m)) : StandardModel m
  | suzuki (n : ℕ) (hn : 1 ≤ n) : StandardModel (2 * n + 1)
  | linearThree (F : Type) [Field F] [Finite F] [CharP F 2]
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m) : StandardModel m
  | symplecticFour (F : Type) [Field F] [Finite F] [CharP F 2]
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m) : StandardModel m
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2]
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m) : StandardModel m
  | triality (m : ℕ) (hm : 1 < m) : StandardModel m
  | ree (n : ℕ) (hn : 1 ≤ n) : StandardModel (2 * n + 1)

namespace StandardModel

/-- The actual group of the standard presentation. -/
def Carrier {m : ℕ} (M : StandardModel m) : Type := by
  cases M with
  | linearTwo F _ _ => exact PSL(2, F)
  | unitaryThree F J _ _ _ _ => exact ↥(ProjectiveSpecialUnitaryMatrixGroup J)
  | suzuki n _ => exact ↥(SuzukiMatrixGroup n)
  | linearThree F _ _ => exact PSL(3, F)
  | symplecticFour F _ _ => exact ↥(Theory.SpecificGroups.SymplecticFour.Sp F)
  | g2 F _ _ => exact ↥(Atlas.G2.Model F)
  | triality n hn => exact Triality.Standard.Carrier (Triality.Standard.binaryParameters m (by omega))
  | ree n _ => exact ReeF4.Model n

instance {m : ℕ} (M : StandardModel m) : Group M.Carrier := by
  cases M <;> simp only [Carrier] <;> infer_instance

instance {m : ℕ} (M : StandardModel m) : Finite M.Carrier := by
  cases M with
  | unitaryThree F J hJ hm hF hconj =>
    exact Finite.of_surjective _ (suProjection_surjective J)
  | _ => simp only [Carrier]; infer_instance

/-- The full positive root subgroup, defined independently of its normalizer. -/
def U {m : ℕ} (M : StandardModel m) : Subgroup M.Carrier := by
  cases M with
  | linearTwo F _ _ => exact BenderSuzuki.Converse.PUnip F
  | unitaryThree F J hJ _ _ _ => exact (hermitianUnipotentPSU J hJ).range
  | suzuki n _ => exact SuzukiRootSubgroup n
  | linearThree F _ _ => exact Matrix.PSL3.LinearThree.unipotent F
  | symplecticFour F _ _ => exact Theory.SpecificGroups.SymplecticFour.unipotent
  | g2 F _ _ => exact Atlas.G2.unipotent
  | triality n hn =>
    exact Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters m (by omega))
  | ree n _ => exact ReeF4.Parabolics.unipotent n

/-- The concrete matrix/root Borel; it is never defined as an unknown normalizer. -/
def B {m : ℕ} (M : StandardModel m) : Subgroup M.Carrier := by
  cases M with
  | linearTwo F _ _ => exact BenderSuzuki.Converse.PBorel F
  | unitaryThree F J hJ _ _ _ => exact
      (hermitianUnipotentPSU J hJ).range ⊔ (hermitianTorusPSU J hJ).range
  | suzuki n _ => exact SuzukiBorelSubgroup n
  | linearThree F _ _ => exact Matrix.PSL3.LinearThree.borel F
  | symplecticFour F _ _ => exact Theory.SpecificGroups.SymplecticFour.borel
  | g2 F _ _ => exact Atlas.G2.borel
  | triality n hn =>
    exact Triality.Standard.Parabolics.borel (Triality.Standard.binaryParameters m (by omega))
  | ree n _ => exact ReeF4.Parabolics.borel n

/-- Each concrete positive subgroup is an ambient Sylow subgroup. -/
theorem exists_sylow {m : ℕ} (M : StandardModel m) :
    ∃ Q : Sylow 2 M.Carrier, (Q : Subgroup M.Carrier) = M.U := by
  cases M with
  | linearTwo F hm hF => exact ⟨Linear.projectiveSylow F, Linear.projectiveSylow_coe F⟩
  | unitaryThree F J hJ hm hF hconj =>
    obtain ⟨_, _, S, hS, _⟩ := Unitary.standard_su_borel_data J _ (by omega) hF hconj hJ
    refine ⟨S.mapSurjective (suProjection_surjective J), ?_⟩
    change (S : Subgroup J.specialSubgroup).map (suProjection J) = _
    rw [hS]
    exact Unitary.suRoot_map_projection J hJ
  | suzuki n hn => exact suzukiRootSubgroup_isSylow n (by omega)
  | linearThree F hm hF =>
    exact ⟨Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF, rfl⟩
  | symplecticFour F hm hF =>
    exact ⟨Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega), rfl⟩
  | g2 F hm hF => exact ⟨Atlas.G2.LieParabolicSetup.sylow, rfl⟩
  | triality n hn => exact ⟨Triality.Standard.Parabolics.unipotentSylow _ rfl, rfl⟩
  | ree n hn => exact ⟨ReeF4.Parabolics.ThreeSylowContainment.positiveSylow n,
      ReeF4.Parabolics.ThreeSylowContainment.positiveSylow_coe n⟩

/-- The concrete root normalizer is the concrete Borel in every family. -/
theorem normalizer_U {m : ℕ} (M : StandardModel m) : normalizer (M.U : Set M.Carrier) = M.B := by
  cases M with
  | linearTwo F hm hF =>
    have h := Linear.projectiveSylow_normalizer F
    change normalizer ((Linear.projectiveSylow F : Subgroup (BenderSuzuki.Converse.PSL2 F)) :
      Set (BenderSuzuki.Converse.PSL2 F)) = _ at h
    rw [Linear.projectiveSylow_coe] at h
    exact h
  | unitaryThree F J hJ hm hF hconj =>
    obtain ⟨_, _, _, _, _, _, hsup, hN, _⟩ :=
      Unitary.standard_projective_matrix_borel J _ (by omega) hF hconj hJ
    exact hN.trans hsup.symm
  | suzuki n hn => exact suzukiRootSubgroup_normalizer n (by omega)
  | linearThree F hm hF => exact Matrix.PSL3.LinearThree.normalizer_unipotent F (by omega) hF
  | symplecticFour F hm hF => exact Theory.SpecificGroups.SymplecticFour.borel_eq_normalizer_unipotent.symm
  | g2 F hm hF => exact Atlas.G2.SylowNormalizer.normalizer_unipotent
  | triality n hn => exact Triality.Standard.ConcreteBruhat.normalizer_unipotent_eq_borel _ rfl
  | ree n hn => exact ReeF4.Parabolics.unipotent_normalizer_eq_borel n

end StandardModel

/-- The complete large-field list admits one of the concrete standard
presentations. The unitary basis change and both central-quotient comparisons
are actual group equivalences. -/
theorem exists_standardModel {D : Type*} [Group D] {m : ℕ}
    (hmodel : InitialSieve.BinaryModelAt D m) (hm : 1 < m) :
    ∃ M : StandardModel m, Nonempty (D ≃* M.Carrier) := by
  cases hmodel with
  | linear_two n hn iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact ⟨.linearTwo F hm hF, ⟨e⟩⟩
  | unitary_three n hn iso =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := iso
    obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J m (by omega) hF hconj
    exact ⟨.unitaryThree F (Unitary.FormTransport.standardForm J) rfl hm hF hconj,
      ⟨e.trans (Unitary.FormTransport.projectiveEquiv J C hC)⟩⟩
  | suzuki n hn iso => exact ⟨.suzuki n hn, iso⟩
  | linear_three n hn iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact ⟨.linearThree F hm hF, ⟨e⟩⟩
  | symplectic n hn iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact ⟨.symplecticFour F hm hF, ⟨e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm⟩⟩
  | g2 n hn iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact ⟨.g2 F hm hF, ⟨e⟩⟩
  | triality n hn iso =>
    obtain ⟨P, hP, ⟨e⟩⟩ := iso
    rw [P.eq_binaryParameters_of_q_eq m (by omega) hP] at e
    exact ⟨.triality m hm, ⟨e⟩⟩
  | ree n hn iso =>
    obtain ⟨d, ⟨e⟩⟩ := iso
    exact ⟨.ree n hn, ⟨e.trans d.modelEquiv⟩⟩
  | symplectic_derived _ => omega
  | g2_derived _ => omega
  | tits _ => omega
  | binary_linear _ _ _ => omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.Catalogue
