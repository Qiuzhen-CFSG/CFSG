module

public import Theory.SpecificGroups.SU3.SylowFixedInvolutions
public import BenderSuzuki.SE.Borel
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.SpecificGroups.SU3.GraphFixedResidual

/-!
# Involution geometry in binary PSU₃

The upper Hermitian root group is a Sylow two-subgroup. An involution in
its coordinates has first coordinate zero, so it is a long-root element.
Sylow conjugacy gives this description for every involution. The regular
root action on isotropic points identifies its normalizer with a genuine
point stabilizer and puts the involution centralizer in that parabolic.

The outer-involution classification gives conjugacy to the actual graph
action. Its fixed-group equivalence and perfectness identify the embedded
two-residual with the full fixed subgroup and with PSL₂ of the fixed field.

Source: Aschbacher–Smith, 16.1.4(1),(6) and 16.1.6, printed pp.1171–1172;
Huppert II.10.12 for the natural action and root coordinates.
-/

@[expose] public section
open Subgroup BenderSuzuki.External
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryInvolutionTable
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- A nonidentity involution conjugate to the long root `I + b E₁₃`. -/
def IsLongRootInvolution (x : ProjectiveSpecialUnitaryMatrixGroup J) : Prop :=
  orderOf x = 2 ∧ ∃ (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (z : hermitianUnipotentCoord J), z.val.1 = 0 ∧ MulAut.conj g x = root J hJ z

/-- The standard rank-one parabolic, identified below as an isotropic-point stabilizer. -/
def rootParabolic : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  normalizer (rootGroup J hJ : Set _)

/-- The isotropic lines in the specified Hermitian space. -/
abbrev IsotropicPoint := {x : Projectivization E (Fin 3 → E) // x ∈
  {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0), x = Projectivization.mk E v hv ∧
    dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}

variable [Finite E]
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The parabolic is proper, as the opposite root is distinct. -/
theorem rootParabolic_ne_top {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    rootParabolic J hJ ≠ ⊤ := by
  intro h
  have hw : weyl J hJ ∈ normalizer (rootGroup J hJ : Set _) := by
    rw [← rootParabolic, h]
    trivial
  have he := mem_normalizer_iff_map_conj_eq.mp hw
  exact rootGroup_ne_oppositeRootGroup J hJ hq hcard hfixed
    (he.symm.trans (oppositeRootGroup_eq_map J hJ).symm)

/-- This is the actual projective matrix action, not an abstract Borel tag. -/
theorem rootParabolic_isotropic_stabilizer {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (IsotropicPoint J))
      (p : IsotropicPoint J),
      (∀ (g : ProjectiveSpecialUnitaryMatrixGroup J) (z : IsotropicPoint J)
        (M : J.specialSubgroup), Matrix.ProjGenLinGroup.mk M.val = g.val →
        (rho g z).val = (Matrix.GeneralLinearGroup.toLin M.val).toLinearEquiv • z.val) ∧
      rootParabolic J hJ = (MulAction.stabilizer (Equiv.Perm (IsotropicPoint J)) p).comap rho := by
  obtain ⟨_, rho, p, _, hnat, _, hroot, _⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, hRfix, _, hRnorm, _, _, _, hRcard, _, _, _, hreg,
    ⟨coord, hcoord⟩, _⟩ := hroot
  have hcoord_eq (w : hermitianUnipotentCoord J) : (coord w).val = root J hJ w := by
    obtain ⟨M, hM, heq⟩ := hcoord w
    have hM' : M = hermitianUnipotentGL J w := Units.ext hM
    apply Subtype.ext
    simpa only [hM', root, hermitianUnipotentPSU_val] using heq
  have hR : R = rootGroup J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨w, hw⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨w, (hcoord_eq w).symm.trans (congrArg Subtype.val hw)⟩
    · rintro r ⟨w, rfl⟩
      rw [← hcoord_eq w]
      exact (coord w).property
  have hne : R ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hRcard
    have := one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)
    omega
  change ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (IsotropicPoint J) at rho
  change IsotropicPoint J at p
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (IsotropicPoint J) :=
    MulAction.compHom _ rho
  refine ⟨rho, p, hnat, ?_⟩
  change normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
  rw [← hR]
  exact BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl
    R p hRfix hne hreg hRnorm

/-- Simplicity and perfectness are proved from the actual unitary parameters. -/
theorem center_eq_bot {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  have hq : 2 < 2 ^ n := by
    change 2 ^ 1 < 2 ^ n
    exact Nat.pow_lt_pow_right (by decide) (by omega : 1 < n)
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  let := huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  exact Subgroup.center_eq_bot_of_simple_perfect

/-- Every involution has a long-root representative, and its full centralizer
lies in the corresponding conjugate of the standard proper parabolic. -/
theorem involution_root_geometry [CharP E 2] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ∃ (g : ProjectiveSpecialUnitaryMatrixGroup J) (z : hermitianUnipotentCoord J),
      z.val.1 = 0 ∧ MulAut.conj g x = root J hJ z ∧
      centralizer ({x} : Set _) ≤ (rootParabolic J hJ).comap (MulAut.conj g).toMonoidHom ∧
      (rootParabolic J hJ).comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, hx, pow_one] using (dvd_refl 2))
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let P := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S P
  have hxg : MulAut.conj g x ∈ P := by
    rw [← hg]
    exact ⟨x, hS (mem_zpowers x), rfl⟩
  obtain ⟨z, hz⟩ := hxg
  have hz2 : z ^ 2 = 1 := root_injective J hJ (by
    rw [map_pow, hz, ← map_pow, hx2, map_one, map_one])
  refine ⟨g, z, (EvenSemilinear.square_eq_one_iff_first_zero J z).mp hz2,
    hz.symm, ?_, ?_⟩
  · intro y hy
    apply SylowFixedInvolutions.projective_centralizer_le_normalizer
      J hn hJ hcard hfixed P (MulAut.conj g x) ⟨z, hz⟩
      (by
        intro he
        have hx1 : x = 1 := (MulAut.conj g).injective (he.trans (map_one _).symm)
        simp only [hx1, orderOf_one] at hx
        omega)
    apply mem_centralizer_singleton_iff.mpr
    have hc := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp hy)
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hc
  · intro ht
    apply rootParabolic_ne_top J hJ (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed
    apply top_unique
    intro y _
    obtain ⟨w, rfl⟩ := (MulAut.conj g).surjective y
    exact show w ∈ (rootParabolic J hJ).comap (MulAut.conj g).toMonoidHom from ht ▸ mem_top w

/-- The concrete long-root predicate is satisfied by every binary PSU₃ involution. -/
theorem involution_isLongRoot [CharP E 2] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    IsLongRootInvolution J hJ x := by
  obtain ⟨g, z, hz, he, _, _⟩ := involution_root_geometry J hJ hn hcard hfixed x hx
  exact ⟨hx, g, z, hz, he⟩
end BenderSuzuki.MatrixGroups.HermitianForm.BinaryInvolutionTable

namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryInvolutionTable
open Subgroup
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The derived endpoint in the source table is the full fixed-field PSL₂
in the simple unitary range. -/
theorem fixedField_commutator_eq_top {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    commutator (PSL2MatrixGroup (FixedBy.subfield E J.conj)) = ⊤ := by
  let K := FixedBy.subfield E J.conj
  have hK : 4 ≤ Nat.card K := by
    change 4 ≤ Nat.card {x : E // J.conj x = x}
    rw [hfixed]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hu : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  let : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu⟩ := exists_ne (1 : Kˣ)
  exact SL2Simple.PSL_commutator_eq_top ⟨(u : K), u.ne_zero, fun hs =>
    hu (Units.val_eq_one.mp (CharTwo.sq_injective (by simpa using hs)))⟩

/-- Every non-inner involution is conjugate to the concrete graph action.
Its embedded two-residual is its full fixed subgroup and is PSL₂(2ⁿ)′.
In GLS Notation 16.1.3 this unitary action is called graph, not field. -/
theorem outer_involution_geometry {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ x, a = MulAut.conj x) :
    ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      MulAut.congr c (J.projectiveGraphAut hJ) = a ∧
      MulAut.embeddedFixedResidual 2 a = a.fixedSubgroup ∧
      Nonempty (MulAut.embeddedFixedResidual 2 a ≃*
        commutator (PSL2MatrixGroup (FixedBy.subfield E J.conj))) := by
  obtain ⟨c, hc⟩ := J.outer_involution_conjugate n hn hJ hcard hfixed
    (J.projectiveGraphAut_isEntrywiseConjugation hJ) a ha houter
  let d : (J.projectiveGraphAut hJ).fixedSubgroup ≃* a.fixedSubgroup :=
    (MulAut.fixedSubgroupCongr c (J.projectiveGraphAut hJ)).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hc))
  have hr : pResidual 2 a.fixedSubgroup = ⊤ := by
    rw [← map_pResidual 2 d, J.graph_fixed_twoResidual_eq_top hJ hn hfixed,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr d.surjective]
  have he : MulAut.embeddedFixedResidual 2 a = a.fixedSubgroup := by
    rw [MulAut.embeddedFixedResidual, hr, ← MonoidHom.range_eq_map, range_subtype]
  let e := d.symm.trans (J.projectiveGraphFixedEquiv hJ)
  exact ⟨c, hc, he, ⟨(MulEquiv.subgroupCongr he).trans (e.trans
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
      (fixedField_commutator_eq_top J hn hfixed).symm)))⟩⟩
end BenderSuzuki.MatrixGroups.HermitianForm.BinaryInvolutionTable
