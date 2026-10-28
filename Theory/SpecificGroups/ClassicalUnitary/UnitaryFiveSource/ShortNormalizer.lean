module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortSpace
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortNormalizer
public import Theory.GroupTheory.EmbeddedCenterMap
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Intrinsic short-root geometry in the unitary-five residual

The central Hermitian parameters are exactly the embedded center of the
canonical plane two-core. Their commutators with the marked short-root
centralizer generate the orthogonal three-space: every action difference
is symmetric, and one diagonal Levi commutator yields its long-root
normal generator. The full short-root line is the central part of this
space. These intrinsic descriptions allow transport under every ambient
normalizer preserving the residual and the selected short root.

The commutator uses Z(O₂(L)), since the unitary-five plane core itself is
nonabelian. Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
refs/quasithin.pdf.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneRadical UnitaryFourShortRoot
open scoped commutatorElement

@[expose] public noncomputable section
namespace Theory.SpecificGroups.UnitaryFive.ShortSpace

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1)
local notation "σ" => J.conj
local notation "K" => FixedBy.subfield F σ
local notation "H" => hermitianMatrices F σ
local notation "P" => PlaneCore.PlaneSemidirect J

omit [Finite F] in
theorem adaptedParameter_range : (adaptedParameter J c hc).range =
    center (PlaneCore.Parameters J) := by
  apply le_antisymm
  · rintro _ ⟨X,rfl⟩
    exact adaptedParameter_central J c hc X
  · intro u hu
    let v := PlaneCore.Parameters.planeAction (basis J c hc)⁻¹ u
    have hvC : v ∈ center (PlaneCore.Parameters J) :=
      MulEquivClass.apply_mem_center (PlaneCore.Parameters.planeAction (basis J c hc)⁻¹) hu
    have hv0 : v.x = 0 :=
      (PlaneCore.Parameters.mem_center_iff_x_eq_zero J c hc v).mp hvC
    let X : H := ⟨v.z, by
      change adjoint σ v.z = v.z
      ext i j
      change σ (v.z j i) = v.z i j
      have hh := v.relation i j
      rw [hv0] at hh
      simp only [Pi.zero_apply, zero_mul] at hh
      exact add_left_cancel (hh.trans (CharTwo.add_self_eq_zero _).symm)⟩
    have hp : parameter J (Multiplicative.ofAdd X) = v := by
      apply PlaneCore.Parameters.ext
      · simp [parameter,X,hv0]
      · rfl
    refine ⟨Multiplicative.ofAdd X, ?_⟩
    change PlaneCore.Parameters.planeAction (basis J c hc)
      (parameter J (Multiplicative.ofAdd X)) = u
    rw [hp]
    exact (PlaneCore.Parameters.planeAction (basis J c hc)).apply_symm_apply u

omit [Finite F] in
theorem radical_range_eq_centerParamsImage : (radical J c hc).range =
    (center (PlaneCore.Parameters J)).map
      (SemidirectProduct.inl : PlaneCore.Parameters J →* P) := by
  ext p
  constructor
  · rintro ⟨X,rfl⟩
    have h := adaptedParameter_range J c hc
    have hx : adaptedParameter J c hc X ∈ center (PlaneCore.Parameters J) :=
      (le_of_eq h) ⟨X,rfl⟩
    exact ⟨adaptedParameter J c hc X,hx,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    rw [←adaptedParameter_range J c hc] at hu
    obtain ⟨X,hX⟩ := Set.mem_range.mp hu
    refine ⟨X, ?_⟩
    change SemidirectProduct.inl (adaptedParameter J c hc X) = SemidirectProduct.inl u
    rw [hX]

theorem embeddedCoreCenter_eq_radical_range :
    (center (pCore 2 P)).map (pCore 2 P).subtype = (radical J c hc).range := by
  let i : PlaneCore.Parameters J →* P := SemidirectProduct.inl
  have himage : (⊤ : Subgroup (PlaneCore.Parameters J)).map i = pCore 2 P := by
    rw [←i.range_eq_map, PlaneCore.semidirect_pCore]
  have h := Subgroup.map_embeddedCenter
    (R := (⊤ : Subgroup (PlaneCore.Parameters J)))
    (f := (SemidirectProduct.inl : PlaneCore.Parameters J →* P))
    SemidirectProduct.inl_injective
  have hcenter : (center (⊤ : Subgroup (PlaneCore.Parameters J))).map
      (⊤ : Subgroup (PlaneCore.Parameters J)).subtype = center (PlaneCore.Parameters J) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      apply mem_center_iff.mpr
      intro z
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨z, trivial⟩)
    · intro hy
      refine ⟨⟨y,trivial⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro z
      apply Subtype.ext
      exact mem_center_iff.mp hy z.val
  have hleft := congrArg (Subgroup.map i) hcenter
  rw [himage,hleft] at h
  calc
    (center (pCore 2 P)).map (pCore 2 P).subtype =
        (center (PlaneCore.Parameters J)).map i := h.symm
    _ = (radical J c hc).range := (radical_range_eq_centerParamsImage J c hc).symm

def centerCore : Subgroup (centralizer J) := (intoCentralizer J c hc).range

omit [Finite F] in
theorem centerCore_normal : (centerCore J c hc).Normal := by
  constructor
  rintro x ⟨X, rfl⟩ a
  refine ⟨Multiplicative.ofAdd (hermitianCongruence F σ J.conj_involutive
    (projection J c hc a.val) X.toAdd), ?_⟩
  apply Subtype.ext
  change radical J c hc _ = a.val * radical J c hc X * a.val⁻¹
  rw [←radical_conjugation J c hc a.val X]

theorem centralizer_commutator_eq_space (hK : 2 < Nat.card K) :
    ⁅(⊤ : Subgroup (centralizer J)), centerCore J c hc⁆ = space J c hc := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha b hb
    obtain ⟨X, rfl⟩ := hb
    have hA : projection J c hc a.val ∈ fixedSL F σ :=
      (mem_centralizer J c hc a.val).mp a.property
    have hDelta := SourceNormalizer.FourShortRoot.congruence_difference_fixed
      F σ J.conj_involutive _ hA X.toAdd
    refine ⟨Multiplicative.ofAdd
      (hermitianCongruence F σ J.conj_involutive (projection J c hc a.val) X.toAdd - X.toAdd),
      hDelta, ?_⟩
    apply Subtype.ext
    change radical J c hc _ = a.val * radical J c hc X * a.val⁻¹ * (radical J c hc X)⁻¹
    rw [radical_conjugation]
    simp [div_eq_mul_inv]
  · have hz : longMark J c hc ∈ ⁅(⊤ : Subgroup (centralizer J)), centerCore J c hc⁆ := by
      obtain ⟨r,hr0,hr1⟩ := ENat.exists_ne_ne_of_three_le
        (α := K) (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (by omega : 3 ≤ Nat.card K)) 0 1
      have hrF : (r:F) ≠ 0 := fun he => hr0 (Subtype.ext he)
      have hr2 : r^2 - 1 ≠ 0 := by
        intro he
        rcases sq_eq_one_iff.mp (sub_eq_zero.mp he) with he | he
        · exact hr1 he
        · exact hr1 (by simpa only [CharTwo.neg_eq] using he)
      have hrf : σ (r:F) = r := r.property
      let b : K := (r^2 - 1)⁻¹
      let A : SpecialLinearGroup (Fin 2) F :=
        ⟨!![(r:F),0;0,(r:F)⁻¹],by simp [det_fin_two,hrF]⟩
      have hA : A ∈ fixedSL F σ := by
        rw [mem_fixedSL]
        intro i j
        fin_cases i <;> fin_cases j <;> simp [A,hrf]
      let X := SourceNormalizer.FourShortRoot.symmetric F σ b 0 0
      have he : hermitianCongruence F σ J.conj_involutive A X - X =
          longParameter F σ := by
        have hb : ((r:F)^2 - 1) * (b:F) = 1 :=
          congrArg Subtype.val (mul_inv_cancel₀ hr2)
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianCongruence,A,X,SourceNormalizer.FourShortRoot.symmetric,
            fixedHermitianEquiv,longParameter,adjoint,Matrix.vecMul,dotProduct,
            Fin.sum_univ_two,hrf]
        linear_combination hb
      have hh := commutator_mem_commutator
        (H₁ := (⊤ : Subgroup (centralizer J))) (H₂ := centerCore J c hc)
        (mem_top (levi J c hc ⟨A,hA⟩)) (show intoCentralizer J c hc
          (Multiplicative.ofAdd X) ∈ centerCore J c hc from ⟨_,rfl⟩)
      rw [commutatorElement_def,levi_conjugation,←map_inv,←map_mul] at hh
      rw [←ofAdd_neg,←ofAdd_add,←sub_eq_add_neg] at hh
      simp only [toAdd_ofAdd,he] at hh
      exact hh
    let _ := centerCore_normal J c hc
    rw [←long_normalClosure]
    apply normalClosure_le_normal
    rintro x rfl
    exact hz

theorem space_map_eq_commutator (hK : 2 < Nat.card K) :
    (space J c hc).map (centralizer J).subtype =
      ⁅(center (pCore 2 P)).map (pCore 2 P).subtype, centralizer J⁆ := by
  rw [←centralizer_commutator_eq_space J c hc hK, map_commutator,
    ←MonoidHom.range_eq_map, range_subtype, centerCore, MonoidHom.map_range,
    embeddedCoreCenter_eq_radical_range, commutator_comm]
  rfl

omit [Finite F] in
theorem line_eq_space_inf_center :
    line J c hc = space J c hc ⊓ center (centralizer J) := by
  apply le_antisymm
  · exact le_inf (line_le_space J c hc) (line_le_center J c hc)
  · intro x hx
    apply (fixed_primeTo J c hc).le
    exact ⟨hx.1,center_le_centralizer _ hx.2⟩

omit [Finite F] in
theorem line_map_eq_space_inf_centralizer :
    (line J c hc).map (centralizer J).subtype =
      (space J c hc).map (centralizer J).subtype ⊓
        Subgroup.centralizer (centralizer J : Set P) := by
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨mem_map_of_mem _ (line_le_space J c hc ha),?_⟩
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp (line_le_center J c hc ha) ⟨b,hb⟩)
  · rintro x ⟨⟨a,ha,rfl⟩,hx⟩
    refine ⟨a,(line_eq_space_inf_center J c hc).ge ⟨ha,?_⟩,rfl⟩
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (hx b.val b.property)

end Theory.SpecificGroups.UnitaryFive.ShortSpace
end
