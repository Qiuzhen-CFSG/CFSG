module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.RadicalGeometry.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.FixedComplements


/-!
# The literal first Cartan kernel

A Cartan element fixing a point of P outside R₁ has equal lower diagonal
entries in the aligned SL₃ quotient. In characteristic two, the square of
its action on the quotient by the flag point is scalar. Its commutators
with the actual L₁ therefore lie in O₂(L₁). Odd order then puts the
original element in the kernel of the normalizer action on L₁/O₂(L₁).

The proof transports through the original aligned quotient and its
intrinsic local cores. It keeps R₁ = O₂(L₁T) distinct from O₂(L₁).
The first scalar family uses this result to place its constructed actors
in the source subgroup X₁.

Source: Aschbacher--Smith, the proof of 11.3.9, printed p.775.
-/

open Subgroup Matrix
open Matrix.PSL3.LinearThree
open scoped MatrixGroups commutatorElement
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The action of the point stabilizer on the literal quotient by its point. -/
private def pointBlock : pointParabolicSL F →* Matrix (Fin 2) (Fin 2) F where
  toFun g := g.val.val.submatrix Fin.succ Fin.succ
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    obtain ⟨hg10,hg20⟩ := (mem_pointParabolicSL_iff F g).mp g.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two,hg10,hg20]

/-- Fixing a line-radical element outside the point radical forces equal quotient diagonal entries. -/
private theorem equal_diagonal_of_fixed_root (g u : SL(3,F))
    (hg : g ∈ borelSL F) (hu : u ∈ (lineLocalSL F).pCoreIn 2)
    (hu12 : u.val 1 2 ≠ 0) (hc : Commute g u) : g.val 1 1 = g.val 2 2 := by
  obtain ⟨h10,_,_⟩ := (mem_borelSL_iff F g).mp hg
  have hm := MarkedSections.RadicalGeometry.line_core_matrix u hu
  have he := congrArg (fun x : SL(3,F) => x.val 1 2) hc.eq
  change (g.val * u.val) 1 2 = (u.val * g.val) 1 2 at he
  rw [hm] at he
  have he' : g.val 1 1 * u.val 1 2 = g.val 2 2 * u.val 1 2 := by
    simpa [Matrix.mul_apply,Fin.sum_univ_three,h10,mul_comm,add_comm] using he
  exact mul_right_cancel₀ hu12 he'

/-- In characteristic two, the square of this quotient block is scalar. -/
private theorem pointBlock_sq_scalar (g : pointParabolicSL F)
    (h21 : g.val.val 2 1 = 0) (hd : g.val.val 1 1 = g.val.val 2 2) :
    pointBlock (g^2) = g.val.val 1 1 ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [map_pow,pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointBlock,Matrix.mul_apply,Fin.sum_univ_two,h21,←hd,pow_two,mul_comm,
      CharTwo.add_self_eq_zero]
  rw [mul_comm (g.val.val 1 2), CharTwo.add_self_eq_zero]

private theorem odd_mem_of_sq_mem {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (x : G) (ho : Odd (orderOf x)) (h : x^2 ∈ H) : x ∈ H := by
  obtain ⟨k,hk⟩ := ho
  have hp := pow_orderOf_eq_one x
  rw [hk,pow_add,pow_one] at hp
  have he : (x^2)^k = x⁻¹ := by
    rw [←pow_mul]
    exact eq_inv_of_mul_eq_one_left hp
  have hh := H.pow_mem h k
  rw [he] at hh
  simpa using H.inv_mem hh
omit [CharP F 2] in
private theorem pointBlock_commutator (g a : pointParabolicSL F) (t : F)
    (hg : pointBlock g = t • (1 : Matrix (Fin 2) (Fin 2) F)) :
    pointBlock ⁅g,a⁆ = 1 := by
  have hc : pointBlock g * pointBlock a = pointBlock a * pointBlock g := by
    rw [hg]
    simp only [Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one]
  calc
    pointBlock ⁅g,a⁆ = pointBlock g * pointBlock a * pointBlock g⁻¹ * pointBlock a⁻¹ := by
      simp only [commutatorElement_def,map_mul]
    _ = pointBlock a * (pointBlock g * pointBlock g⁻¹) * pointBlock a⁻¹ := by rw [hc]; simp only [mul_assoc]
    _ = 1 := by rw [←map_mul,mul_inv_cancel,map_one,mul_one,←map_mul,mul_inv_cancel,map_one]

private theorem point_core_of_block_one (a : pointLocalSL F)
    (ha : pointBlock (F := F) ⟨a.val,(mem_pointParabolicSL_iff F a).mpr
      ((mem_pointLocalSL_iff F a).mp a.property).2⟩ = 1) :
    a.val ∈ (pointLocalSL F).pCoreIn 2 := by
  refine ⟨a,?_,rfl⟩
  rw [pointLocalSL_twoCore_eq]
  apply (mem_pointRadicalSL_iff F a).mpr
  exact ⟨congrArg (fun b => b 0 0) ha,congrArg (fun b => b 0 1) ha,
    congrArg (fun b => b 1 0) ha,congrArg (fun b => b 1 1) ha⟩

open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open MarkedSections.RadicalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
private theorem core_kernel_of_commutators {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (x : G) (hx : x ∈ normalizer (A : Set G))
    (hc : ∀ a : A, ⁅x,(a : G)⁆ ∈ A.pCoreIn 2) :
    x ∈ coreQuotientCentralizer A := by
  let xn : normalizer (A : Set G) := ⟨x,hx⟩
  refine ⟨xn,?_,rfl⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) z
  rw [coreQuotientAction_apply_mk]
  change QuotientGroup.mk' (pCore 2 A) (A.normalizerMonoidHom xn a) =
    QuotientGroup.mk' (pCore 2 A) a
  apply (mul_inv_eq_one).mp
  rw [←map_inv,←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (mem_map_iff_mem A.subtype_injective).mp (hc a)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {X P W : Subgroup G}

private theorem cartan_normalizes_local (hX : IsCartan T L X) (i : Fin 2) :
    X ≤ normalizer (f.Li i : Set G) := by
  have hXf : X ≤ normalizer (f.Vi i.castSucc : Set G) := by
    rw [MarkedSections.flag_eq D S m f]
    exact SL3.cartan_normalizes D S m hX i.castSucc
  exact (((le_inf ((hX.1.trans inf_le_left).trans L.le_normalizer)
    (hXf.trans (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ (solvableResidual _)))

include f in
private theorem cartan_image_borel (hX : IsCartan T L X) (x : X) :
    SL3.PlaneAction.alignedQuotient D S m (inclusion (hX.1.trans inf_le_left) x) ∈
      borelSL S.field.Carrier := by
  let l := inclusion (hX.1.trans inf_le_left) x
  have hi (i : Fin 3) (v : V) (hv : (v : G) ∈ f.Vi i) :
      (SL3.PlaneAction.alignedQuotient D S m l).val.mulVec
        (alignedVectors D S m (Additive.ofMul v)) ∈ SL3.Model.flag i := by
    rw [←alignedVectors_conjugation]
    apply (mem_flag_aligned D S m f i _).mp
    have hn : (x : G) ∈ normalizer (f.Vi i : Set G) := by
      rw [MarkedSections.flag_eq D S m f]
      exact SL3.cartan_normalizes D S m hX i x.property
    exact (mem_normalizer_iff.mp hn _).mp hv
  let v₀ := (alignedVectors D S m).symm ![1,0,0]
  let v₁ := (alignedVectors D S m).symm ![0,1,0]
  have hv₀ : alignedVectors D S m v₀ = ![1,0,0] := (alignedVectors D S m).apply_symm_apply _
  have hv₁ : alignedVectors D S m v₁ = ![0,1,0] := (alignedVectors D S m).apply_symm_apply _
  have h₀ := hi 0 v₀.toMul ((mem_flag_aligned D S m f 0 v₀.toMul).mpr (by change alignedVectors D S m v₀ ∈ SL3.Model.flag 0; rw [hv₀]; exact ⟨rfl,rfl⟩))
  have h₁ := hi 1 v₁.toMul ((mem_flag_aligned D S m f 1 v₁.toMul).mpr (by change alignedVectors D S m v₁ ∈ SL3.Model.flag 1; rw [hv₁]; rfl))
  simp only [ofMul_toMul,hv₀] at h₀
  simp only [ofMul_toMul,hv₁] at h₁
  change (_ *ᵥ _) 1 = 0 ∧ (_ *ᵥ _) 2 = 0 at h₀
  change (_ *ᵥ _) 2 = 0 at h₁
  apply (mem_borelSL_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · simpa [mulVec,dotProduct,Fin.sum_univ_three] using h₀.1
  · simpa [mulVec,dotProduct,Fin.sum_univ_three] using h₀.2
  · simpa [mulVec,dotProduct,Fin.sum_univ_three] using h₁

private theorem local_core_of_image (a : L) (ha : (a : G) ∈ f.Li 0)
    (hq : SL3.PlaneAction.alignedQuotient D S m a ∈
      (pointLocalSL S.field.Carrier).pCoreIn 2) : (a : G) ∈ (f.Li 0).pCoreIn 2 := by
  let q := SL3.PlaneAction.alignedQuotient D S m
  let A := (f.Li 0).subgroupOf L
  have hAL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hi : A.map q = pointLocalSL S.field.Carrier := by
    change ((f.Li 0).subgroupOf L).map (SL3.PlaneAction.alignedQuotient D S m) = _
    rw [MarkedSections.flag_eq D S m f,SL3.PlaneAction.local_image]
    rfl
  have hk : IsPGroup 2 q.ker := by
    rw [SL3.PlaneAction.alignedQuotient_ker]
    exact pCore_isPGroup
  have hh := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q A hk
  have hm : a ∈ A.pCoreIn 2 := by
    rw [←hh,hi]
    exact ⟨ha,hq⟩
  rw [pCoreIn_subgroupOf 2 _ L hAL] at hm
  exact hm

/-- A Cartan element fixing a nonradical element of P belongs to the literal
normalizer-action kernel on L₁/O₂(L₁). -/
theorem first_kernel_of_fixed_element (hX : IsCartan T L X)
    (hP : P = (f.Li 1).pCoreIn 2) (hTL : (T : Subgroup G) ≤ L)
    (x : X) (w : P) (hw : (w : G) ∉ f.Ri 0) (hc : Commute (x : G) (w : G)) :
    (x : G) ∈ coreQuotientCentralizer (f.Li 0) := by
  let q := SL3.PlaneAction.alignedQuotient D S m
  have hXL := hX.1.trans inf_le_left
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((localResidual_le _).trans inf_le_left)
  let xL := inclusion hXL x
  let wL := inclusion hPL w
  have hxB := cartan_image_borel D S m f hX x
  obtain ⟨hx10,hx20,hx21⟩ := (mem_borelSL_iff _ _).mp hxB
  let g : pointParabolicSL S.field.Carrier :=
    ⟨q xL,(mem_pointParabolicSL_iff _ _).mpr ⟨hx10,hx20⟩⟩
  have hwq : q wL ∈ (lineLocalSL S.field.Carrier).pCoreIn 2 := by
    rw [←common_core_image D S m f P hP]
    exact mem_map_of_mem q w.property
  have hw12 : (q wL).val 1 2 ≠ 0 := by
    intro hz
    apply hw
    apply (mem_radical_iff D S m f hTL 0 wL).mpr
    exact (line_core_mem_point_core_iff _ hwq).mpr hz
  have hd : (q xL).val 1 1 = (q xL).val 2 2 :=
    equal_diagonal_of_fixed_root (q xL) (q wL) hxB hwq hw12
      ((show Commute xL wL from Subtype.ext hc).map q)
  have hg := pointBlock_sq_scalar g hx21 hd
  have hxn := cartan_normalizes_local D S m f hX 0
  have hsq : (x : G)^2 ∈ coreQuotientCentralizer (f.Li 0) := by
    have hnorm : (x : G)^2 ∈ normalizer (f.Li 0 : Set G) :=
      (normalizer (f.Li 0 : Set G)).pow_mem (hxn x.property) 2
    apply core_kernel_of_commutators (f.Li 0) ((x : G)^2) hnorm
    intro a
    let aL : L := ⟨a,(localResidual_le _ a.property).1⟩
    let bL : L := ⁅xL^2,aL⁆
    have hb : (bL : G) ∈ f.Li 0 :=
      (f.Li 0).mul_mem ((mem_normalizer_iff.mp hnorm _).mp a.property)
        ((f.Li 0).inv_mem a.property)
    have ha : q aL ∈ pointLocalSL S.field.Carrier := by
      have hh := mem_map_of_mem q (show aL ∈ ((f.Li 0).subgroupOf L) from a.property)
      rw [MarkedSections.flag_eq D S m f,SL3.PlaneAction.local_image] at hh
      exact hh
    let aq : pointParabolicSL S.field.Carrier := ⟨q aL,(mem_pointParabolicSL_iff _ _).mpr
      ((mem_pointLocalSL_iff _ _).mp ha).2⟩
    have hbq : q bL ∈ pointLocalSL S.field.Carrier := by
      have hh := mem_map_of_mem q (show bL ∈ ((f.Li 0).subgroupOf L) from hb)
      rw [MarkedSections.flag_eq D S m f,SL3.PlaneAction.local_image] at hh
      exact hh
    change (bL : G) ∈ (f.Li 0).pCoreIn 2
    apply local_core_of_image D S m f bL hb
    apply point_core_of_block_one ⟨q bL,hbq⟩
    have he : (⟨q bL,(mem_pointParabolicSL_iff _ _).mpr
        ((mem_pointLocalSL_iff _ _).mp hbq).2⟩ : pointParabolicSL S.field.Carrier) = ⁅g^2,aq⁆ := by
      apply Subtype.ext
      change q ⁅xL^2,aL⁆ = ⁅q xL ^ 2,q aL⁆
      rw [map_commutatorElement,map_pow]
    rw [he]
    exact pointBlock_commutator (g^2) aq _ hg
  apply odd_mem_of_sq_mem _ (x : G) _ hsq
  exact hX.odd.of_dvd_nat ((orderOf_map_dvd X.subtype x).trans (orderOf_dvd_natCard x))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
