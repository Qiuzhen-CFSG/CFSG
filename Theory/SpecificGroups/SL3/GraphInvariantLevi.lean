module
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
/-!
# Graph-invariant overgroups of the degree-three Levi

The centralizer of diag(-1,-1,1) is contained in two complementary
parabolics, so it is not intrinsically maximal. It is, however, maximal
among proper subgroups stable under inverse transpose. An off-block
matrix, normalized by Levi root operations, yields a nonzero opposite
root element. Its transpose and the Levi then generate all of SL₃.

The argument works over every field of characteristic different from two,
including the prime three. It supplies the linear geometry in
Aschbacher–Smith E.2.2(2d), printed pp.215–216. Elementary generation uses
the attributed ATLAS port; see the imported module and LICENSES/ATLAS.txt.
-/
public section
open Matrix Subgroup
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.OuterSolvable
namespace Matrix.SL3.LeviGraph
variable (F : Type*) [Field F]
local notation "e01" => SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide)
local notation "e10" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide)
local notation "e12" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide)
local notation "e21" => SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide)

private theorem conj_root_val (g : SL(3,F)) (a : F) (i j : Fin 3) :
    (g * e01 a * g⁻¹).val i j = (1 : Matrix (Fin 3) (Fin 3) F) i j +
      g.val i 0 * a * g⁻¹.val 1 j := by
  have hi : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  change ((g.val * (1 + single 0 1 a)) * g⁻¹.val : Matrix (Fin 3) (Fin 3) F) i j = _
  rw [mul_add, mul_one, add_mul, hi]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem levi_root (h2 : (2:F)≠0) (a : F) :
    e01 a ∈ centralizer ({standardInvolution F}:Set SL(3,F)) ∧
    e10 a ∈ centralizer ({standardInvolution F}:Set SL(3,F)) := by
  constructor <;> rw [mem_standardInvolution_centralizer_iff F h2] <;>
    simp [SpecialLinearGroup.transvection_coe]

private theorem conjugated_root_row (g : SL(3,F)) (hg : g.val 1 0=0) (a : F) :
    (g * e01 a * g⁻¹).val 1 0=0 ∧
    (g * e01 a * g⁻¹).val 1 1=1 ∧
    (g * e01 a * g⁻¹).val 1 2=0 := by
  simp [conj_root_val,hg]

private theorem row_root_identity (x : SL(3,F))
    (h10 : x.val 1 0=0) (h11 : x.val 1 1=1) (h12 : x.val 1 2=0) :
    x * e01 (1:F) = e01 (x.val 0 0) * e21 (x.val 2 0) * x := by
  apply Subtype.ext
  change x.val * (1+single 0 1 1) =
    (1+single 0 1 (x.val 0 0)) * (1+single 2 1 (x.val 2 0)) * x.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,h10,h11,h12]
  all_goals ring

private theorem lower_root_of_column (h2 : (2:F)≠0)
    (H : Subgroup SL(3,F))
    (hC : centralizer ({standardInvolution F}:Set SL(3,F)) ≤ H)
    (g : SL(3,F)) (hg : g∈H) (h10 : g.val 1 0=0) (h20 : g.val 2 0≠0) :
    ∃a:F,a≠0 ∧ e21 a∈H := by
  let x := g * e01 (1:F) * g⁻¹
  have hx : x∈H := H.mul_mem (H.mul_mem hg (hC (levi_root F h2 1).1)) (H.inv_mem hg)
  have hr := conjugated_root_row F g h10 1
  by_cases hv : g⁻¹.val 1 0=0
  · have hrel : g⁻¹.val 1 2 * g.val 2 0=0 := by
      have hi := congrArg (fun y : SL(3,F) => y.val 1 0) (inv_mul_cancel g)
      change (g⁻¹.val * g.val : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 at hi
      simpa only [Matrix.mul_apply,Fin.sum_univ_three,h10,hv,zero_mul,mul_zero,zero_add,add_zero] using hi
    have hv2 : g⁻¹.val 1 2=0 := (mul_eq_zero.mp hrel).resolve_right h20
    have hv1 : g⁻¹.val 1 1≠0 := by
      intro hv1
      have hi := congrArg (fun y : SL(3,F) => y.val 1 1) (inv_mul_cancel g)
      change (g⁻¹.val * g.val : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 at hi
      simp only [Matrix.mul_apply,Fin.sum_univ_three,hv,hv1,hv2,zero_mul,zero_add] at hi
      exact zero_ne_one hi
    have he : x = e01 (g.val 0 0*g⁻¹.val 1 1) * e21 (g.val 2 0*g⁻¹.val 1 1) := by
      apply Subtype.ext
      ext i j
      change (g*e01 (1:F)*g⁻¹).val i j = _
      rw [conj_root_val]
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply,Fin.sum_univ_three,h10,hv,hv2]
    refine ⟨_,mul_ne_zero h20 hv1,?_⟩
    rw [he] at hx
    exact (H.mul_mem_cancel_left (hC (levi_root F h2 _).1)).mp hx
  · refine ⟨x.val 2 0,?_,?_⟩
    · simpa [x,conj_root_val] using mul_ne_zero h20 hv
    · have he := row_root_identity F x hr.1 hr.2.1 hr.2.2
      have hh := H.mul_mem hx (hC (levi_root F h2 1).1)
      rw [he] at hh
      exact (H.mul_mem_cancel_left (hC (levi_root F h2 _).1)).mp
        ((H.mul_mem_cancel_right hx).mp hh)

private theorem graph_root {i j : Fin 3} (hij : i≠j) (a:F) :
    graphSL F (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm (-a) := by
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a))⁻¹ = _
  have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transpose,SpecialLinearGroup.transvection_coe,
      Matrix.transpose_add,Matrix.transpose_single]
  rw [h,SpecialLinearGroup.transvection_inv]

private theorem eq_top_of_lower_root (h2:(2:F)≠0) (H:Subgroup SL(3,F))
    (hC:centralizer ({standardInvolution F}:Set SL(3,F))≤H)
    (hgraph:∀g∈H,graphSL F g∈H)
    (a:F) (ha:a≠0) (haH:e21 a∈H) : H=⊤ := by
  have h12 : e12 (-a)∈H := by simpa only [graph_root] using hgraph _ haH
  have h02 (b:F) : SpecialLinearGroup.transvection (show (0:Fin 3)≠2 by decide) b∈H := by
    rw [← div_mul_cancel₀ b (neg_ne_zero.mpr ha),
      ← Atlas.elementary_commutator (show (0:Fin 3)≠2 by decide)
        (show (0:Fin 3)≠1 by decide) (show (1:Fin 3)≠2 by decide)]
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hC (levi_root F h2 _).1) h12)
      (H.inv_mem (hC (levi_root F h2 _).1))) (H.inv_mem h12)
  have h20 (b:F) : SpecialLinearGroup.transvection (show (2:Fin 3)≠0 by decide) b∈H := by
    simpa only [graph_root,neg_neg] using hgraph _ (h02 (-b))
  have h12' (b:F) : e12 b∈H := by
    rw [← mul_one b,← Atlas.elementary_commutator (show (1:Fin 3)≠2 by decide)
      (show (1:Fin 3)≠0 by decide) (show (0:Fin 3)≠2 by decide),commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hC (levi_root F h2 b).2) (h02 1))
      (H.inv_mem (hC (levi_root F h2 b).2))) (H.inv_mem (h02 1))
  have h21 (b:F) : e21 b∈H := by
    simpa only [graph_root,neg_neg] using hgraph _ (h12' (-b))
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g=>g∈H) _ (fun _ _=>H.mul_mem) g
  intro i j hij b
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hC (levi_root F h2 b).1
  · exact h02 b
  · exact hC (levi_root F h2 b).2
  · exact (hij rfl).elim
  · exact h12' b
  · exact h20 b
  · exact h21 b
  · exact (hij rfl).elim

private theorem lower_root_of_nonzero (h2:(2:F)≠0) (H:Subgroup SL(3,F))
    (hC:centralizer ({standardInvolution F}:Set SL(3,F))≤H)
    (g:SL(3,F)) (hg:g∈H) (h20:g.val 2 0≠0) :
    ∃a:F,a≠0 ∧ e21 a∈H := by
  by_cases h10:g.val 1 0=0
  · exact lower_root_of_column F h2 H hC g hg h10 h20
  have first (g:SL(3,F)) (hg:g∈H) (h00:g.val 0 0≠0) (h20:g.val 2 0≠0) :
      ∃a:F,a≠0 ∧ e21 a∈H := by
    let x := e10 (-g.val 1 0/g.val 0 0) * g
    have hx:x∈H := H.mul_mem (hC (levi_root F h2 _).2) hg
    apply lower_root_of_column F h2 H hC x hx
    · simp [x,SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply,Fin.sum_univ_three,h00]
    · simpa [x,SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply,Fin.sum_univ_three] using h20
  by_cases h00:g.val 0 0=0
  · apply first (e01 (1:F)*g) (H.mul_mem (hC (levi_root F h2 1).1) hg)
    · simpa [SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply,Fin.sum_univ_three,h00] using h10
    · simpa [SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply,Fin.sum_univ_three] using h20
  · exact first g hg h00 h20

/-- Every proper inverse-transpose-invariant overgroup of the standard Levi
is the Levi itself. The two containing parabolics are exchanged by the graph actor. -/
theorem eq_centralizer (h2:(2:F)≠0) (H:Subgroup SL(3,F))
    (hC:centralizer ({standardInvolution F}:Set SL(3,F))≤H)
    (hgraph:∀g∈H,graphSL F g∈H) (hH:H≠⊤) :
    H=centralizer ({standardInvolution F}:Set SL(3,F)) := by
  have h20 (g:SL(3,F)) (hg:g∈H) : g.val 2 0=0 := by
    by_contra h
    obtain ⟨a,ha,haH⟩ := lower_root_of_nonzero F h2 H hC g hg h
    exact hH (eq_top_of_lower_root F h2 H hC hgraph a ha haH)
  have h21 (g:SL(3,F)) (hg:g∈H) : g.val 2 1=0 := by
    have h := h20 (g*e10 (1:F)) (H.mul_mem hg (hC (levi_root F h2 1).2))
    simpa [SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply,Fin.sum_univ_three,h20 g hg] using h
  apply le_antisymm _ hC
  intro g hg
  rw [mem_standardInvolution_centralizer_iff F h2]
  have htrans : graphSL F g⁻¹ = SpecialLinearGroup.transpose g := by
    rw [map_inv]
    change ((SpecialLinearGroup.transpose g)⁻¹)⁻¹ = _
    exact inv_inv _
  have ht : SpecialLinearGroup.transpose g∈H := htrans ▸ hgraph _ (H.inv_mem hg)
  exact ⟨h20 _ ht,h21 _ ht,h20 g hg,h21 g hg⟩
end Matrix.SL3.LeviGraph
