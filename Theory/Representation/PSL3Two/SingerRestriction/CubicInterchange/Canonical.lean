module

public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace
public import Theory.Representation.PSL3Two.SingerRestriction.CubicInterchange.Action

/-!
# The two cubic fixed lines in canonical Singer coordinates

The actual Steinberg module is the trace-zero endomorphism space. A small
kernel-checked matrix certificate identifies the cubic fixed plane. Singer
transitivity excludes the sum of its two distinguished vectors from a moving
constituent. The displayed inner involution and the inner-times-graph outer
involution swap these vectors, with the action computed through steinbergAut
and the actual automorphism intertwiner autEquiv.

The complete scratch check took 21 seconds wall time and 4.0 GiB peak RSS,
including loading imports. No finite enumeration of subspaces is used.

Source: Aschbacher–Smith J.2.3(7), printed p.434 (PDF p.445),
combined manuscript of 1 March 2004.
-/

public section

open Matrix Representation Representation.BinaryOffender Subgroup
open scoped Matrix
namespace BinaryLinearThree.SingerRestriction.CubicInterchange
open Matrix.PSL3Two.OuterInvolutionSinger FiveSpace.Certificate
noncomputable section
local instance : AddCommGroup Steinberg := inferInstance
local instance : Module (ZMod 2) Steinberg := inferInstance

def matrix (v : Steinberg) : Mat := LinearMap.toMatrix' v.val
private lemma matrix_injective : Function.Injective matrix := by
  intro v w he
  exact Subtype.ext (LinearMap.toMatrix'.injective he)
lemma matrix_action (g : Group) (v : Steinberg) :
    matrix (S g v) = g.val * matrix v * (g⁻¹).val := by
  change LinearMap.toMatrix' (g.val.toLin' ∘ₗ v.val ∘ₗ (g⁻¹).val.toLin') = _
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', matrix, mul_assoc]
private lemma matrix_trace (v : Steinberg) : (matrix v).trace = 0 := by
  rw [matrix, ← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact v.property
private lemma matrix_add (v w : Steinberg) : matrix (v+w) = matrix v + matrix w :=
  map_add LinearMap.toMatrix' v.val w.val
private lemma matrix_zero : matrix 0 = 0 := map_zero LinearMap.toMatrix'

def inner : Group := ⟨!![0,0,1; 1,1,1; 1,0,0], by decide⟩
def outer : MulAut Group := MulAut.conj singer * AutomorphismAction.graph

def first : Steinberg := ⟨cubic.val.toLin', by
  change LinearMap.trace (ZMod 2) Vector cubic.val.toLin' = 0
  rw [Matrix.trace_toLin'_eq]
  decide⟩
def second : Steinberg := ⟨(cubicMatrix 2).toLin', by
  change LinearMap.trace (ZMod 2) Vector (cubicMatrix 2).toLin' = 0
  rw [Matrix.trace_toLin'_eq]
  decide⟩
lemma matrix_first : matrix first = cubic.val := LinearMap.toMatrix'_toLin' _
lemma matrix_second : matrix second = cubicMatrix 2 := LinearMap.toMatrix'_toLin' _

lemma outer_action (v : Steinberg) :
    matrix (AutomorphismAction.steinbergAut outer v) =
      singer.val * (matrix v).transpose * (singer⁻¹).val := by
  have hi : AutomorphismAction.steinbergAut (MulAut.conj singer) = S singer :=
    congrArg (fun ρ : Representation (ZMod 2) Group Steinberg => ρ singer)
      AutomorphismAction.steinbergAut_comp_conj
  rw [outer, map_mul, Module.End.mul_apply, hi,
    AutomorphismAction.steinbergAut_graph, matrix_action]
  have hm : matrix (AutomorphismAction.steinbergTranspose v) = (matrix v).transpose := by
    unfold matrix
    rw [AutomorphismAction.steinbergTranspose_apply, LinearMap.toMatrix'_toLin']
  exact congrArg (fun m : Mat => singer.val * m * (singer⁻¹).val) hm

lemma inner_sq : inner ^ 2 = 1 := by decide
lemma inner_ne_one : inner ≠ 1 := by decide
lemma inner_cubic : (MulAut.conj inner) cubic = cubic⁻¹ := by decide
lemma outer_singer : outer singer = singer⁻¹ := by decide
lemma outer_cubic : outer cubic = cubic := by decide
lemma outer_inner : outer inner = inner := by decide
lemma outer_sq : outer ^ 2 = 1 := by
  ext x : 1
  change singer * AutomorphismAction.graph (singer * AutomorphismAction.graph x * singer⁻¹) * singer⁻¹ = x
  simp only [map_mul, map_inv]
  have hr : AutomorphismAction.graph singer = singer⁻¹ := by decide
  have hg : AutomorphismAction.graph (AutomorphismAction.graph x) = x :=
    congrArg (fun a : MulAut Group => a x) AutomorphismAction.graph_sq
  rw [hr,hg]
  group
lemma outer_not_inner : outer ∉ MulAut.innerSubgroup Group := by
  rintro ⟨g,hg⟩
  apply AutomorphismAction.graph_not_inner
  refine ⟨singer⁻¹*g, ?_⟩
  rw [map_mul,map_inv]
  rw [hg]
  exact inv_mul_cancel_left _ _

lemma inner_first : S inner first = second := by
  apply matrix_injective
  rw [matrix_action,matrix_first,matrix_second]
  decide
lemma inner_second : S inner second = first := by
  apply matrix_injective
  rw [matrix_action,matrix_first,matrix_second]
  decide
lemma outer_first : AutomorphismAction.steinbergAut outer first = second := by
  apply matrix_injective
  rw [outer_action,matrix_first,matrix_second]
  decide
lemma outer_second : AutomorphismAction.steinbergAut outer second = first := by
  apply matrix_injective
  rw [outer_action,matrix_first,matrix_second]
  decide
lemma first_ne_second : first ≠ second := by
  intro h
  have := congrArg matrix h
  rw [matrix_first,matrix_second] at this
  exact (by decide : cubic.val ≠ cubicMatrix 2) this

set_option maxRecDepth 3000 in
private lemma fixed_certificate : ∀ v : Mat, v.trace = 0 → cubic.val * v = v * cubic.val →
    v = 0 ∨ v = cubic.val ∨ v = cubicMatrix 2 ∨ v = cubic.val + cubicMatrix 2 := by
  decide +kernel
private lemma sum_not_orbit : ∀ i : Fin 7,
    act i (cubic.val + cubicMatrix 2) ≠
      (cubic.val + cubicMatrix 2) + act 1 (cubic.val + cubicMatrix 2) := by
  decide +kernel

private lemma exists_power (g : Group) (hg : g ∈ zpowers singer) :
    ∃ i : Fin 7, power i = g := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ho : orderOf singer = 7 :=
    orderOf_eq_prime (by decide : singer ^ 7 = 1) (by decide : singer ≠ 1)
  have hr := (isOfFinOrder_of_finite singer).mem_zpowers_iff_mem_range_orderOf.mp hg
  rw [ho] at hr
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hr
  exact ⟨⟨i,Finset.mem_range.mp hi⟩,(power_eq ⟨i,Finset.mem_range.mp hi⟩).trans he⟩
private lemma act_matrix (i : Fin 7) (v : Steinberg) :
    act i (matrix v) = matrix (S (power i) v) := by
  rw [matrix_action,act,inverseMatrix_eq]
  rfl

lemma canonical_fixed_cases (M : Submodule (ZMod 2) Steinberg)
    (hM : ∀ h ∈ zpowers singer, ∀ v ∈ M, S h v ∈ M)
    (hd : fixedSpace S (zpowers singer) ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ zpowers singer, S h v = w)
    (v : Steinberg) (hv : v ∈ M) (hv0 : v ≠ 0)
    (hvD : v ∈ fixedSpace S (zpowers cubic)) : v = first ∨ v = second := by
  have hfix := (mem_fixedSpace_zpowers_iff S cubic v).mp hvD
  have hmat := congrArg matrix hfix
  rw [matrix_action] at hmat
  have hci : (cubic⁻¹).val * cubic.val = 1 := congrArg Subtype.val (inv_mul_cancel cubic)
  have hcomm : cubic.val * matrix v = matrix v * cubic.val := by
    calc
      cubic.val * matrix v = (cubic.val * matrix v * (cubic⁻¹).val) * cubic.val := by
        rw [mul_assoc (cubic.val * matrix v),hci,mul_one]
      _ = matrix v * cubic.val := congrArg (fun a => a * cubic.val) hmat
  rcases fixed_certificate (matrix v) (matrix_trace v) hcomm with hz | hf | hs | hsum
  · exact False.elim (hv0 (matrix_injective (hz.trans matrix_zero.symm)))
  · exact Or.inl (matrix_injective (hf.trans matrix_first.symm))
  · exact Or.inr (matrix_injective (hs.trans matrix_second.symm))
  · have hw : v + S singer v ∈ M := M.add_mem hv (hM singer (mem_zpowers singer) v hv)
    have hw0 : v + S singer v ≠ 0 := by
      intro hz
      have hfix : S singer v = v := by
        have he := congrArg (fun x => v+x) hz
        have hvv : v+v = 0 := by
          apply Subtype.ext
          ext x i
          exact CharTwo.add_self_eq_zero _
        simpa only [← add_assoc,hvv,zero_add,add_zero] using he
      exact hv0 (show v ∈ (⊥ : Submodule (ZMod 2) Steinberg) from
        hd ▸ ⟨(mem_fixedSpace_zpowers_iff S singer v).mpr hfix,hv⟩)
    obtain ⟨h,hh,he⟩ := ht v hv hv0 _ hw hw0
    obtain ⟨i,rfl⟩ := exists_power h hh
    apply False.elim
    apply sum_not_orbit i
    rw [← hsum,act_matrix,he,matrix_add]
    congr 1
    rw [act_matrix]
    have hp : power 1 = singer := by simpa using power_eq 1
    rw [hp]

lemma canonical_interchange (M : Submodule (ZMod 2) Steinberg)
    (hM : ∀ h ∈ zpowers singer, ∀ v ∈ M, S h v ∈ M)
    (hd : fixedSpace S (zpowers singer) ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ zpowers singer, S h v = w)
    (v : Steinberg) (hv : v ∈ M) (hv0 : v ≠ 0)
    (hvD : v ∈ fixedSpace S (zpowers cubic)) :
    S inner v = SteinbergStructure.autEquiv outer v ∧ S inner v ≠ v := by
  rw [autEquiv_action]
  rcases canonical_fixed_cases M hM hd ht v hv hv0 hvD with rfl | rfl
  · exact ⟨inner_first.trans outer_first.symm, fun h => first_ne_second (h.symm.trans inner_first)⟩
  · exact ⟨inner_second.trans outer_second.symm, fun h => first_ne_second (inner_second.symm.trans h)⟩
lemma inner_normalizes : inner ∈ normalizer (zpowers cubic) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers ((MulAut.conj inner) cubic) = zpowers cubic
  rw [inner_cubic,zpowers_inv]
lemma outer_normalizes : (zpowers singer).map outer.toMonoidHom = zpowers singer := by
  rw [MonoidHom.map_zpowers]
  change zpowers (outer singer) = zpowers singer
  rw [outer_singer,zpowers_inv]
lemma outer_centralizes (d : Group) (hd : d ∈ zpowers cubic) : outer d = d := by
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hd
  rw [map_zpow,outer_cubic]
lemma first_fixed : first ∈ fixedSpace S (zpowers cubic) := by
  rw [mem_fixedSpace_zpowers_iff]
  apply matrix_injective
  rw [matrix_action,matrix_first]
  decide
lemma second_fixed : second ∈ fixedSpace S (zpowers cubic) := by
  rw [mem_fixedSpace_zpowers_iff]
  apply matrix_injective
  rw [matrix_action,matrix_second]
  decide

/-- The chosen outer involution uses precisely the inverse-transpose graph
map in the concrete special-linear model. -/
lemma outer_graphSL : outer = MulAut.conj singer * BinaryLinear.OuterCyclic.graphSL 3 := by
  change MulAut.conj singer * AutomorphismAction.graph = _
  apply congrArg (fun a : MulAut Group => MulAut.conj singer * a)
  ext g : 1
  change g⁻¹.transpose = g.transpose⁻¹
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  change (g⁻¹).val.transpose * g.val.transpose = 1
  rw [← Matrix.transpose_mul]
  have hh : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [hh,Matrix.transpose_one]
end
end BinaryLinearThree.SingerRestriction.CubicInterchange
