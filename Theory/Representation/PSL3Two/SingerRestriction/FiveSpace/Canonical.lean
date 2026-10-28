module

public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace.Basic
public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace.Certificate

/-!
# Canonical Singer normalizer action on the moving three-space

The matrix certificates apply to the trace-zero endomorphism representation
through its actual conjugation action. If a fixed-point-free Singer subspace
is transitive away from zero, then `v + singer(v)` belongs to the same orbit
as v. The certificate places the cubic image there too. The explicit normalizer
factorization extends preservation to the whole canonical Singer normalizer.

Source: Aschbacher–Smith, J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

public section

open Matrix Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Subgroup
namespace BinaryLinearThree.SingerRestriction.FiveSpace
open Matrix.PSL3Two.OuterInvolutionSinger Certificate
noncomputable local instance : AddCommGroup Steinberg := inferInstance
noncomputable local instance : Module (ZMod 2) Steinberg := inferInstance
private noncomputable def matrix (v : Steinberg) : Certificate.Mat := LinearMap.toMatrix' v.val
private theorem matrix_injective : Function.Injective matrix := by
  intro v w he
  exact Subtype.ext (LinearMap.toMatrix'.injective he)
private theorem matrix_action (g : Group) (v : Steinberg) :
    matrix (S g v) = g.val * matrix v * (g⁻¹).val := by
  change LinearMap.toMatrix' (g.val.toLin' ∘ₗ v.val ∘ₗ (g⁻¹).val.toLin') = _
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', matrix, mul_assoc]
private theorem matrix_trace (v : Steinberg) : (matrix v).trace = 0 := by
  rw [matrix, ← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact v.property
private theorem act_matrix (i : Fin 7) (v : Steinberg) :
    act i (matrix v) = matrix (S (power i) v) := by
  rw [matrix_action, act, inverseMatrix_eq]
  rfl
private theorem exists_power (g : Group) (hg : g ∈ zpowers singer) :
    ∃ i : Fin 7, power i = g := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ho : orderOf singer = 7 :=
    orderOf_eq_prime (by decide : singer ^ 7 = 1) (by decide : singer ≠ 1)
  have hr := (isOfFinOrder_of_finite singer).mem_zpowers_iff_mem_range_orderOf.mp hg
  rw [ho] at hr
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hr
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, (power_eq ⟨i, Finset.mem_range.mp hi⟩).trans he⟩
private theorem normalizer_form (g : Group) (hg : g ∈ normalizer (zpowers singer)) :
    ∃ i : Fin 7, ∃ j : Fin 3, g = power i * cubicPower j := by
  apply normalizer_certificate g
  have hc := (mem_normalizer_iff.mp hg singer).mp (mem_zpowers singer)
  obtain ⟨i, hi⟩ := exists_power _ hc
  exact ⟨i, mul_inv_eq_iff_eq_mul.mp hi.symm⟩
private theorem cubic_orbit (v : Steinberg)
    (hv : ∃ h ∈ zpowers singer, S h v = v + S singer v) :
    ∃ h ∈ zpowers singer, S cubic v = S h v := by
  obtain ⟨h, hh, he⟩ := hv
  obtain ⟨i, rfl⟩ := exists_power h hh
  have hm : ∃ i : Fin 7, act i (matrix v) = matrix v + act 1 (matrix v) := by
    refine ⟨i, ?_⟩
    rw [act_matrix, act_matrix]
    have hp1 : power 1 = singer := by simpa using power_eq 1
    rw [hp1, he]
    exact map_add LinearMap.toMatrix' v.val (S singer v).val
  obtain ⟨j, hj⟩ := vector_certificate (matrix v) (matrix_trace v) hm
  have hpj : power j ∈ zpowers singer := by
    rw [power_eq]
    exact (zpowers singer).pow_mem (mem_zpowers singer) _
  refine ⟨power j, hpj, ?_⟩
  apply matrix_injective
  rw [matrix_action, ← act_matrix j v]
  have hi : (cubic⁻¹).val = cubicMatrix 2 := by decide
  rw [hi]
  exact hj

theorem canonical_mem
    (M : Submodule (ZMod 2) Steinberg)
    (hM : ∀ h ∈ zpowers singer, ∀ v ∈ M, S h v ∈ M)
    (hd : fixedSpace S (zpowers singer) ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ zpowers singer, S h v = w)
    (g : Group) (hg : g ∈ normalizer (zpowers singer)) (v : Steinberg) (hv : v ∈ M) :
    S g v ∈ M := by
  have hc : ∀ v ∈ M, S cubic v ∈ M := by
    intro v hv
    by_cases hv0 : v = 0
    · simpa only [hv0, map_zero] using M.zero_mem
    have hw : v + S singer v ∈ M := M.add_mem hv (hM singer (mem_zpowers singer) v hv)
    have hw0 : v + S singer v ≠ 0 := by
      intro hz
      have hfix : S singer v = v := by
        have hh := congrArg (fun x => v + x) hz
        have hvv : v + v = 0 := by
          apply Subtype.ext
          ext x i
          exact CharTwo.add_self_eq_zero _
        simpa only [← add_assoc, hvv, zero_add, add_zero] using hh
      have hf := (mem_fixedSpace_zpowers_iff S singer v).mpr hfix
      exact hv0 (show v ∈ (⊥ : Submodule (ZMod 2) Steinberg) from hd ▸ ⟨hf,hv⟩)
    obtain ⟨h, hh, he⟩ := cubic_orbit v (ht v hv hv0 _ hw hw0)
    rw [he]
    exact hM h hh v hv
  have hcp (n : ℕ) : ∀ v ∈ M, S (cubic ^ n) v ∈ M := by
    induction n with
    | zero => intro v hv; simpa only [pow_zero, map_one, Module.End.one_apply] using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact ih _ (hc v hv)
  obtain ⟨i, j, rfl⟩ := normalizer_form g hg
  rw [map_mul, Module.End.mul_apply, cubicPower_eq]
  have hpi : power i ∈ zpowers singer := by
    rw [power_eq]
    exact (zpowers singer).pow_mem (mem_zpowers singer) _
  exact hM _ hpi _ (hcp j v hv)

theorem conjugate_apply (t h : Group) (v : Steinberg) :
    S ((MulAut.conj t) h) (S t v) = S t (S h v) := by
  change S (t*h*t⁻¹) (S t v) = _
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]


end BinaryLinearThree.SingerRestriction.FiveSpace
