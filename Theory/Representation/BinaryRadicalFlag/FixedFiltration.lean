module
public import Theory.Representation.NormalInvariants
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# The fixed filtration of a normal two-group

Starting at zero, take the full U-fixed space in the quotient by each
preceding layer. Normality makes every resulting layer invariant under
the ambient action. A nonzero modular fixed vector makes the next layer
strictly larger unless the whole module has been reached. Finite dimension
therefore gives an exhaustive strict flag with length at most the dimension.
The two-group acts trivially on every successive factor.

This supplies the actual linear flag for Aschbacher, A pushing up theorem
for finite groups (1981), 8.2(7), pp.73–74; it is used in Aschbacher–Smith
C.2.7(3), printed pp.145–146. No parabolic-existence premise is assumed.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Representation.BinaryRadical
variable {F N V : Type*} [Field F] [Group N] [AddCommGroup V] [Module F V]
    (ρ : Representation F N V) (U : Subgroup N) [U.Normal]

/-- The next full fixed layer: U acts trivially modulo the preceding layer. -/
def next (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := {
    carrier := {v | ∀ u : U, ρ u v - v ∈ W.toSubmodule}
    zero_mem' := by intro u; simpa only [map_zero,sub_self] using W.toSubmodule.zero_mem
    add_mem' := by
      intro v w hv hw u
      simpa only [map_add,add_sub_add_comm] using W.toSubmodule.add_mem (hv u) (hw u)
    smul_mem' := by
      intro c v hv u
      simpa only [map_smul,smul_sub] using W.toSubmodule.smul_mem c (hv u) }
  apply_mem_toSubmodule g v hv u := by
    let u' : U := ⟨g⁻¹ * u * g, by simpa only [inv_inv] using (inferInstance : U.Normal).conj_mem u u.property g⁻¹⟩
    have h := W.apply_mem_toSubmodule g (hv u')
    simpa only [u',map_sub,←Module.End.mul_apply,←map_mul,Subgroup.coe_mk,
      mul_assoc,mul_inv_cancel_left] using h

theorem le_next (W : Subrepresentation ρ) : W ≤ next ρ U W := by
  intro v hv
  change ∀ u : U, ρ u v - v ∈ W.toSubmodule
  intro u
  exact W.toSubmodule.sub_mem (W.apply_mem_toSubmodule u hv) hv

variable [Finite N] [CharP F 2] [FiniteDimensional F V]

theorem lt_next {W : Subrepresentation ρ} (hW : W ≠ ⊤) (hU : IsPGroup 2 U) :
    W < next ρ U W := by
  have hW' : W.toSubmodule ≠ ⊤ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial (V ⧸ W.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hW'
  have hc : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector (hc ▸ (by decide : (2:ℕ) ≠ 0))
    (hc.symm ▸ hU) (W.quotientRepresentation.comp U.subtype)
  obtain ⟨w,rfl⟩ := W.toSubmodule.mkQ_surjective v
  refine SetLike.lt_iff_le_and_exists.mpr ⟨le_next ρ U W,w,?_,?_⟩
  · change ∀ u : U, ρ u w - w ∈ W.toSubmodule
    intro u
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ u w - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hfix u)
  · intro hw
    exact hv ((Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr hw)

omit [Finite N] [CharP F 2] [FiniteDimensional F V] in
noncomputable def filtration (i : ℕ) : Subrepresentation ρ := (next ρ U)^[i] ⊥

omit [Finite N] [CharP F 2] [FiniteDimensional F V] in
@[simp] theorem filtration_zero : filtration ρ U 0 = ⊥ := rfl
omit [Finite N] [CharP F 2] [FiniteDimensional F V] in
@[simp] theorem filtration_succ (i : ℕ) :
    filtration ρ U (i+1) = next ρ U (filtration ρ U i) :=
  Function.iterate_succ_apply' _ _ _

omit [Finite N] [CharP F 2] [FiniteDimensional F V] in
theorem filtration_mono : Monotone (filtration ρ U) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [filtration_succ]
  exact le_next ρ U _

theorem exists_filtration_top (hU : IsPGroup 2 U) : ∃ k, filtration ρ U k = ⊤ := by
  by_contra! h
  have hs : StrictMono (fun i => Module.finrank F (filtration ρ U i).toSubmodule) := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hh := lt_next ρ U (h i) hU
    rw [← filtration_succ] at hh
    exact Submodule.finrank_lt_finrank_of_lt hh
  have ha := hs.id_le (Module.finrank F V+1)
  have hb := Submodule.finrank_le (filtration ρ U (Module.finrank F V+1)).toSubmodule
  exact Nat.not_succ_le_self _ (ha.trans hb)


/-- A normal two-group has a full invariant flag on whose layers it acts trivially. -/
theorem exists_fixed_filtration (hU : IsPGroup 2 U) :
    ∃ (k : ℕ) (W : Fin (k+1) → Submodule F V),
      StrictMono W ∧ W 0 = ⊥ ∧ W (Fin.last k) = ⊤ ∧
      k ≤ Module.finrank F V ∧
      (∀ g i v, v ∈ W i → ρ g v ∈ W i) ∧
      (∀ (i : Fin k) (u : U) v, v ∈ W i.succ → ρ u v - v ∈ W i.castSucc) := by
  classical
  let ex := exists_filtration_top ρ U hU
  let k := Nat.find ex
  let W : Fin (k+1) → Submodule F V := fun i => (filtration ρ U i).toSubmodule
  have hk : filtration ρ U k = ⊤ := Nat.find_spec ex
  have hs : StrictMono W := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hne : filtration ρ U i ≠ ⊤ := Nat.find_min ex i.isLt
    have hlt := lt_next ρ U hne hU
    rw [←filtration_succ] at hlt
    exact hlt
  have hbound : k ≤ Module.finrank F V := by
    let f : Fin (k+1) → Fin (Module.finrank F V+1) := fun i =>
      ⟨Module.finrank F (W i),Nat.lt_succ_of_le (Submodule.finrank_le (W i))⟩
    have hf : Function.Injective f := by
      apply StrictMono.injective
      intro i j hij
      exact Submodule.finrank_lt_finrank_of_lt (hs hij)
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_fin,Nat.add_le_add_iff_right] using hc
  refine ⟨k,W,hs,?_,?_,hbound,?_,?_⟩
  · exact congrArg Subrepresentation.toSubmodule (filtration_zero ρ U)
  · exact congrArg Subrepresentation.toSubmodule hk
  · intro g i v hv
    exact (filtration ρ U i).apply_mem_toSubmodule g hv
  · intro i u v hv
    change v ∈ (filtration ρ U (i+1)).toSubmodule at hv
    rw [filtration_succ] at hv
    exact hv u

end Representation.BinaryRadical
