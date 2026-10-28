module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ResidualRigidity
public import Theory.SpecificGroups.PSL3.HigherFieldBorelResidual
public import Theory.SpecificGroups.PSL3Even.ThompsonProduct

/-!
# Higher-field PSL₃ Borel geometry

The pointwise Sylow fixer is a highest-root inner automorphism. A nontrivial
split torus scalar moves every nonidentity highest-root element, so the
full Borel has trivial automorphism fixer. Sylow conjugacy retains the
specified normalizer. Its two-perfectness is the concrete root calculation.
For a normal component, the proved Thompson product shows that this Borel
normalizes J(S): it normalizes the component Sylow and fixes the other factor.

Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098, using the
Thompson product of 2.5.7 and the matrix geometry of E.6.8.
-/

public section
open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.CartanActions
namespace Matrix.PSL3.OrdinaryBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem torus_conj_root (k : Fˣ) (a : F) :
    torusMap F (k,1) * projective F ⟨0,0,a⟩ * (torusMap F (k,1))⁻¹ =
      projective F ⟨0,0,(k:F)*a⟩ := by
  change projection F (torusSL F (k,1)) * projection F (specialLinear F ⟨0,0,a⟩) *
    (projection F (torusSL F (k,1)))⁻¹ = projection F (specialLinear F _)
  rw [← map_inv,← map_mul,← map_mul,← map_inv]
  apply congrArg (projection F)
  apply Subtype.ext
  have hu (u : U F) : (specialLinear F u).val = matrix F u := rfl
  simp only [SpecialLinearGroup.coe_mul,torusSL_val,hu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Matrix.diagonal_mul,Matrix.mul_diagonal]

 theorem borel_fixer {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (α : MulAut PSL(3,F)) (hfix : ∀ x ∈ borel F, α x = x) : α = 1 := by
  obtain ⟨a,ha⟩ := ResidualRigidity.fixer_unipotent_is_root_inner (by omega) hF α
    (by rw [mem_fixingSubgroup_iff]; exact fun u hu => hfix u (unipotent_le_borel F hu))
  have hlarge : 1 < Nat.card Fˣ := by
    rw [Nat.card_units,hF]
    have hpow : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
    omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨k,hk⟩ := exists_ne (1:Fˣ)
  have hkt := hfix (torusMap F (k,1)) (torus_le_borel F ⟨(k,1),rfl⟩)
  rw [ha] at hkt
  change projective F ⟨0,0,a⟩ * torusMap F (k,1) * (projective F ⟨0,0,a⟩)⁻¹ =
    torusMap F (k,1) at hkt
  have hc : torusMap F (k,1) * projective F ⟨0,0,a⟩ * (torusMap F (k,1))⁻¹ =
      projective F ⟨0,0,a⟩ := by
    exact mul_inv_eq_iff_eq_mul.mpr (mul_inv_eq_iff_eq_mul.mp hkt).symm
  rw [torus_conj_root] at hc
  have hka : (k:F)*a=a := congrArg U.c (projective_injective F hc)
  have ha0 : a=0 := by
    have hh : ((k:F)-1)*a=0 := by rw [sub_mul,one_mul,hka,sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (fun he => hk (Units.ext (sub_eq_zero.mp he)))
  rw [ha,ha0]
  have hu : (⟨0,0,0⟩:U F)=1 := rfl
  rw [hu,map_one,map_one]

theorem normalizer_fixer {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (α : MulAut PSL(3,F))
    (hfix : ∀ x ∈ normalizer (P : Set PSL(3,F)), α x = x) : α = 1 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (unipotentSylow F (by omega) hF) P
  let e := MulAut.conj g
  have hP : (unipotent F).map e.toMonoidHom = P := congrArg Sylow.toSubgroup hg
  have hB : (borel F).map e.toMonoidHom = normalizer (P : Set PSL(3,F)) := by
    rw [← normalizer_unipotent F (by omega) hF,map_equiv_normalizer_eq,hP]
    rfl
  have hα : MulAut.congr e.symm α = 1 := borel_fixer hn hF _ (by
    intro x hx
    change e.symm (α (e x)) = x
    rw [hfix (e x) (hB ▸ mem_map_of_mem e.toMonoidHom hx),e.symm_apply_apply])
  exact (MulAut.congr e.symm).injective (hα.trans (map_one _).symm)

theorem normalizer_twoPerfect {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) : IsPPerfect 2 (normalizer (P : Set PSL(3,F))) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (unipotentSylow F (by omega) hF) P
  let e := MulAut.conj g
  have hP : (unipotent F).map e.toMonoidHom = P := congrArg Sylow.toSubgroup hg
  have hB : (borel F).map e.toMonoidHom = normalizer (P : Set PSL(3,F)) := by
    rw [← normalizer_unipotent F (by omega) hF,map_equiv_normalizer_eq,hP]
    rfl
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  rw [← hB]
  exact (HigherFieldBorelResidual.borel_isPPerfect hlarge).of_surjective
    (e.toMonoidHom.subgroupMap _) (e.toMonoidHom.subgroupMap_surjective _)

variable {G : Type*} [Group G] [Finite G]
omit [CharP F 2] in
theorem normalizer_thompson (K : Subgroup G) [K.Normal]
    (e : K ≃* PSL(3,F)) {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n) (S : Sylow 2 G) :
    (normalizer ((S : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
  let J := Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)
  have he : J = ((S : Subgroup G) ⊓ K) ⊔ (J ⊓ centralizer (K:Set G)) :=
    PSL3Even.ThompsonInner.thompson_eq_sylow_component_sup_centralizer K e hn hF S
  rw [show Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)=J from rfl,he]
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_inf
  · have hh := le_normalizer_map (H := (S : Subgroup G).subgroupOf K) K.subtype
    rwa [subgroupOf_map_subtype] at hh
  · apply le_trans (map_subtype_le _) ?_
    apply le_trans (le_centralizer_iff.mpr (show J ⊓ centralizer (K:Set G) ≤
      centralizer (K:Set G) from inf_le_right))
    exact Subgroup.centralizer_le_normalizer _
end Matrix.PSL3.OrdinaryBorel
