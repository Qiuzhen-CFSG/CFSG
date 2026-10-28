module
public import Theory.SpecificGroups.PSL3.HigherFieldBorelGeometry
public import Theory.SpecificGroups.PSL3Four.CentralCover.NonElementaryParabolic
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover
public import Theory.GroupTheory.InnerInvolutionSylowCenter
public import Theory.GroupTheory.PResidual.PerfectCentralLift
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Borel geometry in perfect central covers of PSL₃

Sylow conjugacy transports the pointwise Sylow-fixer calculation. Perfectness
lifts innerness and triviality from the central quotient. A nontrivial
involutory Sylow fixer consequently forces a PSL₃(4) covering center to be
elementary, since a non-elementary center equals the entire Sylow center.
Central transfer proves two-perfectness of the full Borel. The actual
central-cover Thompson product then supplies its Thompson normalization.

Source: Aschbacher--Smith 15.1.21(i), pp.1097--1098, using 2.5.7 and
I.2.2(3a,b). The central kernel and the specified Sylow are retained.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OrdinaryBorel
variable {F E : Type*} [Field F] [Finite F] [CharP F 2]
variable [Group E] [Finite E] [Group.IsPerfect E]

/-- Every pointwise fixer of a specified Sylow subgroup is inner. -/
theorem sylow_fixer_inner {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (α : MulAut PSL(3,F))
    (hfix : ∀ x ∈ P, α x = x) : ∃ a, α = MulAut.conj a := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (LinearThree.unipotentSylow F hn hF) P
  let e := MulAut.conj g
  have hP : (LinearThree.unipotent F).map e.toMonoidHom = P := congrArg Sylow.toSubgroup hg
  have hf : MulAut.congr e.symm α ∈ fixingSubgroup (MulAut PSL(3,F))
      (LinearThree.unipotent F : Set PSL(3,F)) := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    change e.symm (α (e x)) = x
    have hxP : e x ∈ (P : Subgroup PSL(3,F)) := hP ▸ mem_map_of_mem e.toMonoidHom hx
    rw [hfix (e x) hxP,e.symm_apply_apply]
  obtain ⟨a,ha⟩ := LinearThree.ResidualRigidity.fixer_unipotent_is_root_inner hn hF _ hf
  exact (MulAut.congr_inner_iff e.symm α).mp ⟨_,ha⟩

/-- The full lifted Borel remains two-perfect across a central two-cover. -/
theorem cover_normalizer_twoPerfect {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (E ⧸ center E) ≃* PSL(3,F)) (hZ : IsPGroup 2 (center E))
    (P : Sylow 2 E) : IsPPerfect 2 (normalizer (P : Set E)) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  apply isPPerfect_of_central_pKernel_image q (normalizer (P : Set E)) hk.le
    (hk.symm ▸ hZ)
  · exact hk.le.trans ((hZ.le_sylow_of_normal P).trans (P : Subgroup E).le_normalizer)
  · intro hd
    exact P.not_dvd_index (hd.trans (index_dvd_of_le (P : Subgroup E).le_normalizer))
  · rw [P.normalizer_map_surjective q hq]
    exact normalizer_twoPerfect hn hF (P.mapSurjective hq)

/-- The full lifted Borel has trivial pointwise automorphism fixer. -/
theorem cover_normalizer_fixer {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (E ⧸ center E) ≃* PSL(3,F)) (P : Sylow 2 E)
    (α : MulAut E) (hfix : ∀ x ∈ normalizer (P : Set E), α x = x) : α = 1 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  have hB : (normalizer (P : Set E)).map q = normalizer (Q : Set PSL(3,F)) :=
    P.normalizer_map_surjective q hq
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  apply normalizer_fixer hn hF Q
  intro x hx
  rw [←hB] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  change MulAut.centralQuotientAction e α (e (QuotientGroup.mk' (center E) y)) = _
  rw [MulAut.centralQuotientAction_apply,hfix y hy]
  rfl

/-- A nontrivial involutory Sylow fixer forces the exceptional covering center
 to be elementary; the center is not silently removed. -/
theorem four_cover_center_frattini
    (e : (E ⧸ center E) ≃* Matrix.PSL3Four.PSL) (hZ : IsPGroup 2 (center E))
    (P : Sylow 2 E) (α : MulAut E) (hα : α^2 = 1) (hne : α ≠ 1)
    (hfix : ∀ x ∈ P, α x = x) : frattini (center E) = ⊥ := by
  by_contra hphi
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  have hi : ∃ x, MulAut.centralQuotientAction e α = MulAut.conj x := by
    apply sylow_fixer_inner (n:=2) (by decide) (by simpa using Matrix.PSL3Four.card_F) Q
    rintro _ ⟨x,hx,rfl⟩
    change MulAut.centralQuotientAction e α (e (QuotientGroup.mk' (center E) x)) = _
    rw [MulAut.centralQuotientAction_apply,hfix x hx]
    rfl
  obtain ⟨x,hx⟩ := (MulAut.centralQuotientAction_inner_iff e α).mp hi
  obtain ⟨a,ha,haα⟩ := MulAut.exists_center_sylow_conjugator_of_inner_involution
    P α hα ⟨x,hx.symm⟩ hfix hZ
  have haZ : (a:E) ∈ center E :=
    (Matrix.PSL3Four.NonElementaryKernel.source_nonElementary_center e hZ hphi P).1 ▸
      mem_map_of_mem (P : Subgroup E).subtype ha
  apply hne
  rw [←haα]
  apply MulEquiv.ext
  intro y
  change (a:E)*y*(a:E)⁻¹=y
  rw [←mem_center_iff.mp haZ y,mul_inv_cancel_right]

variable {G : Type*} [Group G] [Finite G]

omit [CharP F 2] in
/-- A perfect central cover's Thompson product makes its Borel normalize J(S). -/
theorem cover_normalizer_thompson (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* PSL(3,F)) (hZ : IsPGroup 2 (center K))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ W : Subgroup PSL(3,F), IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (PSL3Even.ThompsonCentralCover.projection K e)))
    {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n) (S : Sylow 2 G) :
    (normalizer ((S : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
  let J := Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)
  have he : J = ((S : Subgroup G) ⊓ K) ⊔ (J ⊓ centralizer (K:Set G)) :=
    PSL3Even.ThompsonCentralCover.thompson_eq_sylow_component_sup_centralizer
      K e hZ hlift hn hF S
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
