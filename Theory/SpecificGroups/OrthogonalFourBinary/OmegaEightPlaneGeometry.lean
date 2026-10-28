module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega

/-!
# Plane-stabilizer geometry of commuting binary Omega involutions

Every nonidentity involution in the genuine Siegel-generated Ω fixes a
four-element plane. Among two distinct commuting involutions, at least one
has centralizer of order twelve and pointwise fixed-plane stabilizer of
order two. These are the axis involutions in Ω ≅ S₃ × S₃; two distinct
non-axis involutions do not commute.

The finite checks use the existing 72-coordinate bijection with actual
quadratic isometries. Balanced reflection parity is the proved membership
test for Ω. Counts are transported to the literal centralizer and action
kernel, retaining the actual natural action for subgroup lifting.

This is the finite input for the elementary-eight normalizer construction
in the full Omega branch of Aschbacher--Smith 15.1.11, printed p.1089.
-/

namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000
private def balanced (k : Code) : Prop := k.1.2=k.2.1.2
private instance (k : Code) : Decidable (balanced k) := inferInstanceAs (Decidable (_=_))
private def nontrivialInvolution (k : Code) : Prop :=
  (∃v:Space,eval k v≠v) ∧ ∀v:Space,eval k (eval k v)=v
private instance (k : Code) : Decidable (nontrivialInvolution k) :=
  inferInstanceAs (Decidable (_∧_))
private def commutes (k j : Code) : Prop := ∀v:Space,eval k (eval j v)=eval j (eval k v)
private instance (k j : Code) : Decidable (commutes k j) := inferInstanceAs (Decidable (∀_,_))
private def fixes (k j : Code) : Prop := ∀v:Space,eval k v=v → eval j v=v
private instance (k j : Code) : Decidable (fixes k j) := inferInstanceAs (Decidable (∀_,_))
private def axis (k : Code) : Prop :=
  Fintype.card {j:Code // balanced j ∧ commutes k j}=12 ∧
  Fintype.card {j:Code // balanced j ∧ fixes k j}=2
private instance (k : Code) : Decidable (axis k) := inferInstanceAs (Decidable (_∧_))
set_option maxRecDepth 10000 in
private theorem fixed_table : ∀k:Code, balanced k → nontrivialInvolution k →
    Fintype.card {v:Space // eval k v=v}=4 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem axis_table : ∀k j:Code, balanced k → balanced j →
    nontrivialInvolution k → nontrivialInvolution j → k≠j → commutes k j →
    axis k ∨ axis j := by decide +kernel

/-- The pointwise stabilizer in Ω of the fixed plane of an involution. -/
@[expose] public def omegaFixedPlaneKernel (z : omega) : Subgroup omega where
  carrier g := ∀v:Space, z • v=v → g • v=v
  one_mem' := by intro v hv; exact one_smul _ _
  mul_mem' := by intro a b ha hb v hv; rw [mul_smul,hb v hv,ha v hv]
  inv_mem' := by intro a ha v hv; exact inv_smul_eq_iff.mpr (ha v hv).symm

/-- The axis involution supplies centralizer order 12 and fixed-plane kernel order 2. -/
@[expose] public def OmegaEightPlaneGeometry (z : omega) : Prop :=
  Nat.card (Subgroup.centralizer ({z}:Set omega))=12 ∧
  Nat.card (omegaFixedPlaneKernel z)=2

private noncomputable def omegaCodeEquiv : {k:Code // balanced k} ≃ omega :=
  codeEquiv.subtypeEquiv (fun k => (codeMap_mem_omega k).symm)

private theorem commutes_iff (k j : Code) :
    commutes k j ↔ Commute (codeMap k) (codeMap j) := by
  constructor
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change candidate k (candidate j v)=candidate j (candidate k v)
    simpa only [candidate_eval] using h v
  · intro h v
    have hh := congrArg (fun g : IsometryGroup => g.val v) h.eq
    change candidate k (candidate j v)=candidate j (candidate k v) at hh
    simpa only [candidate_eval] using hh

private theorem code_nontrivial_involution (z:omega) (hne:z≠1) (h2:z^2=1)
    (k:Code) (hk:codeMap k=z.val) : nontrivialInvolution k := by
  constructor
  · by_contra! h
    apply hne
    apply Subtype.ext
    rw [←hk]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact (candidate_eval k v).trans (h v)
  · intro v
    have hh := congrArg (fun g:omega => g.val.val v) h2
    change z.val.val (z.val.val v)=v at hh
    rw [←hk] at hh
    simpa only [codeMap,candidate_eval] using hh

private theorem axis_of_code (z:omega) (k:Code) (hk:codeMap k=z.val)
    (haxis:axis k) : OmegaEightPlaneGeometry z := by
  have hc : ∀j:{j:Code // balanced j},
      commutes k j.val ↔ omegaCodeEquiv j∈Subgroup.centralizer ({z}:Set omega) := by
    intro j
    rw [commutes_iff,Subgroup.mem_centralizer_singleton_iff]
    change Commute (codeMap k) (codeMap j.val) ↔ Commute (omegaCodeEquiv j) z
    rw [hk]
    constructor
    · intro h
      apply Subtype.ext
      exact h.symm.eq
    · intro h
      exact congrArg Subtype.val h.symm.eq
  let ec := (Equiv.subtypeSubtypeEquivSubtypeInter balanced (commutes k)).symm.trans
    (omegaCodeEquiv.subtypeEquiv hc)
  have hf : ∀j:{j:Code // balanced j},
      fixes k j.val ↔ omegaCodeEquiv j∈omegaFixedPlaneKernel z := by
    intro j
    change (∀v,eval k v=v → eval j.val v=v) ↔
      ∀v, z.val.val v=v → (codeMap j.val).val v=v
    rw [←hk]
    simp only [codeMap,candidate_eval]
  let ef := (Equiv.subtypeSubtypeEquivSubtypeInter balanced (fixes k)).symm.trans
    (omegaCodeEquiv.subtypeEquiv hf)
  exact ⟨(Nat.card_congr ec).symm.trans (by
    rw [Nat.card_eq_fintype_card]; exact haxis.1),
    (Nat.card_congr ef).symm.trans (by
      rw [Nat.card_eq_fintype_card]; exact haxis.2)⟩

/-- Every nonidentity Ω-involution fixes precisely four vectors. -/
public theorem omega_involution_fixed_card (z:omega) (hne:z≠1) (h2:z^2=1) :
    Nat.card {v:Space // z • v=v}=4 := by
  obtain ⟨k,hk⟩ := codeMap_bijective.surjective z.val
  have h := fixed_table k ((codeMap_mem_omega k).mp (hk.symm ▸ z.property))
    (code_nontrivial_involution z hne h2 k hk)
  change Nat.card {v:Space // z.val.val v=v}=4
  rw [←hk]
  simp only [codeMap,candidate_eval]
  rw [Nat.card_eq_fintype_card]
  exact h

/-- Two distinct commuting involutions cannot both be the non-axis type. -/
public theorem omega_commuting_involutions_plane_geometry
    (z w:omega) (hz:z≠1) (hw:w≠1) (hz2:z^2=1) (hw2:w^2=1)
    (hne:z≠w) (hcomm:Commute z w) :
    OmegaEightPlaneGeometry z ∨ OmegaEightPlaneGeometry w := by
  obtain ⟨k,hk⟩ := codeMap_bijective.surjective z.val
  obtain ⟨j,hj⟩ := codeMap_bijective.surjective w.val
  have hkbal := (codeMap_mem_omega k).mp (hk.symm ▸ z.property)
  have hjbal := (codeMap_mem_omega j).mp (hj.symm ▸ w.property)
  have hkj : k≠j := by
    intro he
    exact hne (Subtype.ext (hk.symm.trans ((congrArg codeMap he).trans hj)))
  have hc : commutes k j := (commutes_iff k j).mpr (by
    rw [hk,hj]
    exact congrArg Subtype.val hcomm.eq)
  rcases axis_table k j hkbal hjbal (code_nontrivial_involution z hz hz2 k hk)
      (code_nontrivial_involution w hw hw2 j hj) hkj hc with h|h
  · exact Or.inl (axis_of_code z k hk h)
  · exact Or.inr (axis_of_code w j hj h)
end OrthogonalFourBinary.SylowGeometry
