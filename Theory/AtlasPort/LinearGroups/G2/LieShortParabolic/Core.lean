module

public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The short local two-core and Borel product in G₂

The sixth coordinate of the unipotent multiplication law is additive, so the
five-root subgroup is normalized by the positive roots. The displayed short
reflection formula proves its normality in the first local group. Conversely,
a normal two-subgroup lies in the common Sylow subgroup, and reflection forces
its sixth coordinate to vanish. This identifies the two-core of both the local
group and its torus extension, including the full binary model.

An explicit short-root word supplies the rank-one torus. Its conjugation
formula proves that the Borel normalizes the local group and that their literal
product is the first parabolic. Quotient and geometric identification are
separate results; none is assumed in the two-core proof.

Source: Aschbacher--Smith, F.1.11--12, printed pp. 262--264.
The coordinates use the licensed ATLAS root model from the imported modules.
-/

@[expose] public section

namespace Atlas.G2.LieParabolicSetup
open Explicit Atlas.SplitOctonion
variable {F : Type*} [Field F]
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem unipotent_normalizes_radical₁ :
    unipotent (K := F) ≤ Subgroup.normalizer (radical₁ (F := F) : Set (Model F)) := by
  have hconj : ∀ g ∈ unipotent (K := F), ∀ x ∈ radical₁ (F := F),
      g*x*g⁻¹ ∈ radical₁ := by
    intro g hg x hx
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    obtain ⟨u,hu,rfl⟩ := hx
    rw [unipotentProduct_inv, unipotentProduct_mul, unipotentProduct_mul]
    exact ⟨_, by simp [unipotentProductParameters, unipotentInverseParameters, hu], rfl⟩
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj g hg x
  · intro hx
    have hh := hconj g⁻¹ (unipotent.inv_mem hg) _ hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

theorem weylS_fiveRoot_conjugate [CharP F 2] (t : Fin 6 → F) (ht : t 5 = 0) :
    weylS * unipotentProduct t * weylS⁻¹ =
      unipotentProduct ![t 0 + t 1*t 4 + t 2*t 3,t 4,t 3,t 2,t 1,0] := by
  have h3 : (3 : F) = 1 := by
    have h := CharTwo.two_eq_zero (R := F)
    linear_combination h
  have hs : (weylS : Model F)⁻¹ = weylS := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, weylS_sq])
  rw [hs]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [unipotentProduct, ht, weylS, weylSEquiv, weylSLinear, weylSApply,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
      rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
      rootDApply,rootEApply,rootFApply, CharTwo.neg_eq, CharTwo.sub_eq_add] <;>
    ring_nf
  all_goals simp [CharTwo.two_eq_zero, h3]

theorem weylS_normalizes_radical₁ [CharP F 2] :
    (weylS : Model F) ∈ Subgroup.normalizer (radical₁ (F := F) : Set (Model F)) := by
  have hconj : ∀ x ∈ radical₁ (F := F), weylS*x*weylS⁻¹ ∈ radical₁ := by
    rintro x ⟨t,ht,rfl⟩
    rw [weylS_fiveRoot_conjugate t ht]
    exact ⟨_,rfl,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj x
  · intro hx
    have hh := hconj _ hx
    have he : (weylS : Model F)*(weylS*x*weylS⁻¹)*weylS⁻¹ = x := by
      calc
        _ = (weylS*weylS)*x*(weylS*weylS)⁻¹ := by group
        _ = x := by rw [← pow_two, weylS_sq]; simp
    rwa [he] at hh

theorem local₁_normalizes_radical₁ [CharP F 2] :
    local₁ (F := F) ≤ Subgroup.normalizer (radical₁ (F := F) : Set (Model F)) := by
  exact sup_le unipotent_normalizes_radical₁
    ((Subgroup.closure_le _).mpr (by simpa using weylS_normalizes_radical₁ (F := F)))

instance radical₁_normal [CharP F 2] :
    ((radical₁ (F := F)).subgroupOf local₁).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer local₁_normalizes_radical₁

theorem mem_radical₁_of_reflection_mem_unipotent [CharP F 2] {g : Model F}
    (hg : g ∈ unipotent) (hs : weylS*g*weylS⁻¹ ∈ unipotent) : g ∈ radical₁ := by
  rw [unipotent_eq_range] at hg hs
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨u,hu⟩ := hs
  have he := congrArg (fun g : Model F => g.val (basisVector 0) 1) hu
  have hleft : (unipotentProduct u).val (basisVector 0) 1 = 0 := by
    have hh := unipotent_le_fixingFirstVector (unipotentProduct_mem u)
    change (unipotentProduct u).val (basisVector 0) = basisVector 0 at hh
    rw [hh]
    rfl
  have hright : (weylS*unipotentProduct t*weylS⁻¹).val (basisVector 0) 1 = t 5 := by
    simp [unipotentProduct, basisVector, weylS, weylSEquiv, weylSLinear, weylSApply,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
      rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
      rootDApply,rootEApply,rootFApply, CharTwo.neg_eq]
  rw [hleft, hright] at he
  exact ⟨t, he.symm, rfl⟩

theorem local₁_pCore [Finite F] [CharP F 2] :
    (local₁ (F := F)).pCoreIn 2 = radical₁ := by
  apply le_antisymm
  · have hle : pCore 2 (local₁ (F := F)) ≤
        ((sylow (F := F)).subtype unipotent_le_local₁ : Subgroup local₁) :=
      pCore_isPGroup.le_sylow_of_normal _
    rintro _ ⟨g,hg,rfl⟩
    apply mem_radical₁_of_reflection_mem_unipotent (hle hg)
    let s : local₁ (F := F) := ⟨weylS,
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))⟩
    exact hle ((inferInstance : (pCore 2 (local₁ (F := F))).Normal).conj_mem g hg s)
  · exact Subgroup.le_pCoreIn_of_normalizes radical₁_isTwoGroup
      radical₁_le_local₁ local₁_normalizes_radical₁

theorem torus_normalizes_radical₁ :
    splitTorus (K := F) ≤ Subgroup.normalizer (radical₁ (F := F) : Set (Model F)) := by
  have hconj : ∀ g ∈ splitTorus (K := F), ∀ x ∈ radical₁ (F := F),
      g*x*g⁻¹ ∈ radical₁ := by
    rintro g ⟨⟨l,m⟩,rfl⟩ x ⟨t,ht,rfl⟩
    change torus l m * unipotentProduct t * (torus l m)⁻¹ ∈ radical₁
    rw [torus_unipotentProduct]
    exact ⟨_, by simp [torusUnipotentParameters, ht], rfl⟩
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj g hg x
  · intro hx
    have hh := hconj g⁻¹ (splitTorus.inv_mem hg) _ hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

theorem parabolic₁_normalizes_radical₁ [CharP F 2] :
    parabolic₁ (F := F) ≤ Subgroup.normalizer (radical₁ (F := F) : Set (Model F)) :=
  sup_le (sup_le unipotent_normalizes_radical₁ torus_normalizes_radical₁)
    ((Subgroup.closure_le _).mpr (by simpa using weylS_normalizes_radical₁ (F := F)))

theorem parabolic₁_pCore [Finite F] [CharP F 2] :
    (parabolic₁ (F := F)).pCoreIn 2 = radical₁ := by
  have hu : unipotent (K := F) ≤ parabolic₁ := le_trans le_sup_left le_sup_left
  apply le_antisymm
  · have hle : pCore 2 (parabolic₁ (F := F)) ≤
        ((sylow (F := F)).subtype hu : Subgroup parabolic₁) :=
      pCore_isPGroup.le_sylow_of_normal _
    rintro _ ⟨g,hg,rfl⟩
    apply mem_radical₁_of_reflection_mem_unipotent (hle hg)
    let s : parabolic₁ (F := F) := ⟨weylS,
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))⟩
    exact hle ((inferInstance : (pCore 2 (parabolic₁ (F := F))).Normal).conj_mem g hg s)
  · exact Subgroup.le_pCoreIn_of_normalizes radical₁_isTwoGroup
      ((fiveRootSubgroup_le_unipotent _ _).trans hu) parabolic₁_normalizes_radical₁

variable [CharP F 2]

theorem short_torus_word (a : Fˣ) :
    torus a a⁻¹ = rootF (a : F) * weylS * rootF (↑(a⁻¹) : F) * weylS *
      rootF (a : F) * weylS := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,weylS,weylSEquiv,weylSLinear,weylSApply,
      rootF,rootFEquiv,rootFLinear,rootFApply,CharTwo.neg_eq,CharTwo.sub_eq_add] <;>
    field_simp <;> ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

theorem short_torus_mem_local₁ (a : Fˣ) : torus a a⁻¹ ∈ local₁ (F := F) := by
  have hf : rootF (a : F) ∈ local₁ (F := F) :=
    unipotent_le_local₁ (Subgroup.subset_closure (by simp))
  have hi : rootF (↑(a⁻¹) : F) ∈ local₁ (F := F) :=
    unipotent_le_local₁ (Subgroup.subset_closure (by simp))
  have hs : (weylS : Model F) ∈ local₁ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  rw [short_torus_word]
  exact local₁.mul_mem (local₁.mul_mem (local₁.mul_mem (local₁.mul_mem
    (local₁.mul_mem hf hs) hi) hs) hf) hs

omit [CharP F 2] in
theorem torus_weylS_conjugate (l m : Fˣ) :
    torus l m * weylS * (torus l m)⁻¹ = torus (l*m⁻¹) (l*m⁻¹)⁻¹ * weylS := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,weylS,weylSEquiv,weylSLinear,weylSApply] <;>
    field_simp

theorem torus_normalizes_local₁ :
    splitTorus (K := F) ≤ Subgroup.normalizer (local₁ (F := F) : Set (Model F)) := by
  have hconj : ∀ t ∈ splitTorus (K := F), ∀ g ∈ local₁ (F := F),
      t*g*t⁻¹ ∈ local₁ := by
    intro t ht
    change local₁ ≤ local₁.comap (MulAut.conj t).toMonoidHom
    apply sup_le
    · intro u hu
      exact unipotent_le_local₁ (torus_normalizes_unipotent ht hu)
    · apply (Subgroup.closure_le _).mpr
      rintro g (rfl : g = weylS)
      obtain ⟨⟨l,m⟩,rfl⟩ := ht
      change torus l m * weylS * (torus l m)⁻¹ ∈ local₁
      rw [torus_weylS_conjugate]
      exact local₁.mul_mem (short_torus_mem_local₁ _)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj g hg x
  · intro hx
    have hh := hconj g⁻¹ (splitTorus.inv_mem hg) _ hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

theorem borel_normalizes_local₁ :
    borel (K := F) ≤ Subgroup.normalizer (local₁ (F := F) : Set (Model F)) :=
  sup_le (unipotent_le_local₁.trans local₁.le_normalizer) torus_normalizes_local₁

open scoped Pointwise in
/-- The literal product of the two subgroups, not only their generated join. -/
theorem parabolic₁_eq_local₁_mul_borel :
    (parabolic₁ (F := F) : Set (Model F)) = (local₁ (F := F) : Set (Model F)) * (borel (K := F) : Set (Model F)) := by
  rw [← local₁_sup_borel]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ borel_normalizes_local₁

end Atlas.G2.LieParabolicSetup
