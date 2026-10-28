module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# The exceptional module is the whole odd-core commutator

For an abelian odd core W=[W,S], an S-normalized subgroup F of order three
captures the whole W-action commutator whenever [V,S]≤[V,F]. The action
is on an elementary abelian two-group. Coprime F-action splits V into its
fixed subgroup C and U=[V,F]. Abelianness makes W preserve both pieces;
the assumed containment makes S fix C, hence W=[W,S] fixes C as well.
Thus [V,W]≤U, and actor monotonicity supplies the reverse inclusion.

This identifies the sixteen-element local module with V* in the bounded
exceptional branch of Stellmacher (1.6)(b), journal p.18.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative commutatorElement
namespace Stellmacher.SectionOne
universe u

public theorem commutatorAction_oddCore_eq_of_exceptional_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S F : Subgroup G) [IsMulCommutative (oddCore G)]
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (hFW : F ≤ oddCore G) (hFcard : Nat.card F = 3)
    (hSnorm : S ≤ Subgroup.normalizer (F : Set G))
    (hcommS : commutatorAction S V ≤ commutatorAction F V) :
    commutatorAction (oddCore G) V = commutatorAction F V := by
  let W : Subgroup G := oddCore G
  let U : Subgroup V := commutatorAction F V
  let C : Subgroup V := FixedPoints.subgroup F V
  have hWnormF : W ≤ Subgroup.normalizer (F : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer (F : Set G))
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨f, hFW hf⟩ : W) (⟨w, hw⟩ : W))
  let _ : IsInvariant S V U := commutatorAction_isInvariant_of_normalizing_actor S F hSnorm
  let _ : IsInvariant S V C := fixedPoints_isInvariant_of_normalizing_actor S F hSnorm
  let _ : IsInvariant W V U := commutatorAction_isInvariant_of_normalizing_actor W F hWnormF
  let _ : IsInvariant W V C := fixedPoints_isInvariant_of_normalizing_actor W F hWnormF
  have hcopF : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFcard, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcomp : IsCompl C U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y) hcopF inferInstance
  have hSfix : C ≤ FixedPoints.subgroup S V := by
    intro v hv s
    have hdU : v⁻¹ * (s • v) ∈ U := by
      apply hcommS
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨s, v, rfl⟩
    have hdC : v⁻¹ * (s • v) ∈ C := C.mul_mem (C.inv_mem hv)
      ((IsInvariant.invariant (A := S) (G := V) (H := C) s v).mp hv)
    exact (inv_mul_eq_one.mp (hcomp.disjoint.le_bot ⟨hdC, hdU⟩)).symm
  have hWfix : W ≤ fixingSubgroup G (C : Set V) := by
    change oddCore G ≤ _
    rw [hW]
    apply Subgroup.commutator_le.mpr
    intro w hw s hs
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hinv : w⁻¹ • v ∈ C :=
      (IsInvariant.invariant (A := W) (G := V) (H := C) (⟨w, hw⟩ : W)⁻¹ v).mp hv
    have hsfix : s • (w⁻¹ • v) = w⁻¹ • v := hSfix hinv ⟨s, hs⟩
    have hsinv : s⁻¹ • v = v := hSfix hv ⟨s⁻¹, S.inv_mem hs⟩
    simp only [commutatorElement_def, mul_smul]
    rw [hsinv, hsfix, smul_inv_smul]
  apply le_antisymm
  · rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le (K := U)).mpr
    rintro v ⟨w, x, rfl⟩
    have hx : x ∈ C ⊔ U := by rw [hcomp.sup_eq_top]; trivial
    let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
    obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hwc : w • c = c :=
      (mem_fixingSubgroup_iff (M := G) (s := (C : Set V))).mp (hWfix w.property) c hc
    have hwu : w • u ∈ U :=
      (IsInvariant.invariant (A := W) (G := V) (H := U) w u).mp hu
    have heq : (c * u)⁻¹ * (w • (c * u)) = u⁻¹ * (w • u) := by
      rw [mul_inv_rev, smul_mul', hwc]
      group
    rw [heq]
    exact U.mul_mem (U.inv_mem hu) hwu
  · rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro v ⟨f, x, rfl⟩
    exact ⟨(⟨f, hFW f.property⟩ : W), x, rfl⟩

end Stellmacher.SectionOne

