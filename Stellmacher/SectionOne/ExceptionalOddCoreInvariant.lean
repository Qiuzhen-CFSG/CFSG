module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupAction.FixedLineIndecomposable
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.Commutator.ActionTriviality

/-!
# The whole odd core preserves the exceptional module

In the faithful Section 1 setting, let the odd core `W` be a three-group,
and let a two-group `S` normalize an order-three subgroup `F≤W`.
Suppose `U=[V,F]` has two common `S`-fixed elements, contains the full
`S`-action commutator, and `C_W(S)=1`. Then `U` is `W`-invariant.

The proof identifies `U` with `[V,Z(W)]`. The center is nontrivial,
normal, and equals its commutator with `S` by coprime decomposition.
The full-module containment makes `S` fix `C_V(F)`; the center preserves
that complement and hence fixes it too. Thus `[V,Z(W)]≤U`.
Coprime center-fixed and center-commutator subgroups restrict to disjoint
`S`-invariant subgroups of `U`. Its fixed subgroup of order two forces
one to vanish; faithfulness rules out the commutator vanishing. A second
use of coprime decomposition gives the identification.

This supplies the invariant-module transfer needed before embedding the
odd core into `GL₄(2)` in Stellmacher (1.6), journal p.18. A trivial
pointwise stabilizer alone is not used to infer invariance.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative commutatorElement

namespace Stellmacher.SectionOne

universe u

public theorem commutatorAction_isInvariant_oddCore_of_exceptional_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S F : Subgroup G)
    (hS : IsPGroup 2 S) (hWthree : IsPGroup 3 (oddCore G))
    (hFW : F ≤ oddCore G) (hFcard : Nat.card F = 3)
    (hSnorm : S ≤ Subgroup.normalizer (F : Set G))
    (hfixed : Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup S V : Subgroup V) = 2)
    (hcommS : commutatorAction S V ≤ commutatorAction F V)
    (hCWS : oddCore G ⊓ Subgroup.centralizer (S : Set G) = ⊥) :
    IsInvariant (oddCore G) V (commutatorAction F V) := by
  let W : Subgroup G := oddCore G
  let Z : Subgroup G := centerIn W
  let U : Subgroup V := commutatorAction F V
  let C : Subgroup V := FixedPoints.subgroup F V
  let N : Subgroup V := commutatorAction Z V
  let _ : W.Normal := pPrimeCore_normal
  let _ : Z.Normal := by dsimp [Z, centerIn]; infer_instance
  let _ : Group.IsSolvable G := h.G_solvable
  let _ : IsInvariant S V U := commutatorAction_isInvariant_of_normalizing_actor S F hSnorm
  let _ : IsInvariant S V C := fixedPoints_isInvariant_of_normalizing_actor S F hSnorm
  have hZnormF : Z ≤ Subgroup.normalizer (F : Set G) :=
    (inf_le_right.trans (Subgroup.centralizer_le hFW)).trans
      (Subgroup.centralizer_le_normalizer (F : Set G))
  let _ : IsInvariant Z V U := commutatorAction_isInvariant_of_normalizing_actor Z F hZnormF
  let _ : IsInvariant Z V C := fixedPoints_isInvariant_of_normalizing_actor Z F hZnormF
  have hWne : W ≠ ⊥ := by
    intro hw
    have hFbot : F = ⊥ := le_antisymm (hFW.trans hw.le) bot_le
    simp [hFbot] at hFcard
  let _ : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  have hZne : Z ≠ ⊥ := by
    have hcenter := hWthree.bot_lt_center
    intro hz
    have hmap : (Subgroup.center W).map W.subtype = ⊥ := by
      simpa only [Z, centerIn_eq_map_center] using hz
    have hc : Subgroup.center W = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center W) W.subtype_injective).mp hmap
    exact hcenter.ne' hc
  have hZodd : Nat.Coprime 2 (Nat.card Z) :=
    (pPrimeCore_coprime_card (G := G) (p := 2)).of_dvd_right
      (Subgroup.card_dvd_of_le (show Z ≤ W from inf_le_left))
  have hcopSZ : Nat.Coprime (Nat.card S) (Nat.card Z) := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn]
    exact hZodd.pow_left n
  have hZS : Z = ⁅Z, S⁆ := by
    have hc : Z ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
      apply le_antisymm _ bot_le
      exact (inf_le_inf (show Z ≤ W from inf_le_left) le_rfl).trans hCWS.le
    have hd := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime
      Z S Subgroup.le_normalizer_of_normal inferInstance hcopSZ
    simpa only [hc, sup_bot_eq] using hd
  have hcopF : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFcard, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompF : IsCompl C U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y) hcopF inferInstance
  have hSfixC : C ≤ FixedPoints.subgroup S V := by
    intro v hv s
    have hdU : v⁻¹ * (s • v) ∈ U := by
      apply hcommS
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨s, v, rfl⟩
    have hdC : v⁻¹ * (s • v) ∈ C := C.mul_mem (C.inv_mem hv)
      ((IsInvariant.invariant (A := S) (G := V) (H := C) s v).mp hv)
    have hd1 : v⁻¹ * (s • v) = 1 := hcompF.disjoint.le_bot ⟨hdC, hdU⟩
    exact (inv_mul_eq_one.mp hd1).symm
  have hZfixC : Z ≤ fixingSubgroup G (C : Set V) := by
    rw [hZS]
    apply Subgroup.commutator_le.mpr
    intro z hz s hs
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hinv : z⁻¹ • v ∈ C :=
      (IsInvariant.invariant (A := Z) (G := V) (H := C) (⟨z, hz⟩ : Z)⁻¹ v).mp hv
    have hsfix : s • (z⁻¹ • v) = z⁻¹ • v := hSfixC hinv ⟨s, hs⟩
    have hsinv : s⁻¹ • v = v := hSfixC hv ⟨s⁻¹, S.inv_mem hs⟩
    simp only [commutatorElement_def, mul_smul]
    rw [hsinv, hsfix, smul_inv_smul]
  have hNle : N ≤ U := by
    change commutatorAction Z V ≤ U
    rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le (K := U)).mpr
    rintro v ⟨z, w, rfl⟩
    have hw : w ∈ C ⊔ U := by rw [hcompF.sup_eq_top]; trivial
    let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
    obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hw
    have hzc : z • c = c :=
      (mem_fixingSubgroup_iff (M := G) (s := (C : Set V))).mp (hZfixC z.property) c hc
    have hzu : z • u ∈ U :=
      (IsInvariant.invariant (A := Z) (G := V) (H := U) z u).mp hu
    have heq : (c * u)⁻¹ * (z • (c * u)) = u⁻¹ * (z • u) := by
      rw [mul_inv_rev, smul_mul', hzc]
      group
    rw [heq]
    exact U.mul_mem (U.inv_mem hu) hzu
  have hNne : N ≠ ⊥ := by
    intro hn
    have htriv := actsTrivially_of_commutatorAction_eq_bot hn
    have hzfix : Z ≤ fixingSubgroup G (Set.univ : Set V) := by
      intro z hz
      rw [mem_fixingSubgroup_iff]
      exact fun v _ => htriv ⟨z, hz⟩ v
    exact hZne (le_antisymm (hzfix.trans h.action_faithful.le) bot_le)
  let D := (FixedPoints.subgroup Z V).subgroupOf U
  let E := N.subgroupOf U
  let _ : IsElementaryAbelian 2 U := RankOneThreeGroupAssembly.isElementaryAbelian_subgroup U
  let _ : IsInvariant S V (FixedPoints.subgroup Z V) :=
    fixedPoints_isInvariant_of_normalizing_actor S Z Subgroup.le_normalizer_of_normal
  let _ : IsInvariant S V N :=
    commutatorAction_isInvariant_of_normalizing_actor S Z Subgroup.le_normalizer_of_normal
  let _ : IsInvariant S U D := isInvariant_subgroupOf _ _
  let _ : IsInvariant S U E := isInvariant_subgroupOf _ _
  have hfixedU : Nat.card (FixedPoints.subgroup S U) = 2 := by
    rw [← Subgroup.card_map_of_injective (K := FixedPoints.subgroup S U) U.subtype_injective,
      fixedPoints_subgroup_map_subtype_eq_inf]
    exact hfixed
  have hcopZ : Nat.Coprime (Nat.card Z) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hZodd.symm.pow_right n
  have hcompZ : IsCompl (FixedPoints.subgroup Z V) N :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := Z)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y) hcopZ inferInstance
  have hDE : Disjoint D E := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro v hv
    apply Subtype.ext
    exact hcompZ.disjoint.le_bot ⟨hv.1, hv.2⟩
  have hEne : E ≠ ⊥ := by
    intro he
    have hm := congrArg (fun K : Subgroup U => K.map U.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hNle, Subgroup.map_bot] at hm
    exact hNne hm
  have hDbot : D = ⊥ :=
    (eq_bot_or_eq_bot_of_disjoint_of_fixed_card_two hS hfixedU D E hDE).resolve_right hEne
  have hUN : U = N := by
    apply le_antisymm _ hNle
    intro u hu
    have huTop : u ∈ FixedPoints.subgroup Z V ⊔ N := by rw [hcompZ.sup_eq_top]; trivial
    let _ : (FixedPoints.subgroup Z V).Normal := Subgroup.normal_of_isMulCommutative _
    obtain ⟨c, hc, n, hn, heq⟩ := Subgroup.mem_sup_of_normal_left.mp huTop
    have hcU : c ∈ U := by
      have heqc : c = u * n⁻¹ := by rw [← heq]; group
      rw [heqc]
      exact U.mul_mem hu (U.inv_mem (hNle hn))
    have hcD : (⟨c, hcU⟩ : U) ∈ D := hc
    have hc1 : c = 1 := congrArg Subtype.val (hDbot.le hcD)
    have hnu : n = u := by simpa [hc1] using heq
    exact hnu ▸ hn
  change IsInvariant W V U
  rw [hUN]
  exact commutatorAction_isInvariant_of_normalizing_actor W Z Subgroup.le_normalizer_of_normal

end Stellmacher.SectionOne

