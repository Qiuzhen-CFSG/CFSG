module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Theory.GroupTheory.FiveSixteenTwoCentralizer
public import Theory.GroupTheory.FiveNormalizedThreeSubgroup

/-!
# Excluding a five-normalized three-subgroup at the large terminal endpoint

The second local group's action on the residual Frattini quotient has
sixteen points and two-group kernel. Thus every two-subgroup centralizing
the specified five-group lies in the second core. Normalizer confinement
therefore bounds its fixed points in every ambient two-subgroup by four.

Apply this to the two-core of the centralizer of a five-fixed involution y.
The involution belongs to that core and is fixed by the whole centralizer.
If a nontrivial three-subgroup T is normalized fixed-point-freely by A,
the Frobenius group T A acts on this core. Wielandt's fixed-point formula
and orbit counting modulo three force T to centralize the core. The
characteristic-two hypothesis then forces T = 1.

This proves the structural exclusion in Thompson VI, printed p.630, from
the actual terminal data. No full-core Frattini bound, all-prime N condition,
or odd-local solvability assumption is needed. The result applies to any
five-fixed involution once the given fixed-core cardinality and normalizer
confinement hold; the additional noncyclic-alternative hypotheses are not
needed for this step.
-/

universe u

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven Subgroup

/-- Every two-subgroup centralizing the confined five-group lies in the
second local core. The residual Frattini action detects any escape. -/
public theorem LargeTerminalContext.two_subgroup_le_core_of_centralizes_five
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (D : Subgroup G) (hD : IsPGroup 2 D)
    (hDA : D ≤ centralizer (A : Set G)) : D ≤ twoCoreIn ctx.second := by
  obtain ⟨z, hz, hgen, _, _, _⟩ := ctx.involution_centralizer_core
  let C := centralizer ({z} : Set G)
  let R := ctx.firstResidual.subgroupOf C
  let Q := pCore 2 C
  have hPC : ctx.second ≤ C := ctx.second_le_residual_normalizer.trans
    (ctx.residual_normalizer_le_involution_centralizer z hz hgen)
  have hAC : A ≤ C := hAP.trans hPC
  have hDC : D ≤ C := (hDA.trans (Subgroup.centralizer_le_normalizer _)).trans (hN.trans hPC)
  obtain ⟨_, hRn⟩ := ctx.first_residual_normal_of_large_card hS z hz hgen
  let _ : R.Normal := hRn.2
  have hRQ : R ≤ Q := by
    have hh : ctx.firstResidual ≤ twoCoreIn C := by
      obtain ⟨w, _, hw, hlo, _, _⟩ := ctx.involution_centralizer_core
      have hc : C = centralizer (omegaOneCenter (S : Subgroup G) : Set G) := by
        change centralizer ({z} : Set G) = _
        rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
      rwa [← centralizer_closure, ← zpowers_eq_closure, hw, ← hc] at hlo
    intro r hr
    obtain ⟨j, hj, hjr⟩ := hh hr
    exact (show j = r from Subtype.ext hjr) ▸ hj
  have hRcard : Nat.card R = 512 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRn.1).toEquiv).trans ctx.first_residual_structure.1
  have hQcard : Nat.card Q = 1024 :=
    (ctx.involution_centralizer_core_eq_at_generator hS z hgen).2
  have hi : (R.subgroupOf Q).index = 2 := by
    have hh := (R.subgroupOf Q).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv, hRcard, hQcard] at hh
    omega
  let V := R ⧸ frattini R
  let ρ : C →* MulAut V := (quotientAut (frattini R)).comp MulAut.conjNormal
  have hk : IsPGroup 2 ρ.ker := frattini_kernel_isPGroup_of_index_two_in_core
    (ctx.localStructure C (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)).2 R hRQ hi
  have hkQ : ρ.ker ≤ Q := le_sSup ⟨inferInstance, hk⟩
  let e : R ≃* ctx.firstResidual := subgroupOfEquivOfLe hRn.1
  have hPhiMap : (frattini R).map e.toMonoidHom = frattini ctx.firstResidual := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
    · intro x hx
      refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      exact frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hx
  have hV : Nat.card V = 16 := by
    exact (Nat.card_congr (QuotientGroup.congr _ _ e hPhiMap).toEquiv).trans
      ctx.first_residual_frattini_structure.2
  have hDA' : D.subgroupOf C ≤ centralizer (A.subgroupOf C : Set C) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp (hDA hd) a ha)
  have hDk := two_subgroup_le_kernel_of_centralizes_five ρ hk hV
    (A.subgroupOf C) (D.subgroupOf C)
    ((Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA)
    (hD.of_equiv (subgroupOfEquivOfLe hDC).symm) hDA'
  intro d hd
  have hdQ : d ∈ twoCoreIn C := mem_map.mpr ⟨⟨d, hDC hd⟩, hkQ (hDk hd), rfl⟩
  rwa [(ctx.involution_centralizer_core_eq_at_generator hS z hgen).1] at hdQ

/-- The local four-fixed bound controls the five-fixed subgroup in every
ambient two-subgroup, including other involution-centralizer cores. -/
public theorem LargeTerminalContext.five_fixed_two_subgroup_card_le_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (K : Subgroup G) (hK : IsPGroup 2 K) :
    Nat.card ((centralizer (A : Set G)).subgroupOf K) ≤ 4 := by
  let F := (centralizer (A : Set G)).subgroupOf K
  let D := F.map K.subtype
  have hD : IsPGroup 2 D := (hK.to_subgroup F).map K.subtype
  have hDA : D ≤ centralizer (A : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hDQ := ctx.two_subgroup_le_core_of_centralizes_five hS A hA hAP hN D hD hDA
  let J := (centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)
  let f : F →* J := {
    toFun x := ⟨⟨x.val, hDQ (mem_map_of_mem K.subtype x.property)⟩, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : J => (v.val : G)) he
  exact (Nat.card_le_card_of_injective f hf).trans_eq hcard

/-- A three-subgroup centralizing a five-fixed involution and normalized
fixed-point-freely by the five-group is trivial at the upper terminal endpoint. -/
public theorem LargeTerminalContext.three_subgroup_eq_bot_of_five_fixed_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hyA : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2)
    (T : Subgroup G) (hT : IsPGroup 3 T)
    (hTC : T ≤ centralizer ({y} : Set G))
    (hAT : A ≤ normalizer (T : Set G))
    (hfixed : T ⊓ centralizer (A : Set G) = ⊥) : T = ⊥ := by
  let C := centralizer ({y} : Set G)
  let Q := pCore 2 C
  let Ac := A.subgroupOf C
  let Tc := T.subgroupOf C
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hyA a ha)
  have hAQ : Nat.card Ac = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA
  have hTc : IsPGroup 3 Tc := hT.of_equiv (subgroupOfEquivOfLe hTC).symm
  have hATc : Ac ≤ normalizer (Tc : Set C) := by
    intro a ha
    exact le_normalizer_comap C.subtype (hAT ha)
  have hfixedc : Tc ⊓ centralizer (Ac : Set C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro t ht
    apply Subtype.ext
    have htA : (t : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact congrArg C.subtype (mem_centralizer_iff.mp ht.2 ⟨a, hAC ha⟩ ha)
    exact show (t : G) ∈ (⊥ : Subgroup G) from hfixed ▸ ⟨ht.1, htA⟩
  have hyQ : y ∈ twoCoreIn C := central_involution_mem_twoCore C y
    (mem_centralizer_singleton_iff.mpr rfl) le_rfl
    (by rw [← hy2]; exact pow_orderOf_eq_one y)
  obtain ⟨q, hq, hqy⟩ := hyQ
  change (q : G) = y at hqy
  let yq : Q := ⟨q, hq⟩
  have hyqne : yq ≠ 1 := by
    intro he
    have hy1 : y = 1 := hqy.symm.trans (congrArg (fun x : Q => (x.val : G)) he)
    simp [hy1] at hy2
  have hyqc : (yq : C) ∈ center C := by
    rw [mem_center_iff]
    intro c
    apply Subtype.ext
    change (c : G) * (q : G) = (q : G) * (c : G)
    rw [hqy]
    exact mem_centralizer_singleton_iff.mp c.property
  let F := (centralizer (Ac : Set C)).subgroupOf Q
  let K := twoCoreIn C
  let E := (centralizer (A : Set G)).subgroupOf K
  have hEK : Nat.card E ≤ 4 := ctx.five_fixed_two_subgroup_card_le_four hS A hA hAP hN
    hcard K (pCore_isPGroup.map C.subtype)
  have hFA (f : F) : (f.val.val : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact congrArg C.subtype (mem_centralizer_iff.mp f.property ⟨a, hAC ha⟩ ha)
  let j : F →* E := {
    toFun f := ⟨⟨f.val.val, mem_map_of_mem C.subtype f.val.property⟩, hFA f⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x x' he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun f : E => (f.val : G)) he
  have hsmall : Nat.card F ≤ 4 := (Nat.card_le_card_of_injective j hj).trans hEK
  have hbot : Tc = ⊥ := three_subgroup_eq_bot_of_small_five_fixed Q pCore_isPGroup
    (ctx.localStructure C (Theory.GroupTheory.isTwoLocal_involution_centralizer hy2)).2
    yq hyqne hyqc Ac Tc hAQ hTc hATc hfixedc hsmall
  rw [← map_subgroupOf_eq_of_le hTC]
  change Tc.map C.subtype = ⊥
  rw [hbot, Subgroup.map_bot]
end Stellmacher.Recognition
