module
public import Stellmacher.SectionTwo.SelectedFactorResidualModule

/-!
# The residual module of a raw selected natural factor

Keep the original Section Two module V and its exact quotient action. Let
D be a one-seven factor in a subgroup N of that quotient, with the image
of D contained in the image of K. If V lies in K and the actual
core-residual commutator of K has order four, that commutator is precisely
the ambient image of the raw module [V,D]. No one-seven factor property
in the entire quotient is assumed.

The derived subgroup of D has order three, so its ambient image lies in
the image of the two-residual of K. Also V lies in the two-core of K.
Lifting these derived actors puts their action commutator inside the actual
core-residual module. The raw factor identifies its full and derived action
commutators and supplies cardinality four, so containment gives equality.
This retains the exact original factor required by the (2.5) argument in
Stellmacher (4.6), journal p26; refs/latex/stellmacher-n-group.tex.
-/

open scoped commutatorElement
namespace Stellmacher.SectionTwo
universe u

private theorem threeSubgroup_le_twoResidualAmbient
    {X : Type*} [Group X] [Finite X] (A J : Subgroup X)
    (hAJ : A ≤ J) (hA : IsPGroup 3 A) : A ≤ twoResidualAmbient J := by
  let AJ := A.subgroupOf J
  have hAJ3 : IsPGroup 3 AJ := hA.comap_of_injective J.subtype J.subtype_injective
  have hAJR : AJ ≤ twoResidualSubgroup J := by
    intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    rintro N ⟨hN, n, hn⟩
    let _ : N.Normal := hN
    let f := QuotientGroup.mk' N
    have hquot : IsPGroup 2 (J ⧸ N) := IsPGroup.of_card (by
      simpa only [Subgroup.index_eq_card] using hn)
    have himg3 : IsPGroup 3 (AJ.map f) := hAJ3.map f
    have himg2 : IsPGroup 2 (AJ.map f) := hquot.to_subgroup (AJ.map f)
    have himg : AJ.map f = ⊥ := disjoint_self.mp
      (IsPGroup.disjoint_of_ne 3 2 (by decide) (AJ.map f) (AJ.map f) himg3 himg2)
    have hker := (Subgroup.map_eq_bot_iff AJ).mp himg hx
    simpa only [f, QuotientGroup.ker_mk'] using hker
  calc
    A = AJ.map J.subtype := (Subgroup.map_subgroupOf_eq_of_le hAJ).symm
    _ ≤ (twoResidualSubgroup J).map J.subtype := Subgroup.map_mono hAJR
    _ = twoResidualAmbient J := rfl

public theorem selected_raw_factor_residual_module
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    (h : Hypotheses G) (S : Sylow 2 G)
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (K : Subgroup G) (hVK : vSubgroup S ≤ K)
    (N : Subgroup X) (D : Subgroup N)
    (hDK : D.map N.subtype ≤ K.map q)
    (hW : Nat.card (⁅twoCoreAmbient K, twoResidualAmbient K⁆ : Subgroup G) = 4) :
    letI := quotientConjugationAction S q hq hker
    SectionOne.IsOneSevenFactor (V := vSubgroup S) D →
      ⁅twoCoreAmbient K, twoResidualAmbient K⁆ =
        (commutatorAction D (vSubgroup S)).map (vSubgroup S).subtype := by
  let _ := quotientConjugationAction S q hq hker
  intro hD
  let V := vSubgroup S
  change V ≤ K at hVK
  let W := ⁅twoCoreAmbient K, twoResidualAmbient K⁆
  let F := (commutator D).map D.subtype
  let FA := F.map N.subtype
  have hVn : V.Normal := Subgroup.normalClosure_normal
  have hVp : IsPGroup 2 V := by
    let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
    exact IsElementaryAbelian.isPGroup 2 V
  have hVKcore : V ≤ twoCoreAmbient K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVK]
    exact Subgroup.map_mono (le_sSup ⟨hVn.subgroupOf K,
      hVp.comap_of_injective K.subtype K.subtype_injective⟩)
  have hFcard : Nat.card F = 3 := hD.2.1.2.1
  have hF3 : IsPGroup 3 F := IsPGroup.of_card (n := 1) (by simpa using hFcard)
  have hFAK : FA ≤ K.map q := (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans hDK
  have hFR : FA ≤ (twoResidualAmbient K).map q := by
    rw [map_twoResidualAmbient_of_subgroup_image K q (K.map q) rfl]
    exact threeSubgroup_le_twoResidualAmbient FA (K.map q) hFAK (hF3.map N.subtype)
  have hFleW : (commutatorAction F V).map V.subtype ≤ W := by
    rw [Subgroup.map_le_iff_le_comap, commutatorAction_eq_closure]
    apply (Subgroup.closure_le (K := W.comap V.subtype)).mpr
    rintro _ ⟨a, v, rfl⟩
    have ha : ((a : N) : X) ∈ FA := Subgroup.mem_map_of_mem N.subtype a.property
    obtain ⟨r, hr, hra⟩ := hFR ha
    change (v : G)⁻¹ * (((((a : N) : X)) • v : V) : G) ∈ W
    rw [← hra, quotientConjugationAction_smul_coe S q hq hker]
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      (Subgroup.commutator_mem_commutator (hVKcore (V.inv_mem v.property)) hr)
  have hMleW : (commutatorAction D V).map V.subtype ≤ W := by
    rw [SectionOne.oneSevenFactor_full_commutator_eq_derived D hD]
    exact hFleW
  have hMcard : Nat.card ((commutatorAction D V).map V.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective V.subtype_injective]
    exact hD.2.2.1
  exact (Subgroup.eq_of_le_of_card_ge hMleW (by rw [hMcard]; exact hW.le)).symm

end Stellmacher.SectionTwo
