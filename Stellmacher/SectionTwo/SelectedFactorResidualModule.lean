module
public import Stellmacher.SectionTwo.QuotientModuleTransport
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupAction.NormalizingActor

/-!
# Identifying a selected factor's residual module

Keep the Section Two module `V = ⟨Ω₁(Z(S))^G⟩` and its named quotient
conjugation action. Let `V ≤ B ≤ K ≤ L`. Suppose the quotient image of `K`
contains a one-seven factor `D`, normal in the image of `L`. If the actual
core-residual commutator of `K` has order four, it equals the ambient module
of `D` and is normalized by `L`.

The explicit containment puts the normal two-subgroup `V` inside `O₂(K)`.
The original Baumann-closure theorem remains a wrapper: its Sylow condition
puts `V` inside `B`, yielding the required containment.
The derived subgroup of `D` has order three; its image in
a two-group quotient is trivial, so residual functoriality puts it in the
image of `O²(K)`. Lifting these actors under the original quotient action
puts their four-element commutator module in the actual core-residual
commutator. The one-seven factor identifies the derived and full action
commutators; equal cardinalities then give equality. Finally, normalization
of `D` by the image of `L` preserves the same action module and transports
back to normalization of the ambient residual commutator.

This is the selected `W₁ = [O₂(E₁),O²(E₁)]` module identification in
Stellmacher (6.1), Journal of Algebra 190 (1997), p.30; the explicit
containment form also applies to the original module and the partner
Baumann subgroup in (4.6), p.26,
`refs/latex/stellmacher-n-group.tex`. Its order-four hypothesis remains
explicit, and the same quotient action is used in every construction.
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

/-- A selected one-seven factor identifies an actual four-element
core-residual commutator and makes it invariant under the supplied overgroup. -/
public theorem selected_factor_residual_module_of_containment
    {G barG : Type u} [Group G] [Finite G] [Group barG] [Finite barG]
    (h : Hypotheses G) (S : Sylow 2 G)
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B L : Subgroup G)
    (hVB : vSubgroup S ≤ B)
    (K : Subgroup G) (hBK : B ≤ K) (hKL : K ≤ L)
    (D : Subgroup barG) (hDK : D ≤ K.map q)
    (hDn : (D.subgroupOf (L.map q)).Normal)
    (hW : Nat.card (⁅twoCoreAmbient K, twoResidualAmbient K⁆ : Subgroup G) = 4) :
    letI := quotientConjugationAction S q hq hker
    SectionOne.IsOneSevenFactor (V := vSubgroup S) D →
      ⁅twoCoreAmbient K, twoResidualAmbient K⁆ =
        ambientCommutator (D.comap q) (vSubgroup S) ∧
      L ≤ Subgroup.normalizer
        ((⁅twoCoreAmbient K, twoResidualAmbient K⁆ : Subgroup G) : Set G) := by
  let _ := quotientConjugationAction S q hq hker
  intro hD
  let V := vSubgroup S
  let W := ⁅twoCoreAmbient K, twoResidualAmbient K⁆
  let F := (commutator D).map D.subtype
  have hVn : V.Normal := Subgroup.normalClosure_normal
  have hVp : IsPGroup 2 V := by
    let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
    exact IsElementaryAbelian.isPGroup 2 V
  have hVK : V ≤ K := hVB.trans hBK
  have hVKcore : V ≤ twoCoreAmbient K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVK]
    exact Subgroup.map_mono (le_sSup ⟨hVn.subgroupOf K,
      hVp.comap_of_injective K.subtype K.subtype_injective⟩)
  have hFcard : Nat.card F = 3 := hD.2.1.2.1
  have hF3 : IsPGroup 3 F := IsPGroup.of_card (n := 1) (by simpa using hFcard)
  have hFK : F ≤ K.map q := (Subgroup.map_subtype_le _).trans hDK
  have hFR : F ≤ (twoResidualAmbient K).map q := by
    rw [map_twoResidualAmbient_of_subgroup_image K q (K.map q) rfl]
    exact threeSubgroup_le_twoResidualAmbient F (K.map q) hFK hF3
  have hFleW : (commutatorAction F V).map V.subtype ≤ W := by
    rw [Subgroup.map_le_iff_le_comap, commutatorAction_eq_closure]
    apply (Subgroup.closure_le (K := W.comap V.subtype)).mpr
    rintro _ ⟨a, v, rfl⟩
    obtain ⟨r, hr, hra⟩ := hFR a.property
    change (v : G)⁻¹ * (((a : barG) • v : V) : G) ∈ W
    rw [← hra, quotientConjugationAction_smul_coe S q hq hker]
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      (Subgroup.commutator_mem_commutator (hVKcore (V.inv_mem v.property)) hr)
  have hmap : (commutatorAction D V).map V.subtype =
      ambientCommutator (D.comap q) V :=
    quotientConjugationAction_commutator_map S q hq hker D
  have hMleW : ambientCommutator (D.comap q) V ≤ W := by
    rw [← hmap, SectionOne.oneSevenFactor_full_commutator_eq_derived D hD]
    exact hFleW
  have hMcard : Nat.card (ambientCommutator (D.comap q) V) = 4 := by
    rw [← hmap, Subgroup.card_map_of_injective V.subtype_injective]
    exact hD.2.2.1
  have hWeq : W = ambientCommutator (D.comap q) V :=
    (Subgroup.eq_of_le_of_card_ge hMleW (by rw [hMcard]; exact hW.le)).symm
  refine ⟨hWeq, ?_⟩
  have hDL : D ≤ L.map q := hDK.trans (Subgroup.map_mono hKL)
  have hLD : L.map q ≤ Subgroup.normalizer (D : Set barG) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mp hDn
  have hInv := commutatorAction_isInvariant_of_normalizing_actor (V := V) (L.map q) D hLD
  change L ≤ Subgroup.normalizer (W : Set G)
  rw [hWeq, ← hmap, Subgroup.le_normalizer_iff]
  intro l hl w hw
  obtain ⟨v, hv, rfl⟩ := hw
  have hi := (hInv.invariant ⟨q l, Subgroup.mem_map_of_mem q hl⟩ v).mp hv
  refine ⟨q l • v, hi, ?_⟩
  exact quotientConjugationAction_smul_coe S q hq hker l v

/-- A selected one-seven factor identifies an actual four-element
core-residual commutator and makes it invariant under the Baumann closure. -/
public theorem selected_factor_residual_module
    {G barG : Type u} [Group G] [Finite G] [Group barG] [Finite barG]
    (h : Hypotheses G) (S : Sylow 2 G)
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B L : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hL : L = Subgroup.normalClosure (B : Set G))
    (PB : Sylow 2 L) (hPB : (PB : Subgroup L).map L.subtype = B)
    (K : Subgroup G) (hBK : B ≤ K) (hKL : K ≤ L)
    (D : Subgroup barG) (hDK : D ≤ K.map q)
    (hDn : (D.subgroupOf (L.map q)).Normal)
    (hW : Nat.card (⁅twoCoreAmbient K, twoResidualAmbient K⁆ : Subgroup G) = 4) :
    letI := quotientConjugationAction S q hq hker
    SectionOne.IsOneSevenFactor (V := vSubgroup S) D →
      ⁅twoCoreAmbient K, twoResidualAmbient K⁆ =
        ambientCommutator (D.comap q) (vSubgroup S) ∧
      L ≤ Subgroup.normalizer
        ((⁅twoCoreAmbient K, twoResidualAmbient K⁆ : Subgroup G) : Set G) := by
  let V := vSubgroup S
  have hVn : V.Normal := Subgroup.normalClosure_normal
  have hVp : IsPGroup 2 V := by
    let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
    exact IsElementaryAbelian.isPGroup 2 V
  have hZB : zSubgroup S ≤ B := by
    intro z hz
    obtain ⟨hzS, _, hzcent⟩ := (mem_omegaOneCenterAmbient_iff (S : Subgroup G) z).mp hz
    rw [hB]
    refine ⟨hzS, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hxJ := (mem_omegaOneCenterAmbient_iff _ x).mp hx |>.1
    have hJS : elementaryAbelianMaxJ (S : Subgroup G) ≤ (S : Subgroup G) :=
      sSup_le fun _ ha => ha.1
    exact hzcent x (hJS hxJ)
  have hVL : V ≤ L := by
    rw [hL]
    exact Subgroup.normalClosure_mono hZB
  have hVLn : (V.subgroupOf L).Normal := hVn.subgroupOf L
  have hVLp : IsPGroup 2 (V.subgroupOf L) :=
    hVp.comap_of_injective L.subtype L.subtype_injective
  have hVB : V ≤ B := by
    rw [← hPB, ← Subgroup.map_subgroupOf_eq_of_le hVL]
    exact Subgroup.map_mono (hVLp.le_sylow_of_normal PB)
  exact selected_factor_residual_module_of_containment
    h S q hq hker B L hVB K hBK hKL D hDK hDn hW

end Stellmacher.SectionTwo
