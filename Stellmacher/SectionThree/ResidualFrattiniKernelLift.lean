module
public import Stellmacher.TwoResidualIdentification
public import Stellmacher.SectionThree.LemmaThreeThree
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# Lifting residual containment through a proper normal local kernel

Let P be a finite solvable member of the Section Three local family over S.
Suppose C is normal in P and C joined with S is proper in P. If the two-core
of P normalizes L and the two-residual of P lies in L joined with C, then
that residual already lies in L. Both L and C remain subgroups of the
original ambient group, and their containments in P are explicit.

Unique maximality places C joined with S inside the unique maximal over S;
normality then puts C in its normal core. By (3.3), modulo the two-core
this normal core is the Frattini subgroup of the residual. Intersecting the
cover with that residual and applying Frattini nongeneration removes the
image of C. Thus the original residual lies in L joined with the two-core.
Because the two-core normalizes L, this join has two-group quotient by L.
Residual idempotence and the normal two-group extension theorem remove that
last supplement.

This is the kernel-removal step for the simultaneous opposite-Sylow
construction in Stellmacher (8.4), source (1)--(2) and (8), Journal of
Algebra 190 (1997), p.39 of `refs/files/stellmacher-n-group.pdf`. Its inputs
use only the proved Section Three (3.3)--(3.4) local structure; it does not
assume any Section Eight conclusion or quotient-faithfulness condition.
-/

namespace Stellmacher.SectionThree
open BenderSuzuki.External
universe u

private theorem le_of_le_sup_frattini
    {G : Type u} [Group G] [Finite G]
    (R L C : Subgroup G) [C.Normal]
    (hC : C ≤ (frattini R).map R.subtype) (hR : R ≤ L ⊔ C) : R ≤ L := by
  let D := L ⊓ R
  have hCR : C ≤ R := hC.trans (Subgroup.map_subtype_le _)
  have hcover : R ≤ D ⊔ C := by
    intro r hr
    obtain ⟨l, hl, c, hc, heq⟩ := Subgroup.mem_sup_of_normal_right.mp (hR hr)
    have hlR : l ∈ R := by
      have hh : l = r * c⁻¹ := by rw [← heq]; group
      rw [hh]
      exact R.mul_mem hr (R.inv_mem (hCR hc))
    rw [← heq]
    exact (D ⊔ C).mul_mem ((le_sup_left : D ≤ D ⊔ C) ⟨hl, hlR⟩)
      ((le_sup_right : C ≤ D ⊔ C) hc)
  have hsup : D ⊔ (frattini R).map R.subtype = R :=
    le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _))
      (hcover.trans (sup_le_sup le_rfl hC))
  have hinternal : D.subgroupOf R ⊔ frattini R = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_right,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hDtop : D.subgroupOf R = ⊤ := frattini_nongenerating hinternal
  exact (Subgroup.subgroupOf_eq_top.mp hDtop).trans inf_le_left

/-- A proper normal local kernel can be removed from this residual cover. -/
public theorem residual_le_of_le_sup_proper_normal_kernel
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (C L : Subgroup G) (hCP : C ≤ P) (hCn : (C.subgroupOf P).Normal)
    (hproper : C ⊔ S ≠ P) (hLP : L ≤ P)
    (hnorm : twoCoreAmbient P ≤ Subgroup.normalizer (L : Set G))
    (hcover : twoResidualAmbient P ≤ L ⊔ C) :
    twoResidualAmbient P ≤ L := by
  classical
  have hSP : S ≤ P := by
    obtain ⟨U, hU⟩ := hP.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  obtain ⟨M, hM, hSM, huniq⟩ := hP.2
  have hCM : C ≤ M.map P.subtype := le_sup_left.trans
    (le_unique_maximal_over huniq le_sup_right (sup_le hCP hSP) hproper)
  let N := M.normalCore
  let CP := C.subgroupOf P
  let LP := L.subgroupOf P
  let _ : CP.Normal := hCn
  have hCPM : CP ≤ M := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hCM
  have hCN : CP ≤ N := Subgroup.normal_le_normalCore.mpr hCPM
  have hB : IsCoatom M ∧ S.subgroupOf P ≤ M ∧
      ∀ M' : Subgroup P, IsCoatom M' → S.subgroupOf P ≤ M' → M' = M := by
    refine ⟨hM, ?_, ?_⟩
    · apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
      rw [Subgroup.map_subgroupOf_eq_of_le hSP]
      exact hSM
    · intro M' hM' hS'
      exact huniq M' hM' (by rw [← Subgroup.map_subgroupOf_eq_of_le hSP]; exact Subgroup.map_mono hS')
  have hN : N ≤ M ∧ N.Normal ∧
      ∀ A : Subgroup P, A.Normal → A ≤ M → A ≤ N := by
    refine ⟨M.normalCore_le, inferInstance, ?_⟩
    intro A hn ha
    exact @Subgroup.normal_le_normalCore P _ M A hn |>.mpr ha
  have h33 := lemma_three_three S h P hP M N hB hN hsolv
  let Q := pCore 2 P
  let q : P →* P ⧸ Q := QuotientGroup.mk' Q
  let R := twoResidualAmbient (⊤ : Subgroup (P ⧸ Q))
  let RP := twoResidualSubgroup P
  have hRPmap : RP.map q = R := by
    have hRP : RP = hktPResidual 2 P := twoResidualSubgroup_eq_hktPResidual' P
    rw [hRP]
    exact (map_hktPResidual_quotient 2 Q).trans
      (twoResidualAmbient_top_eq_hktPResidual (Q := P ⧸ Q)).symm
  have hCPphi : CP.map q ≤ (frattini R).map R.subtype := by
    have hh := Subgroup.map_mono (f := q) hCN
    rw [h33.part_c] at hh
    exact hh
  have hRPcover : RP ≤ LP ⊔ CP := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLP,
      Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hcover
  have hRcover : R ≤ LP.map q ⊔ CP.map q := by
    rw [← hRPmap, ← Subgroup.map_sup]
    exact Subgroup.map_mono hRPcover
  let _ : (CP.map q).Normal := hCn.map q (QuotientGroup.mk'_surjective Q)
  have hRL : R ≤ LP.map q := le_of_le_sup_frattini R (LP.map q) (CP.map q) hCPphi hRcover
  have hRPQ : RP ≤ LP ⊔ Q := by
    have hle : RP ≤ (LP.map q).comap q := Subgroup.map_le_iff_le_comap.mp
      (hRPmap.symm ▸ hRL)
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk'] using hle
  have hRQ : twoResidualAmbient P ≤ L ⊔ twoCoreAmbient P := by
    have hh := Subgroup.map_mono (f := P.subtype) hRPQ
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLP] at hh
  have hLn : (L.subgroupOf (L ⊔ twoCoreAmbient P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le L.le_normalizer hnorm)
  have htwo : IsPGroup 2 (twoCoreAmbient P) :=
    (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hh := twoResidualAmbient_le_left_of_le_sup L (twoCoreAmbient P)
    (twoResidualAmbient P) hLn htwo hRQ
  have hidem : twoResidualAmbient (twoResidualAmbient P) = twoResidualAmbient P := by
    let R0 := twoResidualAmbient P
    have htop : twoResidualAmbient (⊤ : Subgroup R0) = ⊤ := by
      rw [twoResidualAmbient_top_eq_hktPResidual]
      exact twoResidualAmbient_has_top_twoResidual P
    have hmap := map_twoResidualAmbient_of_subgroup_image
      (⊤ : Subgroup R0) R0.subtype R0 (by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap.symm
  rwa [hidem] at hh
end Stellmacher.SectionThree
