module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.QuasisimpleFactor.OuterSylow
public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace

/-!
# Centralizers in the remaining local action case

For a faithful finite-dimensional binary representation, failure of local
normalization in E.4.2 forces characteristic two. More precisely, if
Q = O₂(H) and P = W_m(Q), then C_H(P) ≤ Q.

Put U = C_V(P) and let N be its pointwise kernel in H. The kernel-image
theorem puts F*(H/Q) in the image of N. By the P × Q fixed-space lemma,
C_H(P) ∩ N is a normal two-subgroup. Thus the images of C_H(P) and N in
H/Q commute, and self-centralization of F*(H/Q) gives C_H(P) ≤ NQ.
The kernel and image of C_H(P) in H/N are both two-groups, so C_H(P) ≤ Q.
The same argument with P = Q supplies the characteristic-two conclusion.

These are structural reductions for the nonnormal outer-Sylow branch.
Preservation of the later weak fixed spaces still requires control of the
remaining outer action. Neither centralizer containment proves normality
of the local factor times the Sylow image or identifies the factor with
the two-residual.

Source context: Aschbacher–Smith, combined manuscript of 1 March 2004,
E.4.2, printed p.241 (PDF p.252); the P × Q lemma in B.1.10–11,
printed pp.72–73.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound.LocalControl
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem centralizer_normal_two_subgroup_le_of_fitting_fixed_kernel_image
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    (hF : generalizedFitting (G ⧸ pCore 2 G) ≤
      (subspaceKernel ρ (fixedSpace ρ P) ⊤).map
        (QuotientGroup.mk' (pCore 2 G))) :
    centralizer (P : Set G) ≤ pCore 2 G := by
  let Q := pCore 2 G
  let C := centralizer (P : Set G)
  let N := subspaceKernel ρ (fixedSpace ρ P) ⊤
  let q := QuotientGroup.mk' Q
  let F := generalizedFitting (G ⧸ Q)
  let : N.Normal := by
    rw [show N = (invariantActionHom ρ (fixedSpace ρ P)
      (fixedSpace_stable_of_normal ρ P)).ker from
        (invariantActionHom_ker ρ _ _).symm]
    infer_instance
  have hCNp : IsPGroup 2 (C ⊓ N : Subgroup G) :=
    isPGroup_of_commuting_fixes_fixedSpace ρ hf P (C ⊓ N) hP
      (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (show C ⊓ N ≤ centralizer (P : Set G) from inf_le_left)))
      inf_le_right
  have hCNQ : C ⊓ N ≤ Q := le_sSup ⟨inferInstance, hCNp⟩
  have hcomm : ⁅C.map q, N.map q⁆ = ⊥ := by
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using (commutator_le_inf C N).trans hCNQ
  have hCF : C.map q ≤ centralizer (F : Set (G ⧸ Q)) :=
    (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (centralizer_le hF)
  have hCN : C ≤ N ⊔ Q := by
    have hc : C.map q ≤ N.map q := hCF.trans
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le.trans hF)
    have hc' := map_le_iff_le_comap.mp hc
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hc'
  let f : C →* G ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hker : IsPGroup 2 f.ker := by
    have he : f.ker = N.subgroupOf C := by
      ext x
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact hCNp.of_injective
      ({ toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
         map_one' := rfl
         map_mul' _ _ := rfl } : N.subgroupOf C →* (C ⊓ N : Subgroup G))
      (fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : (C ⊓ N : Subgroup G) => (z : G)) h)))
  have hpre : C ≤ (Q.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk', sup_comm] using hCN
  have htop : (Q.map (QuotientGroup.mk' N)).comap f = ⊤ := by
    apply top_unique
    intro c _
    exact hpre c.property
  have hp := (pCore_isPGroup (p := 2) (G := G)).map (QuotientGroup.mk' N)
    |>.comap_of_ker_isPGroup f hker
  rw [htop] at hp
  have hC : IsPGroup 2 C := hp.of_equiv Subgroup.topEquiv
  exact le_sSup ⟨inferInstance, hC⟩

/-- In a faithful finite-dimensional binary action, an overgroup with quasisimple
local factor which fails to normalize the earlier weak subgroup has characteristic
two. This reduces the remaining outer-action problem; it is not tail invariance. -/
theorem centralizer_twoCore_le_of_quasisimple_not_normalizing
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    {k j m : ℕ} (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G))
    [IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H))] :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  apply centralizer_normal_two_subgroup_le_of_fitting_fixed_kernel_image (ρ.comp H.subtype)
    (hf.comp H.subtype_injective) (pCore 2 H) pCore_isPGroup
  apply (coreFixedSpace_kernel_image_contains_factor ρ T H hTH hjm hmk hn).trans
  apply map_mono
  intro h hh
  refine ⟨mem_top _, ?_⟩
  intro v hv
  apply hh.2 v
  have hv' : v ∈ fixedSpace ρ ((pCore 2 H).map H.subtype) := by
    rwa [fixedSpace_comp_map] at hv
  exact (fixedSpace_antitone ρ (weakSubgroup_le _ _ _)) hv'

/-- The weak subgroup inside the local two-core already has its entire local
centralizer in that two-core. Normality and centralization are intrinsic to H.
This strengthens the characteristic-two reduction without asserting tail invariance. -/
theorem centralizer_coreWeakSubgroup_le_twoCore_of_quasisimple_not_normalizing
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    {k j m : ℕ} (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G))
    [IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H))] :
    centralizer ((weakSubgroup (fixedSpaceFamily ρ (k + 1)) m
      ((pCore 2 H).map H.subtype)).subgroupOf H : Set H) ≤ pCore 2 H := by
  let P := weakSubgroup (fixedSpaceFamily ρ (k + 1)) m ((pCore 2 H).map H.subtype)
  have hPH : P ≤ H := (weakSubgroup_le _ _ _).trans (map_subtype_le _)
  have hHP : H ≤ normalizer (P : Set G) := by
    apply le_trans _ (weakSubgroup_normalizer ρ (k + 1) m _)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (le_normalizer_map (H := pCore 2 H) H.subtype)
  let : (P.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hPH).mpr hHP
  have hP : IsPGroup 2 (P.subgroupOf H) :=
    ((pCore_isPGroup.map H.subtype).to_le (weakSubgroup_le _ _ _)).comap_subtype
  apply centralizer_normal_two_subgroup_le_of_fitting_fixed_kernel_image
    (ρ.comp H.subtype) (hf.comp H.subtype_injective) (P.subgroupOf H) hP
  apply (coreFixedSpace_kernel_image_contains_factor ρ T H hTH hjm hmk hn).trans
  apply map_mono
  intro h hh
  refine ⟨mem_top _, ?_⟩
  intro v hv
  apply hh.2 v
  rwa [fixedSpace_comp_map, map_subgroupOf_eq_of_le hPH] at hv

end CFSG.Quasithin.ChapterE.ValueBound.LocalControl
