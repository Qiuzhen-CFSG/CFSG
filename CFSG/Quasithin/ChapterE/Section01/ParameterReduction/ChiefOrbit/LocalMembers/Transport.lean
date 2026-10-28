module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Setup
public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.Generation

/-!
# Quotient assembly for the residual-orbit branch

The odd branch uses `K/O₂(K)`. E.1.10(6) puts its residual in the local E₁
subgroup modulo O₂(K), which the specified Sylow already contains.

For the component branch, quotient members in smaller overgroups of tau
lift by E.1.10(7) to actual ambient E-members of the same rank. Their residual
images, together with the Sylow image, cover the larger quotient. E.1.10(8)
then removes its solvable kernel under the full residual-action identity.
The theorem uses the proved stronger solvable-kernel form of E.1.10(8).
It applies in particular to the source kernel O∞(K_A).

These are conditional assembly results. Construction of the diagonal members,
their rank bounds, the quotient cover, and the prescribed local Sylow groups
is still required. No diagonal existence or generation conclusion is packaged
as an unconditional source theorem here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.10(6)--(8) and E.1.11, printed pp.211--213.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- E.1.8(2), with the actual ambient family member and its rank bound. -/
theorem map_eSubgroup_le_generationTarget {i n : ℕ} (hin : i ≤ n)
    (T : Sylow 2 G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (K : Subgroup G) (htau : tau (T : Subgroup G) A ≤ K) :
    (eSubgroup i ((T : Subgroup G).subgroupOf K) (A.subgroupOf K)).map K.subtype ≤
      generationTarget n T Ω := by
  let _ := hΩ.1 A hA
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro P hP
  apply map_le_iff_le_comap.mp
  have hp := (hP.inherit T A K hAT htau).mono hin
  exact (show P.map K.subtype ≤ eSubgroup n (T : Subgroup G) A from le_sSup hp).trans
    ((show eSubgroup n (T : Subgroup G) A ≤ eFamilySubgroup n (T : Subgroup G) Ω from
      le_iSup_of_le (⟨A, hA, hAT⟩ : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)})
        le_rfl).trans le_sup_left)

/-- E.1.10(6) closes the odd residual quotient branch, retaining O₂(K). -/
theorem le_generationTarget_of_odd_residual_quotient {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (K : Subgroup G) (R : Sylow 2 K)
    (hR : (R : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (htau : tau (T : Subgroup G) A ≤ K)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hodd : IsPGroup p ((pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K))))
    (hcomm : (pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)) =
      ⁅(pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)),
        (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))⁆) :
    K ≤ generationTarget n T Ω := by
  let _ := hΩ.1 A hA
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf
    ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans htau)
  let X := pResidual 2 K ⊔ pCore 2 K
  have hXmap : X.map (QuotientGroup.mk' (pCore 2 K)) =
      (pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)) := by
    simp [X, Subgroup.map_sup]
  have hX : IsPGroup p (X ⧸ (pCore 2 K).subgroupOf X) :=
    (hXmap.symm ▸ hodd).of_equiv (quotientSubgroupRangeEquiv X (pCore 2 K)).symm
  have hAR : A.subgroupOf K ≤ (R : Subgroup K) := by
    rw [hR]
    exact fun x hx => hAT hx
  have hRX : pResidual 2 K ≤ X := le_sup_left
  have hXE := odd_section_le_eSubgroup_one_sup hp R X (pCore 2 K) (A.subgroupOf K)
    le_sup_right hX hAR (by simpa only [hXmap] using hcomm)
  have hTM : (T : Subgroup G) ≤ generationTarget n T Ω :=
    (sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right
  have hRM : (R : Subgroup K) ≤ (generationTarget n T Ω).subgroupOf K := by
    rw [hR]
    exact fun x hx => hTM hx
  have hEM : eSubgroup 1 (R : Subgroup K) (A.subgroupOf K) ≤
      (generationTarget n T Ω).subgroupOf K := by
    rw [hR]
    exact map_le_iff_le_comap.mp
      (map_eSubgroup_le_generationTarget hn T hΩ hA hAT K htau)
  apply subgroupOf_eq_top.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top R]
  exact sup_le (hRX.trans (hXE.trans (sup_le hEM
    ((pCore_isPGroup.le_sylow_of_normal R).trans hRM)))) hRM

/-- The literal inclusion of a subgroup induces this map of kernel quotients. -/
def quotientInclusion {H K : Subgroup G} (hHK : H ≤ K)
    (Y : Subgroup K) [Y.Normal] :
    H ⧸ Y.comap (inclusion hHK) →* K ⧸ Y :=
  QuotientGroup.map _ Y (inclusion hHK) le_rfl

/-- E.1.10(7) followed by inheritance, transported to the larger quotient. -/
theorem quotient_member_residual_le_target_image {n : ℕ}
    (T : Sylow 2 G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    {H K : Subgroup G} (hHK : H ≤ K) (Y : Subgroup K) [Y.Normal]
    (R : Sylow 2 H) (hR : (R : Subgroup H) = (T : Subgroup G).subgroupOf H)
    (htau : tau (T : Subgroup G) A ≤ H)
    {I : Subgroup (H ⧸ Y.comap (inclusion hHK))}
    (hI : IsEMemberAt n
      ((R : Subgroup H).map (QuotientGroup.mk' (Y.comap (inclusion hHK))))
      ((A.subgroupOf H).map (QuotientGroup.mk' (Y.comap (inclusion hHK)))) I) :
    ((pResidual 2 I).map I.subtype).map (quotientInclusion hHK Y) ≤
      ((generationTarget n T Ω).subgroupOf K).map (QuotientGroup.mk' Y) := by
  let _ := hΩ.1 A hA
  let _ : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf
    ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans htau)
  have hAR : A.subgroupOf H ≤ (R : Subgroup H) := by
    rw [hR]
    exact fun x hx => hAT hx
  obtain ⟨D, hD, he⟩ := hI.exists_quotient_lift R (A.subgroupOf H)
    (Y.comap (inclusion hHK)) hAR
  have hDG : D.map H.subtype ≤ generationTarget n T Ω := by
    apply le_trans (map_mono (show D ≤ eSubgroup n
      ((T : Subgroup G).subgroupOf H) (A.subgroupOf H) from le_sSup (hR ▸ hD)))
    exact map_eSubgroup_le_generationTarget le_rfl T hΩ hA hAT H htau
  have hDK : D.map (inclusion hHK) ≤ (generationTarget n T Ω).subgroupOf K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDG (mem_map_of_mem H.subtype hx)
  rw [← he, map_map, map_map]
  change (pResidual 2 D).map
    ((QuotientGroup.mk' Y).comp ((inclusion hHK).comp D.subtype)) ≤ _
  rw [← map_map, ← map_map]
  exact map_mono ((map_mono (map_subtype_le (pResidual 2 D))).trans hDK)

/-- E.1.10(8) removes the solvable kernel after lifting each quotient member. -/
theorem le_generationTarget_of_solvable_quotient_member_cover {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (K : Subgroup G) (R : Sylow 2 K)
    (hR : (R : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (htau : tau (T : Subgroup G) A ≤ K)
    (Y : Subgroup K) [Y.Normal] [Group.IsSolvable Y]
    (hcomm : pResidual 2 K = ⁅pResidual 2 K, A.subgroupOf K⁆)
    {ι : Type*} (H : ι → Subgroup G) (hHK : ∀ i, H i ≤ K)
    (S : ∀ i, Sylow 2 (H i))
    (hS : ∀ i, (S i : Subgroup (H i)) = (T : Subgroup G).subgroupOf (H i))
    (hHtau : ∀ i, tau (T : Subgroup G) A ≤ H i)
    (I : ∀ i, Subgroup ((H i) ⧸ Y.comap (inclusion (hHK i))))
    (hI : ∀ i, IsEMemberAt n
      ((S i : Subgroup (H i)).map (QuotientGroup.mk' (Y.comap (inclusion (hHK i)))))
      ((A.subgroupOf (H i)).map (QuotientGroup.mk' (Y.comap (inclusion (hHK i))))) (I i))
    (hcover : (R : Subgroup K).map (QuotientGroup.mk' Y) ⊔
      (⨆ i, ((pResidual 2 (I i)).map (I i).subtype).map (quotientInclusion (hHK i) Y)) = ⊤) :
    K ≤ generationTarget n T Ω := by
  let _ := hΩ.1 A hA
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf
    ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans htau)
  let M := (generationTarget n T Ω).subgroupOf K
  have hTM : (T : Subgroup G) ≤ generationTarget n T Ω :=
    (sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right
  have hRM : (R : Subgroup K) ≤ M := by
    rw [hR]
    exact fun x hx => hTM hx
  have hEM : eSubgroup 1 (R : Subgroup K) (A.subgroupOf K) ≤ M := by
    rw [hR]
    exact map_le_iff_le_comap.mp
      (map_eSubgroup_le_generationTarget hn T hΩ hA hAT K htau)
  have hmap : M.map (QuotientGroup.mk' Y) = ⊤ := by
    apply top_unique
    rw [← hcover]
    refine sup_le (map_mono hRM) (iSup_le fun i => ?_)
    exact quotient_member_residual_le_target_image T hΩ hA hAT
      (hHK i) Y (S i) (hS i) (hHtau i) (hI i)
  have hMY : M ⊔ Y = ⊤ := by
    have hm := congrArg (Subgroup.comap (QuotientGroup.mk' Y)) hmap
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hm
  have hAR : A.subgroupOf K ≤ (R : Subgroup K) := by
    rw [hR]
    exact fun x hx => hAT hx
  have hg := sup_eSubgroup_eq_top_of_solvable_normal_supplement R
    (A.subgroupOf K) Y M hAR hRM hMY hcomm
  rw [sup_eq_left.mpr hEM] at hg
  exact subgroupOf_eq_top.mp hg

end CFSG.Quasithin.ChapterE.ChiefOrbit
