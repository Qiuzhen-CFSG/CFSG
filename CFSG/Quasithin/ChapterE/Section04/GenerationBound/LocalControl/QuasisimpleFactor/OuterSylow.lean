module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.QuasisimpleFactor.KernelImage
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Local tail invariance when the outer Sylow subgroup is normal

Write Hbar = H/O₂(H), F = F*(Hbar), and Tbar for the image of T in Hbar.
The preceding kernel-image theorem proves F ≤ Kbar. If F Tbar is normal
in Hbar, then Kbar Tbar = Kbar (F Tbar) is normal. Pulling back through
the quotient and using O₂(H) ≤ T proves that KT is normal inside H.
The Frattini argument in CoreSpace now gives invariance of every later
weak fixed space.

In particular this proves the branch where Hbar/F is a two-group: Sylow
surjectivity gives F Tbar = Hbar. The normality premise is not asserted
for arbitrary outer automorphism quotients. The case where F Tbar is not
normal remains a separate obligation for the full E.4.2 local theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252).
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound.LocalControl
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- If the local factor times the Sylow image is normal in H/O₂(H), the
pointwise kernel times T is normal relative to H. -/
theorem coreFixedSpace_kernel_sup_sylow_normal_of_factor_sup_normal (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G))
    [IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H))]
    (houter : (generalizedFitting (H ⧸ pCore 2 H) ⊔
      ((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).Normal) :
    ((subspaceKernel ρ (coreFixedSpace ρ k m H) H ⊔ (T : Subgroup G)).subgroupOf H).Normal := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let N := (subspaceKernel ρ (coreFixedSpace ρ k m H) H).subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let F := generalizedFitting (H ⧸ pCore 2 H)
  let : N.Normal := coreFixedSpace_kernel_normal ρ k m H
  let : (N.map q).Normal := Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  let : (F ⊔ S.map q).Normal := houter
  have hFN : F ≤ N.map q := coreFixedSpace_kernel_image_contains_factor ρ T H hTH hjm hmk hn
  have hbar : (N.map q ⊔ S.map q).Normal := by
    have he : N.map q ⊔ S.map q = N.map q ⊔ (F ⊔ S.map q) := by
      rw [← sup_assoc, sup_of_le_left hFN]
    rw [he]
    infer_instance
  have hpre := hbar.comap q
  have hQT : pCore 2 H ≤ S := pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)
  have he : (N.map q ⊔ S.map q).comap q = N ⊔ S := by
    rw [← Subgroup.map_sup, comap_map_eq]
    simp only [q, QuotientGroup.ker_mk', sup_of_le_left (hQT.trans le_sup_right)]
  rw [he] at hpre
  rw [subgroupOf_sup (subspaceKernel_le ρ _ H) hTH]
  exact hpre

/-- Normality of the local factor times the Sylow image suffices to preserve
every later weak fixed space. This normality is an explicit extra premise. -/
theorem eventual_invariance_of_quasisimple_factor_sup_normal (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G))
    [IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H))]
    (houter : (generalizedFitting (H ⧸ pCore 2 H) ⊔
      ((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).Normal) :
    ∀ n, m ≤ n → H ≤ subspaceStabilizer ρ
      (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T)) :=
  eventual_invariance_of_kernel_sup_normal ρ T H hTH k m
    (coreFixedSpace_kernel_sup_sylow_normal_of_factor_sup_normal ρ T H hTH hjm hmk hn houter)

/-- The quasisimple local branch is proved whenever the quotient of H/O₂(H)
by its generalized Fitting subgroup is a two-group. -/
theorem eventual_invariance_of_quasisimple_two_quotient (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G))
    [IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H))]
    (hquot : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ generalizedFitting (H ⧸ pCore 2 H))) :
    ∀ n, m ≤ n → H ≤ subspaceStabilizer ρ
      (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply eventual_invariance_of_quasisimple_factor_sup_normal ρ T H hTH hjm hmk hn
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have he : generalizedFitting (H ⧸ pCore 2 H) ⊔
      ((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
    simpa only [S, sup_comm, Sylow.coe_mapSurjective, Sylow.coe_subtype] using
      S.sup_eq_top_of_quotient_isPGroup (generalizedFitting (H ⧸ pCore 2 H)) hquot
  rw [he]
  infer_instance

end CFSG.Quasithin.ChapterE.ValueBound.LocalControl
