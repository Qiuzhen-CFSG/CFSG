module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.Construction
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# The invariant local space in E.4.2

Intersect a corank-j family member in H with its embedded two-core Q. The
quotient rank bounds the additional corank. Consequently the H-invariant
space U = C_V(W_m(Q)) is fixed by every corank-j family member in H whenever
j + i(H) ≤ m ≤ k. Also C_V(W_m(T)) ≤ U. These facts use the actual family
condition, with no requirement that the containing member A lie in H or T.

A weaker route than residual centralization is available: if H is generated
by its kernel on U and elements normalizing T, then H preserves every
C_V(W_n(T)) for n ≥ m. Frattini's argument gives this generation whenever
the product of the kernel with T is normal in H. No local generalized-Fitting
hypothesis is claimed to imply that remaining normality condition here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252). These are conditional reductions, not E.4.2.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound.LocalControl
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The fixed space of the weak subgroup formed inside the embedded local two-core. -/
@[expose] noncomputable def coreFixedSpace (ρ : Representation (ZMod 2) G V) (k m : ℕ) (H : Subgroup G) :
    Submodule (ZMod 2) V :=
  fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) m
    ((pCore 2 H).map H.subtype))

/-- The whole local overgroup preserves the space formed inside its two-core. -/
theorem coreFixedSpace_invariant (ρ : Representation (ZMod 2) G V)
    (k m : ℕ) (H : Subgroup G) :
    H ≤ subspaceStabilizer ρ (coreFixedSpace ρ k m H) := by
  apply fixedSpace_invariant_normalizer
  apply le_trans _ (weakSubgroup_normalizer ρ (k + 1) m _)
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (le_normalizer_map (H := pCore 2 H) H.subtype)

omit [Finite G] in
/-- The Sylow fixed space at the same corank is contained in the local invariant space. -/
theorem fixedSpace_weakSubgroup_le_coreFixedSpace
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (k m : ℕ) :
    fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) m T) ≤
      coreFixedSpace ρ k m H :=
  fixedSpace_antitone ρ (SubgroupFamily.span_mono _ (core_le_sylow T H hTH))

/-- Every corank-j family member in H fixes the local invariant space; its containing A may lie outside H. -/
theorem coreFixedSpace_le_fixedSpace_of_corank
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    {B : Subgroup G} (hB : B ∈ corankFamily (fixedSpaceFamily ρ (k + 1)) j)
    (hBH : B ≤ H) : coreFixedSpace ρ k m H ≤ fixedSpace ρ B := by
  let Q := (pCore 2 H).map H.subtype
  obtain ⟨A, hA, hBA, hcorank⟩ := core_intersection_corank_witness ρ H hB hBH
  have hDA : B ⊓ Q ≤ A := inf_le_left.trans hBA
  have hDW : B ⊓ Q ≤ weakSubgroup (fixedSpaceFamily ρ (k + 1)) m Q :=
    SubgroupFamily.le_span ⟨A, hA, hDA, hcorank.trans hjm⟩ inf_le_right
  have he := hA.2.2 (B ⊓ Q) hDA (by dsimp only [Q]; omega)
  exact (fixedSpace_antitone ρ hDW).trans (he ▸ fixedSpace_antitone ρ hBA)

/-- All corank-j generators inside H lie in the pointwise kernel, not just one witness inside T. -/
theorem weakSubgroup_le_coreFixedSpace_kernel
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k) :
    weakSubgroup (fixedSpaceFamily ρ (k + 1)) j H ≤
      subspaceKernel ρ (coreFixedSpace ρ k m H) H := by
  apply sSup_le
  rintro B ⟨hB, hBH⟩ b hb
  exact ⟨hBH hb, fun v hv =>
    coreFixedSpace_le_fixedSpace_of_corank ρ H hjm hmk hB hBH hv ⟨b, hb⟩⟩

/-- The local invariant space is fixed by the weak subgroup formed in the whole overgroup. -/
theorem coreFixedSpace_le_fixedSpace_weakSubgroup
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k) :
    coreFixedSpace ρ k m H ≤
      fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j H) :=
  (le_fixedSpace_subspaceKernel ρ _ H).trans
    (fixedSpace_antitone ρ (weakSubgroup_le_coreFixedSpace_kernel ρ H hjm hmk))

/-- The action kernel is normal in H, with no ambient normality assertion. -/
theorem coreFixedSpace_kernel_normal
    (ρ : Representation (ZMod 2) G V) (k m : ℕ) (H : Subgroup G) :
    ((subspaceKernel ρ (coreFixedSpace ρ k m H) H).subgroupOf H).Normal :=
  subspaceKernel_normal ρ _ H (coreFixedSpace_invariant ρ k m H)

/-- Failure to normalize the earlier weak subgroup forces the local action kernel outside the two-core. -/
theorem coreFixedSpace_kernel_not_le_core
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer
      (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G)) :
    ¬ subspaceKernel ρ (coreFixedSpace ρ k m H) H ≤ (pCore 2 H).map H.subtype := by
  intro hK
  apply hn
  apply weakSubgroup_normalized_of_le_core ρ T H
  exact (SubgroupFamily.span_mono _ hTH).trans
    ((weakSubgroup_le_coreFixedSpace_kernel ρ H hjm hmk).trans hK)

private theorem le_kernel_sup_normalizer_of_sup_normal
    (T : Sylow 2 G) (H K : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hn : ((K ⊔ (T : Subgroup G)).subgroupOf H).Normal) :
    H ≤ K ⊔ normalizer (T : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMH : K ⊔ (T : Subgroup G) ≤ H := sup_le hKH hTH
  have hHM := (normal_subgroupOf_iff_le_normalizer hMH).mp hn
  have h := le_normalizer_sylow_sup (K ⊔ (T : Subgroup G)) H hMH hHM
    (T.subtype le_sup_right)
  simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
    (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] at h
  exact h.trans (sup_le le_sup_right (sup_le le_sup_left
    (T.toSubgroup.le_normalizer.trans le_sup_right)))

/-- Kernel and Sylow-normalizer generation makes every later weak fixed space invariant. -/
theorem eventual_invariance_of_kernel_normalizer
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (k m : ℕ)
    (hgen : H ≤ subspaceKernel ρ (coreFixedSpace ρ k m H) H ⊔
      normalizer (T : Set G)) :
    ∀ n, m ≤ n → H ≤ subspaceStabilizer ρ
      (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T)) := by
  intro n hmn
  apply hgen.trans
  apply sup_le
  · apply le_subspaceStabilizer
    intro g hg v hv
    have hvU : v ∈ coreFixedSpace ρ k m H :=
      fixedSpace_weakSubgroup_le_coreFixedSpace ρ T H hTH k m
        ((fixedSpace_antitone ρ (weakSubgroup_mono _ _ hmn)) hv)
    rw [hg.2 v hvU]
    exact hv
  · exact fixedSpace_invariant_normalizer ρ (weakSubgroup_normalizer ρ (k + 1) n T)

/-- Frattini turns relative normality of the kernel times T into invariance of the whole later tail. -/
theorem eventual_invariance_of_kernel_sup_normal
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (k m : ℕ)
    (hn : ((subspaceKernel ρ (coreFixedSpace ρ k m H) H ⊔
      (T : Subgroup G)).subgroupOf H).Normal) :
    ∀ n, m ≤ n → H ≤ subspaceStabilizer ρ
      (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T)) :=
  eventual_invariance_of_kernel_normalizer ρ T H hTH k m
    (le_kernel_sup_normalizer_of_sup_normal T H _ hTH (subspaceKernel_le ρ _ H) hn)

end CFSG.Quasithin.ChapterE.ValueBound.LocalControl
