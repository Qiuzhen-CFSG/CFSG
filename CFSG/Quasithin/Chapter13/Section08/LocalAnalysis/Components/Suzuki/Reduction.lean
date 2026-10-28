module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Commutator reductions for the Suzuki branch of 13.8.16

A solvable Borel normalized by L₁T lies in M by the universal solvable
exclusion, applied to its product with L₁T. The generation identity for Ũ_H
is obtained from the image of its generating seed, retaining relative
normality in the quotient rather than imposing normality in the ambient G.

The linear calculation retains central extensions: an actor commuting with K
and trivial on W/C_W(K) fixes [W,K]. Thus it fixes W when W=[W,K]. Finally,
if [V,K] is fixed by L₁ and V=[V,L₁], commuting K and L₁ force K to fix V.
No splitting of W over its fixed vectors is used.

These are conditional reductions for Aschbacher–Smith 13.8.16, printed
pp.952–953 (combined manuscript of 1 March 2004). The actual Suzuki Borel,
commuting action and natural-module identifications remain separate inputs.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki

variable {G : Type*} [Group G]

/-- The whole Borel lies in M once L₁T normalizes it; solvability of the product is proved. -/
theorem borel_le_of_solvable_exclusion
    (L₁ T G₁ M B : Subgroup G)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (hB : Group.IsSolvable B) (hbase : Group.IsSolvable (L₁ ⊔ T : Subgroup G))
    (hn : L₁ ⊔ T ≤ normalizer (B : Set G))
    (hBG : B ≤ G₁) (hbaseG : L₁ ⊔ T ≤ G₁) : B ≤ M := by
  let J := B ⊔ (L₁ ⊔ T)
  have hBJ : B ≤ J := le_sup_left
  have hCJ : L₁ ⊔ T ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le B.le_normalizer hn
  let : (B.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hBJ).mpr hJN
  let : Group.IsSolvable B := hB
  let : Group.IsSolvable (L₁ ⊔ T : Subgroup G) := hbase
  let : Group.IsSolvable (B.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hBJ).toMonoidHom) (subgroupOfEquivOfLe hBJ).injective
  let : Group.IsSolvable ((L₁ ⊔ T).subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hCJ).toMonoidHom) (subgroupOfEquivOfLe hCJ).injective
  have hsol : Group.IsSolvable J := by
    apply Group.isSolvable_of_normal_sup_eq_top (B.subgroupOf J) ((L₁ ⊔ T).subgroupOf J)
    rw [← subgroupOf_sup hBJ hCJ]
    exact subgroupOf_self _
  exact hBJ.trans (hex J hCJ (sup_le hBG hbaseG) hsol)

variable {D : Type*} [Group D]

/-- A homomorphism carries the conjugate span onto the span of the two images. -/
theorem map_conjugateSpan (f : G →* D) (A H : Subgroup G) :
    (conjugateSpanBy A H).map f = conjugateSpanBy (A.map f) (H.map f) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨h, hh, a, ha, rfl⟩
    change f (h * a * h⁻¹) ∈ conjugateSpanBy (A.map f) (H.map f)
    rw [map_mul, map_mul, map_inv]
    exact subset_closure ⟨f h, mem_map_of_mem f hh, f a, mem_map_of_mem f ha, rfl⟩
  · apply (closure_le _).mpr
    rintro _ ⟨_, ⟨h, hh, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨h * a * h⁻¹, subset_closure ⟨h, hh, a, ha, rfl⟩, ?_⟩
    simp

/-- The source seed identity modulo the quotient kernel generates the whole image of U_H. Normality is required only for the image of L₁ inside the image of H. -/
theorem mapped_UH_eq_commutator (f : G →* D) (H V₃ L₁ : Subgroup G)
    (hLH : L₁ ≤ H)
    (hn : H.map f ≤ normalizer (L₁.map f : Set D))
    (hseed : V₃.map f = ⁅V₃.map f, L₁.map f⁆) :
    (Source.UH H V₃).map f = ⁅(Source.UH H V₃).map f, L₁.map f⁆ := by
  rw [Source.UH, map_conjugateSpan]
  exact conjugateSpanBy_eq_commutator_of_seed _ _ _ _ (map_mono hLH) hn le_rfl hseed

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- If a commutator-generated seed spans V under H, and H normalizes L,
then V=[V,L]. This uses normality in the faithful actor, which may be H/O₂(H),
independently of the module carrier U_H/V₁. -/
theorem commutator_top_of_orbit_seed
    (H L : Subgroup G)
    (A : Submodule (ZMod 2) V)
    (hn : H ≤ normalizer (L : Set G))
    (hseed : subspaceCommutator ρ A L = A)
    (hspan : Submodule.span (ZMod 2) {v | ∃ h ∈ H, ∃ a ∈ A, ρ h a = v} = ⊤) :
    subspaceCommutator ρ ⊤ L = ⊤ := by
  have hA : A ≤ subspaceCommutator ρ ⊤ L := by
    rw [← hseed]
    exact subspaceCommutator_mono_left ρ le_top L
  have hstable : H ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ L) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp)) hn
  apply top_unique
  conv_lhs => rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨h, hh, a, ha, rfl⟩
  exact (hstable hh a).2 (hA ha)


/-- Commuting actors trivial modulo K-fixed vectors fix the K-commutator subspace. -/
theorem fixes_subspaceCommutator (K L : Subgroup G) (W : Submodule (ZMod 2) V)
    (hc : ∀ l ∈ L, ∀ k ∈ K, Commute l k)
    (hd : ∀ l ∈ L, ∀ w ∈ W, ρ l w - w ∈ fixedSpace ρ K) :
    subspaceCommutator ρ W K ≤ fixedSpace ρ L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, w, hw, rfl⟩ l
  have hcomm : ρ l (ρ k w) = ρ k (ρ l w) := by
    change (ρ l * ρ k) w = (ρ k * ρ l) w
    rw [← map_mul, ← map_mul, (hc l l.property k hk).eq]
  have hfix := hd l l.property w hw ⟨k, hk⟩
  change ρ k (ρ l w - w) = ρ l w - w at hfix
  change ρ l (ρ k w - w) = ρ k w - w
  rw [map_sub] at hfix ⊢
  rw [hcomm]
  exact (sub_eq_sub_iff_sub_eq_sub).mp hfix

/-- Centralization lifts through W/C_W(K) when W is generated by its K-commutators. -/
theorem central_extension_fixed (K L : Subgroup G) (W : Submodule (ZMod 2) V)
    (hc : ∀ l ∈ L, ∀ k ∈ K, Commute l k)
    (hgen : subspaceCommutator ρ W K = W)
    (hd : ∀ l ∈ L, ∀ w ∈ W, ρ l w - w ∈ fixedSpace ρ K) :
    W ≤ fixedSpace ρ L := by
  rw [← hgen]
  exact fixes_subspaceCommutator ρ K L W hc hd

/-- The literal central-section action suffices; no complement to C_W(K) is assumed. -/
theorem central_extension_fixed_of_section_kernel
    (K L : Subgroup G) (W : Submodule (ZMod 2) V)
    (hW : L ≤ subspaceStabilizer ρ W)
    (hc : L ≤ centralizer (K : Set G))
    (hgen : subspaceCommutator ρ W K = W)
    (hker : (centralSectionRepresentation ρ K L W hW
      (hc.trans (centralizer_le_normalizer _))).ker = ⊤) :
    W ≤ fixedSpace ρ L := by
  apply central_extension_fixed ρ K L W
  · intro l hl k hk
    exact (show Commute k l from mem_centralizer_iff.mp (hc hl) k hk).symm
  · exact hgen
  · intro l hl w hw
    exact (centralSectionRepresentation_ker_iff ρ K L W hW
      (hc.trans (centralizer_le_normalizer _)) ⟨l, hl⟩).mp
        (by rw [hker]; trivial) w hw

/-- Commuting K and L₁, with L₁ fixing [V,K] and generating V by commutators, force K to act trivially. -/
theorem component_action_trivial_of_commutator_fixed
    (K L : Subgroup G)
    (hc : ∀ l ∈ L, ∀ k ∈ K, Commute l k)
    (hgen : subspaceCommutator ρ ⊤ L = ⊤)
    (hfixed : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ L) :
    (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K := by
  rw [← hgen]
  apply fixes_subspaceCommutator ρ L K ⊤
  · intro k hk l hl
    exact (hc l hl k hk).symm
  · intro k hk v _
    exact hfixed (Submodule.subset_span ⟨k, hk, v, Submodule.mem_top, rfl⟩)

/-- The final contradiction retains the nontrivial component action as an explicit hypothesis. -/
theorem contradiction_of_commutator_fixed
    (K L : Subgroup G)
    (hc : ∀ l ∈ L, ∀ k ∈ K, Commute l k)
    (hgen : subspaceCommutator ρ ⊤ L = ⊤)
    (hfixed : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ L)
    (hnontrivial : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K) : False :=
  hnontrivial (component_action_trivial_of_commutator_fixed ρ K L hc hgen hfixed)

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki
