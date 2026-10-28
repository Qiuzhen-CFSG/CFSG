module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FixedGeometry
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Group

/-!
# The index-two invariance step in the component branch

Once the component contains both factors, a central involution of `T` that
centralizes the component would centralize `Y₁` and both conjugate factors of
`X`. The distinct unique maximal two-local overgroups therefore force this
intersection to be trivial.

Write `B = C_{Tᵢ}(L)` and `A = C_{Tᵢ}(Y₁)`. The model calculation supplies
`|A : B| = 2`. Here `A` is normal in `T`, `B` is normalized by the index-two
subgroup `Tᵢ`, and the normal core of `B` in `T` is trivial by the fixed-point
theorem for two-groups. Intersecting the two conjugates of `B` in `A` gives
`|A| ≤ 4`, hence `|B| ≤ 2`. A nontrivial common fixed subgroup is then all of `B`.

These lemmas do not supply the component or the model index. Their construction
and the final elimination remain with the component-branch assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch

private theorem card_le_two_of_core_free
    {P : Type*} [Group P] [Finite P] (N A B : Subgroup P)
    (hN : N.index = 2) (hNB : N ≤ normalizer (B : Set P))
    [A.Normal] (hBA : B ≤ A) (hBAindex : B.relIndex A = 2)
    (hcore : B.normalCore = ⊥) : Nat.card B ≤ 2 := by
  obtain ⟨t, ht, _⟩ := N.index_eq_two_iff_exists_notMem_and.mp hN
  let B' := B.comap (MulAut.conj t).toMonoidHom
  have hcore' : B ⊓ B' = B.normalCore := by
    apply le_antisymm
    · intro x hx g
      by_cases hg : g ∈ N
      · exact (mem_normalizer_iff.mp (hNB hg) x).mp hx.1
      · have hgt : g * t⁻¹ ∈ N := by
          rw [N.mul_mem_iff_of_index_two hN, N.inv_mem_iff]
          exact iff_of_false hg ht
        have hx' : t * x * t⁻¹ ∈ B := hx.2
        have hh := (mem_normalizer_iff.mp (hNB hgt) (t * x * t⁻¹)).mp hx'
        convert hh using 1
        group
    · intro x hx
      exact ⟨B.normalCore_le hx, hx t⟩
  have hB' : B'.relIndex A = 2 := by
    change (B.comap (MulAut.conj t).toMonoidHom).relIndex A = 2
    rw [relIndex_comap]
    have he : A.map (MulAut.conj t).toMonoidHom = A := Subgroup.Normal.map_conj_eq A t
    rw [he, hBAindex]
  have hAcard : Nat.card A ≤ 4 := by
    have hi := relIndex_inf_le (H := B) (K := B') (L := A)
    rw [hcore', hcore, relIndex_bot_left, hBAindex, hB'] at hi
    exact hi
  have hc := relIndex_mul_relIndex (⊥ : Subgroup P) B A bot_le hBA
  rw [relIndex_bot_left, relIndex_bot_left, hBAindex] at hc
  omega

private theorem normal_eq_bot_of_disjoint_omega
    {G : Type*} [Group G] [Finite G] {T D : Subgroup G}
    (hT : IsPGroup 2 T) (hDT : D ≤ T)
    (hn : T ≤ normalizer (D : Set G))
    (hdis : Stellmacher.omegaOneCenterAmbient T ⊓ D = ⊥) : D = ⊥ := by
  by_contra hD
  let Dₜ := D.subgroupOf T
  have hDₜ : Dₜ ≠ ⊥ := by
    intro hb
    exact hD (by rw [← map_subgroupOf_eq_of_le hDT]; change Dₜ.map T.subtype = ⊥
                 rw [hb, Subgroup.map_bot])
  let : Dₜ.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  obtain ⟨W, _, hWD, hWcard, hWZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 2) Dₜ ((nontrivial_iff_ne_bot Dₜ).mpr hDₜ)
  have hWbot : W = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    have hz : ((w : T) : G) ∈ Stellmacher.omegaOneCenterAmbient T := by
      apply (Stellmacher.mem_omegaOneCenterAmbient_iff T _).mpr
      refine ⟨w.property, ?_, ?_⟩
      · have hp : (⟨w, hw⟩ : W) ^ Nat.card W = 1 := pow_card_eq_one'
        rw [hWcard] at hp
        exact congrArg (fun a : W => ((a : T) : G)) hp
      · intro t ht
        exact congrArg Subtype.val ((mem_center_iff.mp (hWZ hw)) ⟨t, ht⟩)
    have he : (w : G) = 1 := mem_bot.mp (hdis ▸
      (show (w : G) ∈ Stellmacher.omegaOneCenterAmbient T ⊓ D from ⟨hz, hWD hw⟩))
    exact mem_bot.mpr (Subtype.ext he)
  rw [hWbot, card_bot] at hWcard
  omega

/-- The central omega subgroup has trivial intersection with a subgroup
centralizing both factors. Central elements also centralize the conjugate
factor, so the distinct unique maximal overgroups apply to `X` and `Y₁`. -/
theorem centralOmega_disjoint_component_centralizer
    {G : Type*} [Group G] [Finite G]
    {T Tᵢ Y₁ Y₂ X L M₁ M₂ : Subgroup G} {t : G}
    (ht : t ∈ T) (hX : X = Y₂ ⊔ Y₂.map (MulAut.conj t).toMonoidHom)
    (hY₁L : Y₁ ≤ L) (hY₂L : Y₂ ≤ L)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ T ≤ M → M = M₁)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M → M = M₂)
    (hne : M₁ ≠ M₂) :
    Stellmacher.omegaOneCenterAmbient T ⊓
      (Tᵢ ⊓ centralizer (L : Set G)) = ⊥ := by
  let Z := Stellmacher.omegaOneCenterAmbient T
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian T
  have hTZ : T ≤ centralizer (Z : Set G) := by
    intro a ha
    exact mem_centralizer_iff.mpr fun z hz =>
      (((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 a ha).symm
  have hdis := centralizers_disjoint_of_unique hTZ huniqueY huniqueX hne
  apply le_bot_iff.mp
  intro z hz
  have hzY₁ := centralizer_le hY₁L hz.2.2
  have hzY₂ := centralizer_le hY₂L hz.2.2
  let C := centralizer ({z} : Set G)
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (hTZ ht) z hz.1).symm
  have hY₂C : Y₂ ≤ C := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzY₂ y hy)
  have hXC : X ≤ C := by
    rw [hX]
    refine sup_le hY₂C ?_
    rintro _ ⟨y, hy, rfl⟩
    exact C.mul_mem (C.mul_mem htC (hY₂C hy)) (C.inv_mem htC)
  have hzX : z ∈ centralizer (X : Set G) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hXC hx)
  exact hdis.le ⟨⟨hz.1, hzY₁⟩, ⟨hz.1, hzX⟩⟩

/-- The index-two action bounds the component centralizer, using relative
normality in `T` and `Tᵢ`. The index in the fixed subgroup comes from the
`A₆` model decomposition, which is a separate premise. -/
theorem component_centralizer_card_le_two
    {G : Type*} [Group G] [Finite G] {T Tᵢ Y L : Subgroup G}
    (hT : IsPGroup 2 T) (hTᵢT : Tᵢ ≤ T) (hindex : Tᵢ.relIndex T = 2)
    (hTY : T ≤ normalizer (Y : Set G))
    (hTᵢL : Tᵢ ≤ normalizer (L : Set G)) (hYL : Y ≤ L)
    (hfixed : (Tᵢ ⊓ centralizer (L : Set G)).relIndex
      (Tᵢ ⊓ centralizer (Y : Set G)) = 2)
    (hdis : Stellmacher.omegaOneCenterAmbient T ⊓
      (Tᵢ ⊓ centralizer (L : Set G)) = ⊥) :
    Nat.card (Tᵢ ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2 := by
  let A := Tᵢ ⊓ centralizer (Y : Set G)
  let B := Tᵢ ⊓ centralizer (L : Set G)
  let N := Tᵢ.subgroupOf T
  let Aₜ := A.subgroupOf T
  let Bₜ := B.subgroupOf T
  have hAT : A ≤ T := inf_le_left.trans hTᵢT
  have hBT : B ≤ T := inf_le_left.trans hTᵢT
  have hBA : B ≤ A := inf_le_inf_left _ (centralizer_le hYL)
  let : N.Normal := N.normal_of_index_eq_two hindex
  have hTTᵢ : T ≤ normalizer (Tᵢ : Set G) := le_normalizer_of_normal_subgroupOf hTᵢT
  have hTA : T ≤ normalizer (A : Set G) :=
    (le_inf hTTᵢ (hTY.trans (normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  let : Aₜ.Normal := normal_subgroupOf_of_le_normalizer hTA
  have hNB : Tᵢ ≤ normalizer (B : Set G) :=
    (le_inf Tᵢ.le_normalizer (hTᵢL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hNₜBₜ : N ≤ normalizer (Bₜ : Set T) := by
    rw [← subgroupOf_normalizer_eq hBT]
    exact comap_mono hNB
  have hcore : Bₜ.normalCore = ⊥ := by
    let D := Bₜ.normalCore.map T.subtype
    have hDB : D ≤ B := by
      exact (map_mono Bₜ.normalCore_le).trans (map_subgroupOf_eq_of_le hBT).le
    have hDT : D ≤ T := hDB.trans hBT
    have hnD : T ≤ normalizer (D : Set G) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
        using Bₜ.normalCore.le_normalizer_map T.subtype
    have hd : D = ⊥ := normal_eq_bot_of_disjoint_omega hT hDT hnD
      (le_bot_iff.mp ((inf_le_inf_left _ hDB).trans hdis.le))
    exact (Bₜ.normalCore.map_eq_bot_iff_of_injective T.subtype_injective).mp hd
  have hi : Bₜ.relIndex Aₜ = 2 := by
    rw [← relIndex_map_map_of_injective Bₜ Aₜ T.subtype_injective,
      map_subgroupOf_eq_of_le hBT, map_subgroupOf_eq_of_le hAT]
    exact hfixed
  have hc := card_le_two_of_core_free N Aₜ Bₜ hindex hNₜBₜ
    (comap_mono hBA) hi hcore
  rwa [Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv] at hc

/-- A nontrivial common fixed subgroup contained in the component centralizer
is the whole centralizer, and both have order two. -/
theorem component_centralizer_eq_common_fixed
    {G : Type*} [Group G] [Finite G] {T Tᵢ Y L E₀ : Subgroup G}
    (hT : IsPGroup 2 T) (hTᵢT : Tᵢ ≤ T) (hindex : Tᵢ.relIndex T = 2)
    (hTY : T ≤ normalizer (Y : Set G))
    (hTᵢL : Tᵢ ≤ normalizer (L : Set G)) (hYL : Y ≤ L)
    (hfixed : (Tᵢ ⊓ centralizer (L : Set G)).relIndex
      (Tᵢ ⊓ centralizer (Y : Set G)) = 2)
    (hdis : Stellmacher.omegaOneCenterAmbient T ⊓
      (Tᵢ ⊓ centralizer (L : Set G)) = ⊥)
    (hE₀ : E₀ ≠ ⊥) (hE₀C : E₀ ≤ Tᵢ ⊓ centralizer (L : Set G)) :
    Tᵢ ⊓ centralizer (L : Set G) = E₀ ∧ Nat.card E₀ = 2 := by
  have hc := component_centralizer_card_le_two hT hTᵢT hindex hTY hTᵢL hYL hfixed hdis
  have hlarge : 1 < Nat.card E₀ :=
    Finite.one_lt_card_iff_nontrivial.mpr ((nontrivial_iff_ne_bot E₀).mpr hE₀)
  have hle := card_le_of_le hE₀C
  have he : Nat.card E₀ = 2 := by omega
  exact ⟨(eq_of_le_of_card_ge hE₀C (by omega)).symm, he⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
