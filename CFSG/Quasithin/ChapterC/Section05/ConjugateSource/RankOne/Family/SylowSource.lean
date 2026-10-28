module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Sylow

/-!
# The constructed Sylow conjugator for the source blocks

The input is the genuine preceding block action: T acts transitively on
the two modules, and its first-module stabilizer normalizes the first
block. The family theorem constructs the index-two section, and the
Sylow extension theorem constructs T₀ and the replacement conjugator.
The one-block alternative is excluded by the same index-two section.

Source: Aschbacher–Smith C.5.6(6), printed pp.157–158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- Construct T₀ in the actual M₁ and an element of its other coset.
The half-Sylow hypothesis is discharged by the source pair action below. -/
theorem Setup.sylow_replacement (h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) (T : Sylow 2 M) (V : Subgroup G)
    (hVT : V ≤ (T : Subgroup M).map M.subtype)
    (hVL : V ≤ normalizer (L : Set G))
    (hhalf : V.relIndex ((T : Subgroup M).map M.subtype) = 2)
    {x : G} (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    let A := M ⊓ normalizer (Phi R L : Set G)
    ∃ P : Sylow 2 A, V ≤ (P : Subgroup A).map A.subtype ∧
      V.relIndex ((P : Subgroup A).map A.subtype) = 2 ∧
      ∃ y ∈ (P : Subgroup A).map A.subtype,
        y ∉ V ∧ y ∈ normalizer (V : Set G) ∧ y ^ 2 ∈ V ∧
        ¬ (U L).map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (U L : Set G) := by
  let A := M ⊓ normalizer (Phi R L : Set G)
  let B := A ⊓ normalizer (Q R L : Set G)
  let TH := (T : Subgroup M).map M.subtype
  have hVM : V ≤ M := hVT.trans (map_subtype_le _)
  have hVB : V ≤ B := by
    intro v hv
    exact ⟨⟨hVM hv, block_normalizer_le_phi_normalizer R L ⟨hMR (hVM hv), hVL hv⟩⟩,
      h.block_normalizer_le_core_normalizer M hMR ⟨hVM hv, hVL hv⟩⟩
  have hi : B.relIndex A = 2 := by
    rw [inf_relIndex_left]
    exact h.frattini_stabilizer_index M hMR hx hnc
  have hcard : Nat.card TH = Nat.card V * 2 := by
    have he := relIndex_mul_relIndex ⊥ V TH bot_le hVT
    simpa only [relIndex_bot_left, show V.relIndex TH = 2 from hhalf] using he.symm
  have hbound (W : Subgroup G) (hWA : W ≤ A) (hp : IsPGroup 2 W) :
      Nat.card W ≤ Nat.card V * 2 := by
    have hWM : W ≤ M := hWA.trans inf_le_left
    calc
      Nat.card W = Nat.card (W.subgroupOf M) :=
        (Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv).symm
      _ ≤ Nat.card T := card_le_sylow_two hp.comap_subtype T
      _ = Nat.card TH := (card_map_of_injective M.subtype_injective).symm
      _ = Nat.card V * 2 := hcard
  obtain ⟨P, hVP, hindex, hinter⟩ := exists_sylow_index_two_extension_of_bound A B V
    inf_le_left hi ((T.isPGroup'.map M.subtype).to_le hVT) hVB hbound
  let T₀ := (P : Subgroup A).map A.subtype
  have hn : ¬ T₀ ≤ V := by
    intro he
    have hh := relIndex_eq_one.mpr he
    rw [hindex] at hh
    omega
  obtain ⟨y, hy, hyV⟩ := SetLike.not_le_iff_exists.mp hn
  have hyA : y ∈ A := map_subtype_le _ hy
  have hyQ : y ∉ normalizer (Q R L : Set G) := by
    intro hyQ
    exact hyV (hinter ▸ show y ∈ T₀ ⊓ B from ⟨hy, hyA, hyQ⟩)
  have hnorm : (V.subgroupOf T₀).Normal := normal_of_index_eq_two hindex
  exact ⟨P, hVP, hindex, y, hy, hyV,
    (normal_subgroupOf_iff_le_normalizer hVP).mp hnorm hy,
    sq_mem_of_index_two hindex (⟨y, hy⟩ : T₀),
    h.noncentral_of_core_moved (hMR hx) hnc (hMR hyA.1) hyA.2 hyQ⟩

/-- C.5.6(6) for the rank-one and A₃ branches, using the literal module
stabilizer. The only block-action inputs are the preceding transitive
pair action and the stabilizer's normalization of the first block. -/
theorem Setup.source_C56_sylow (h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) (T : Sylow 2 M)
    (s : ℕ) (hs : s = 1 ∨ s = 2)
    (hsingle : s = 1 → (T : Subgroup M).map M.subtype ≤ normalizer (L : Set G))
    (W : Subgroup G)
    (hpair : s = 2 → ∀ t ∈ (T : Subgroup M).map M.subtype,
      (U L).map (MulAut.conj t).toMonoidHom = U L ∨
      (U L).map (MulAut.conj t).toMonoidHom = W)
    (htrans : s = 2 → ∃ t ∈ (T : Subgroup M).map M.subtype,
      (U L).map (MulAut.conj t).toMonoidHom ≠ U L)
    (hstabilizer : ((T : Subgroup M).map M.subtype) ⊓ normalizer (U L : Set G) ≤
      normalizer (L : Set G))
    {x : G} (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    s = 2 ∧
      let T₁ := ((T : Subgroup M).map M.subtype) ⊓ normalizer (U L : Set G)
      let M₁ := M ⊓ normalizer (Phi R L : Set G)
      ∃ T₀ : Sylow 2 M₁, T₁ ≤ (T₀ : Subgroup M₁).map M₁.subtype ∧
        T₁.relIndex ((T₀ : Subgroup M₁).map M₁.subtype) = 2 ∧
        ∃ y ∈ (T₀ : Subgroup M₁).map M₁.subtype,
          y ∉ T₁ ∧ y ∈ normalizer (T₁ : Set G) ∧ y ^ 2 ∈ T₁ ∧
          ¬ (U L).map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (U L : Set G) := by
  have hs2 : s = 2 := hs.resolve_left (fun hs1 =>
    h.sylow_not_normalizes_block M hMR T hx hnc (hsingle hs1))
  refine ⟨hs2, ?_⟩
  obtain ⟨t, ht, hmove⟩ := htrans hs2
  have hi := normalizer_relIndex_eq_two_of_pair
    ((T : Subgroup M).map M.subtype) (U L) W (hpair hs2) t ht hmove
  apply h.sylow_replacement M hMR T _ inf_le_left hstabilizer _ hx hnc
  simpa only [inf_relIndex_left] using hi
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
