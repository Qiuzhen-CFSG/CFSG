module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Conjugators
public import Theory.GroupTheory.SylowIndexTwoExtension

/-!
# The constructed A₅ Sylow replacement

The actual core-pair stabilizer has index two in M₁=N_M(Φ(D)). This
excludes a Sylow subgroup normalizing the first block. The genuine
transitive two-module action then makes T₁=N_T(U) half of the ambient
Sylow subgroup. Sylow extension inside M₁ constructs T₀ and its other
coset, which normalizes T₁, squares into T₁, and moves U noncentrally.

Source: Aschbacher–Smith C.5.6(6), printed pp.157–158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
variable {G : Type*} [Group G] {R K L : Subgroup G}

private theorem block_normalizer_phi (R K : Subgroup G) :
    normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (Phi R K : Set G) := by
  have hnC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have hnD : normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (D R K : Set G) :=
    (le_inf (inf_le_left.trans (Stellmacher.normalizer_le_normalizer_baumann R))
      (inf_le_right.trans hnC)).trans inf_normalizer_le_normalizer_inf
  exact hnD.trans (normalizer_le_normalizer_characteristic_image (D R K) (frattini (D R K)))

private theorem block_normalizer_core (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G)) :
    M ⊓ normalizer (K : Set G) ≤ normalizer (Q R K : Set G) := by
  have hS := hMR.trans (Stellmacher.normalizer_le_normalizer_baumann R)
  exact ((le_inf inf_le_right (inf_le_left.trans hS)).trans
    (normalizer_inf_normalizer_le_normalizer_sup K (S R))).trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ S R) (pCore 2 (K ⊔ S R : Subgroup G)))

variable [Finite G]

/-- The actual index-two core section excludes a Sylow subgroup preserving K. -/
theorem sylow_not_normalizes_block (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G)) (T : Sylow 2 M)
    (x : G) (hx : x ∈ M)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    ¬ (T : Subgroup M).map M.subtype ≤ normalizer (K : Set G) := by
  let A := M ⊓ normalizer (Phi R K : Set G)
  let B := A ⊓ normalizer (Q R K : Set G)
  have hi : B.relIndex A = 2 := by
    rw [inf_relIndex_left]
    exact core_normalizer_index h hsource M hMR x hx hnc
  have hiM : (B.subgroupOf M).relIndex (A.subgroupOf M) = 2 := by
    rw [relIndex_subgroupOf (show A ≤ M from inf_le_left), hi]
  intro hTK
  apply sylow_not_le_index_two_section T (A.subgroupOf M) (B.subgroupOf M)
    (subgroupOf_mono M inf_le_left) hiM
  intro t ht
  have htM : (t : G) ∈ M := t.property
  have htK := hTK (mem_map_of_mem M.subtype ht)
  exact ⟨⟨htM, block_normalizer_phi R K ⟨hMR htM, htK⟩⟩,
    block_normalizer_core M hMR ⟨htM, htK⟩⟩

/-- Construct T₀ in the actual M₁ and an element of its other coset.
The half-Sylow hypothesis is discharged by the source pair action below. -/
theorem sylow_replacement (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K)) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) (T : Sylow 2 M) (V : Subgroup G)
    (hVT : V ≤ (T : Subgroup M).map M.subtype)
    (hVL : V ≤ normalizer (K : Set G))
    (hhalf : V.relIndex ((T : Subgroup M).map M.subtype) = 2)
    {x : G} (hx : x ∈ M)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let A := M ⊓ normalizer (Phi R K : Set G)
    ∃ P : Sylow 2 A, V ≤ (P : Subgroup A).map A.subtype ∧
      V.relIndex ((P : Subgroup A).map A.subtype) = 2 ∧
      ∃ y ∈ (P : Subgroup A).map A.subtype,
        y ∉ V ∧ y ∈ normalizer (V : Set G) ∧ y ^ 2 ∈ V ∧
        ¬ (U K).map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (U K : Set G) := by
  let A := M ⊓ normalizer (Phi R K : Set G)
  let B := A ⊓ normalizer (Q R K : Set G)
  let TH := (T : Subgroup M).map M.subtype
  have hVM : V ≤ M := hVT.trans (map_subtype_le _)
  have hVB : V ≤ B := by
    intro v hv
    exact ⟨⟨hVM hv, block_normalizer_phi R K ⟨hMR (hVM hv), hVL hv⟩⟩,
      block_normalizer_core M hMR ⟨hVM hv, hVL hv⟩⟩
  have hi : B.relIndex A = 2 := by
    rw [inf_relIndex_left]
    exact core_normalizer_index h hsource M hMR x hx hnc
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
  have hyQ : y ∉ normalizer (Q R K : Set G) := by
    intro hyQ
    exact hyV (hinter ▸ show y ∈ T₀ ⊓ B from ⟨hy, hyA, hyQ⟩)
  have hnorm : (V.subgroupOf T₀).Normal := normal_of_index_eq_two hindex
  exact ⟨P, hVP, hindex, y, hy, hyV,
    (normal_subgroupOf_iff_le_normalizer hVP).mp hnorm hy,
    sq_mem_of_index_two hindex (⟨y, hy⟩ : T₀),
    noncentral_of_core_moved h hsource x (hMR hx) hnc y (hMR hyA.1) hyA.2 hyQ⟩

/-- C.5.6(6) for the A₅ branch, using the literal module
stabilizer. The only block-action inputs are the preceding transitive
pair action and the stabilizer's normalization of the first block. -/
theorem source_C56_sylow (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K)) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) (T : Sylow 2 M)
    (s : ℕ) (hs : s = 1 ∨ s = 2)
    (hsingle : s = 1 → (T : Subgroup M).map M.subtype ≤ normalizer (K : Set G))
    (W : Subgroup G)
    (hpair : s = 2 → ∀ t ∈ (T : Subgroup M).map M.subtype,
      (U K).map (MulAut.conj t).toMonoidHom = U K ∨
      (U K).map (MulAut.conj t).toMonoidHom = W)
    (htrans : s = 2 → ∃ t ∈ (T : Subgroup M).map M.subtype,
      (U K).map (MulAut.conj t).toMonoidHom ≠ U K)
    (hstabilizer : ((T : Subgroup M).map M.subtype) ⊓ normalizer (U K : Set G) ≤
      normalizer (K : Set G))
    {x : G} (hx : x ∈ M)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    s = 2 ∧
      let T₁ := ((T : Subgroup M).map M.subtype) ⊓ normalizer (U K : Set G)
      let M₁ := M ⊓ normalizer (Phi R K : Set G)
      ∃ T₀ : Sylow 2 M₁, T₁ ≤ (T₀ : Subgroup M₁).map M₁.subtype ∧
        T₁.relIndex ((T₀ : Subgroup M₁).map M₁.subtype) = 2 ∧
        ∃ y ∈ (T₀ : Subgroup M₁).map M₁.subtype,
          y ∉ T₁ ∧ y ∈ normalizer (T₁ : Set G) ∧ y ^ 2 ∈ T₁ ∧
          ¬ (U K).map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (U K : Set G) := by
  have hs2 : s = 2 := hs.resolve_left (fun hs1 =>
    sylow_not_normalizes_block h hsource M hMR T x hx hnc (hsingle hs1))
  refine ⟨hs2, ?_⟩
  obtain ⟨t, ht, hmove⟩ := htrans hs2
  have hi := normalizer_relIndex_eq_two_of_pair
    ((T : Subgroup M).map M.subtype) (U K) W (hpair hs2) t ht hmove
  apply sylow_replacement h hsource M hMR T _ inf_le_left hstabilizer _ hx hnc
  simpa only [inf_relIndex_left] using hi
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
