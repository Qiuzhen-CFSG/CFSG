module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionGeometry
public import Theory.GroupTheory.NormalizedOrbitCard
public import Theory.GroupTheory.PrimeIndexCentralizer
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Weak closure fixes every proper flag space

For A = Vᵍ ≤ T moving V, the intersection argument gives C_V(B)=C_V(A)
for every noncyclic B≤A. Thus a moved vector has stabilizer of order at
most two. On a proper T-invariant flag space W, its nonidentity orbit
would have at least |A|/2 ≥ |W| elements, which is impossible. Therefore
A fixes W. Taking the span of the conjugates gives the same assertion
for the literal W₀(T,V).

This proves the proper-flag-space action step of Aschbacher--Smith 12.9.9(1),
printed p.863 of `refs/quasithin.pdf`, without the separate L₃(2)/L₄(2)
elementary-subgroup calculation. It does not yet prove centralization of
all of V: the conjugate two-core and coprime-action argument remains with
`qt-d-1291-natural-source`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- A Sylow-contained conjugate fixes every proper space in the original flag. -/
theorem conjugate_centralizes_proper_flag
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G)) (i : ℕ) (hi : i < n) :
    conjugate V g ≤ centralizer (F.Vi i : Set G) := by
  by_cases hmove : ⁅conjugate V g, V⁆ = ⊥
  · exact (commutator_eq_bot_iff_le_centralizer.mp hmove).trans
      (centralizer_le (F.le_seed i))
  have hAM : conjugate V g ≤ normalizer (L : Set G) :=
    hAT.trans (h.sylow_normalizes earlier.structural)
  have he : conjugate V g ⊓ normalizer (L : Set G) = conjugate V g := inf_eq_left.mpr hAM
  have hAT' : conjugate V g ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) :=
    inf_le_left.trans hAT
  obtain ⟨_, _, hfixed⟩ := common_fixed_subgroups h earlier F hab control g hAT'
    (by simpa only [he] using hmove)
  simp only [he] at hfixed
  apply le_centralizer_iff.mp
  apply centralizes_of_small_point_stabilizers (conjugate V g) (F.Vi i)
    (hAT.trans (F.invariant i)) 2
  · have hcard : Nat.card (conjugate V g) = 2 ^ n := by
      change Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = _
      rw [card_map_of_injective (MulAut.conj _).injective, h.seed_card]
    rw [hcard, F.card i hi.le, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) hi
  · intro y hy hmoves
    by_contra! hbig
    apply hmoves
    let B := conjugate V g ⊓ centralizer ({y} : Set G)
    have hyB : y ∈ centralizer (B : Set G) := by
      apply mem_centralizer_iff.mpr
      intro b hb
      exact mem_centralizer_singleton_iff.mp hb.2
    exact ((hfixed B inf_le_left hbig).le ⟨F.le_seed i hy, hyB⟩).2

/-- The literal weak closure W₀(T,V) fixes each proper original flag space. -/
theorem weakClosure_centralizes_proper_flag
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (i : ℕ) (hi : i < n) :
    ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (F.Vi i : Set G) := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAV,hindex⟩,hAT⟩
  have he : A = V.map (MulAut.conj g).toMonoidHom :=
    le_antisymm hAV (relIndex_eq_one.mp (by simpa only [pow_zero] using hindex))
  subst A
  simpa only [conjugate, inv_inv] using
    conjugate_centralizes_proper_flag h earlier F hab control g⁻¹
      (by simpa only [conjugate, inv_inv] using hAT) i hi

/-- The source application: W₀ centralizes the original V_(n−1). -/
theorem weakClosure_centralizes_flag_hyperplane
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L) (control : LocalControl C) :
    ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (F.Vi (n - 1) : Set G) :=
  weakClosure_centralizes_proper_flag h earlier F hab control.normalizers (n - 1)
    (by have := h.rank; omega)

/-- The full first action calculation for a moving conjugate A=Vᵍ≤T:
its fixed space and displacement are V_(n−1), and its action kernel has order two. -/
theorem moving_conjugate_flag_action
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥) :
    V ⊓ centralizer (conjugate V g : Set G) = F.Vi (n - 1) ∧
      Nat.card (conjugate V g ⊓ centralizer (V : Set G) : Subgroup G) = 2 ∧
      ⁅conjugate V g, V⁆ = F.Vi (n - 1) := by
  let A := conjugate V g
  let W := F.Vi (n - 1)
  have hWV : W ≤ V := F.le_seed _
  have hWA : W ≤ centralizer (A : Set G) := le_centralizer_iff.mp
    (conjugate_centralizes_proper_flag h earlier F hab control g hAT (n - 1)
      (by have := h.rank; omega))
  have hcardA : Nat.card A = Nat.card V := by
    exact card_map_of_injective (MulAut.conj _).injective
  have hcardW : Nat.card W * 2 = Nat.card V := by
    rw [h.seed_card, show Nat.card W = 2 ^ (n - 1) from F.card _ (by omega), ← pow_succ]
    congr 1
    have := h.rank
    omega
  have hindex : W.relIndex V = 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) W V bot_le hWV
    simp only [relIndex_bot_left] at hc
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc.trans hcardW.symm)
  have hnot : ¬ V ≤ centralizer (A : Set G) := fun hv =>
    hmove (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hv))
  have hfixedV : V ⊓ centralizer (A : Set G) = W := by
    apply le_antisymm ?_ (le_inf hWV hWA)
    intro y hy
    by_contra hyW
    have hgen := sup_zpowers_eq_of_relIndex_prime hWV Nat.prime_two hindex hy.1 hyW
    exact hnot (hgen ▸ sup_le hWA (zpowers_le.mpr hy.2))
  have hAM : A ≤ normalizer (L : Set G) := hAT.trans (h.sylow_normalizes earlier.structural)
  have he : A ⊓ normalizer (L : Set G) = A := inf_eq_left.mpr hAM
  obtain ⟨_, _, hfixed⟩ := common_fixed_subgroups h earlier F hab control g
    (inf_le_left.trans hAT) (by change ⁅A ⊓ _, V⁆ ≠ ⊥; rwa [he])
  change ∀ B : Subgroup G, B ≤ A ⊓ normalizer (L : Set G) → 2 < Nat.card B →
    V ⊓ centralizer (B : Set G) = V ⊓ centralizer ((A ⊓ normalizer (L : Set G) : Subgroup G) : Set G) at hfixed
  rw [he] at hfixed
  have hsmall := centralizer_card_le_two_of_common_fixed (V := V) (A := A) le_rfl hnot hfixed
  obtain ⟨y,hy,hyC⟩ := SetLike.not_le_iff_exists.mp hnot
  have hyW : y ∉ W := fun hw => hyC (hWA hw)
  have hcentral : A ⊓ centralizer ({y} : Set G) = A ⊓ centralizer (V : Set G) :=
    inf_centralizer_eq_of_prime_index_supplement A W V hWV Nat.prime_two hindex
      (le_centralizer_iff.mp hWA) y hy hyW
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans (h.sylow_normalizes_seed earlier.structural)
  have hlt := card_lt_normalized_card_mul_centralizer A V hAN y hy
    (fun he => hyC (he ▸ one_mem _))
  rw [hcentral, hcardA] at hlt
  have hkernel : Nat.card (A ⊓ centralizer (V : Set G) : Subgroup G) = 2 := by
    have hbig : 1 < Nat.card (A ⊓ centralizer (V : Set G) : Subgroup G) :=
      (Nat.mul_lt_mul_left (Nat.card_pos (α := V))).mp (by simpa only [mul_one] using hlt)
    omega
  refine ⟨hfixedV, hkernel, ?_⟩
  have hcomm : ⁅A,V⁆ ≤ W := by
    rw [commutator_comm]
    exact commutator_le_of_normalized_index_two V W A hWV hindex hAN
      (hAT.trans (F.invariant _))
  apply eq_of_le_of_card_ge hcomm
  have hc := card_le_commutator_card_mul_centralizer A y
  have hsub : (centralizer ({y} : Set G)).subgroupOf A =
      (A ⊓ centralizer ({y} : Set G)).subgroupOf A := by
    ext a
    change _ ↔ a.val ∈ A ∧ _
    exact ⟨fun ha => ⟨a.property,ha⟩,fun ha => ha.2⟩
  rw [hsub, Nat.card_congr (subgroupOfEquivOfLe
    (show A ⊓ centralizer ({y} : Set G) ≤ A from inf_le_left)).toEquiv,
    hcentral, hkernel, hcardA, ← hcardW] at hc
  have hle : Nat.card (⁅A,zpowers y⁆ : Subgroup G) ≤ Nat.card (⁅A,V⁆ : Subgroup G) :=
    Nat.card_le_card_of_injective (inclusion (commutator_mono le_rfl (zpowers_le.mpr hy)))
      (inclusion_injective _)
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
