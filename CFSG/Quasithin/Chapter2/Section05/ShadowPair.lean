module

public import Theory.GroupTheory.ComponentPairNormalizer
public import Theory.GroupTheory.UniqueFixedCosetPowers
public import CFSG.Quasithin.Chapter2.Section05.SourceCompletionInputs

/-!
# The strongly closed pair in the proof of 2.5.21

Put M₊ = N_G(KKˣ). The preceding source paragraphs supply C_G(t) ≤ M₊
and the marked class equality tᴳ ∩ M₊ = tᴹ₊ = I(K) ∪ I(Kˣ). Unique fixed
coset control first puts T in M₊. Every nonidentity element of T ∩ K or
T ∩ Kˣ has an involution power in the marked class, so each returning
conjugator lies in M₊. The normalizer permutes the actual components;
hence their Sylow intersections have strongly closed union and their
intersection-generated subgroup lies in M₊.

The literal crossing-pair application constructs the hypotheses of
Aschbacher's Lemma 3.4. Centerlessness gives disjointness, excluding both
its nested and order-two-intersection alternatives; simplicity makes M₊
proper. The preceding centralizer, marked fusion and rank claims and the
actual universal Lemma 3.4 remain explicit source inputs. This proves the
tail from those inputs, not all of 2.5.21 or its Aut(A₆) quotient conclusion.

Conjugation of the crossing component and strong closure use the source's
right convention. The fixed-coset API uses left cosets, related by inversion.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of Lemma 2.5.21, printed pp.566--567 (PDF pp.583--584).
-/

public section

open Subgroup Theory.GroupTheory
open BenderSuzuki.PFchapter1section1
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure

namespace CFSG.Quasithin.Chapter2.ShadowPair
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem rank_ne_bot {A : Subgroup G} (h : TwoRankAtLeastTwo A) : A ≠ ⊥ := by
  obtain ⟨E, hE, _⟩ := h
  intro he
  have : Subsingleton A := he ▸ inferInstance
  have : Subsingleton E := inferInstance
  have hh : Nat.card E = 1 := Nat.card_unique
  omega

/-- The pair tail, retaining the earlier centralizer and marked fusion claims. -/
theorem closed_union_and_transporter_bound (T : Sylow 2 G) (K L : Subgroup G)
    [IsQuasisimple K] [IsQuasisimple L] (t : G)
    (hc : ⁅K, L⁆ = ⊥) (ht : t ∈ (T : Subgroup G))
    (hC : centralizer ({t} : Set G) ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hfusion : ∀ g : G, g * t * g⁻¹ ∈ normalizer ((K ⊔ L : Subgroup G) : Set G) →
      ∃ m ∈ normalizer ((K ⊔ L : Subgroup G) : Set G),
        g * t * g⁻¹ = m * t * m⁻¹)
    (hmarked : ∀ y : G, orderOf y = 2 → y ∈ (K : Set G) ∪ L → IsConj t y) :
    (T : Subgroup G) ≤ normalizer ((K ⊔ L : Subgroup G) : Set G) ∧
    IsStronglyClosedSet
      (((T : Subgroup G) ⊓ K : Subgroup G) ∪ ((T : Subgroup G) ⊓ L : Subgroup G))
      (T : Subgroup G) ⊤ ∧
    intersectionGenerated ((T : Subgroup G) ⊓ K) ((T : Subgroup G) ⊓ L) ≤
      normalizer ((K ⊔ L : Subgroup G) : Set G) := by
  let M := normalizer ((K ⊔ L : Subgroup G) : Set G)
  let A := (T : Subgroup G) ⊓ K
  let B := (T : Subgroup G) ⊓ L
  have htM : t ∈ M := hC (mem_centralizer_singleton_iff.mpr rfl)
  have hu := UniqueFixedCoset.unique_of_fusion_and_centralizer htM hC hfusion
  have hTM : (T : Subgroup G) ≤ M :=
    (UniqueFixedCoset.p_overgroup_and_normalizer_le htM hu T.isPGroup' ht).1
  have hreturn : ∀ a ∈ (A : Set G) ∪ B, a ≠ 1 →
      ∀ g : G, g⁻¹ * a * g ∈ M → g ∈ M := by
    intro a ha ha1 g hg
    have haT : a ∈ (T : Subgroup G) := ha.elim And.left And.left
    obtain ⟨n, hn⟩ := UniqueFixedCoset.exists_prime_order_power T.isPGroup' haT ha1
    have han : a ^ n ∈ (K : Set G) ∪ L := ha.elim
      (fun ha => Or.inl (K.pow_mem ha.2 n)) (fun ha => Or.inr (L.pow_mem ha.2 n))
    obtain ⟨c, hc⟩ := isConj_iff.mp (hmarked (a ^ n) hn han)
    obtain ⟨m, hm, he⟩ := hfusion c (hc.symm ▸ hTM ((T : Subgroup G).pow_mem haT n))
    exact UniqueFixedCoset.transporter_mem_of_power htM hu hm (hc.symm.trans he) hg
  refine ⟨hTM, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    exact ha.elim And.left And.left
  · intro a ha g _ hag
    by_cases ha1 : a = 1
    · subst a
      simp
    have hg := hreturn a ha ha1 g (hTM hag)
    have haKL : a ∈ (K : Set G) ∪ L := ha.elim
      (fun ha => Or.inl ha.2) (fun ha => Or.inr ha.2)
    have hh := pair_normalizer_preserves_union hc (M.inv_mem hg) haKL
    simp only [inv_inv] at hh
    exact hh.elim (fun h => Or.inl ⟨hag, h⟩) (fun h => Or.inr ⟨hag, h⟩)
  · apply (closure_le M).mpr
    rintro g ⟨C, hCa, D, hDb, hcap⟩
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcap
    obtain ⟨a, ha, he⟩ := y.property.1
    have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
    have ha1 : a ≠ 1 := by
      intro h
      apply hy1
      rw [← he, h, map_one]
    have haAB : a ∈ (A : Set G) ∪ B := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hCa
      rcases hCa with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr ha
    have hyT : (y : G) ∈ (T : Subgroup G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hDb
      rcases hDb with rfl | rfl <;> exact y.property.2.1
    apply hreturn a haAB ha1 g
    change g⁻¹ * a * (g⁻¹)⁻¹ = (y : G) at he
    simp only [inv_inv] at he
    rw [he]
    exact hTM hyT

/-- Literal application to the crossing component Kˣ in source 2.5.21.
The marked class, centralizer and fusion premises belong to the preceding
paragraphs of that proof. The universal Asc75 implication is a separate source
theorem, not a hypothesis asserting the desired contradiction. -/
theorem false_of_marked_crossing_pair [IsSimpleGroup G]
    (T : Sylow 2 G) (K : Subgroup G) [IsQuasisimple K] (x t : G)
    (hc : ⁅K, conjugate K x⁆ = ⊥) (hz : center K = ⊥)
    (ht : t ∈ (T : Subgroup G))
    (hC : centralizer ({t} : Set G) ≤
      normalizer ((K ⊔ conjugate K x : Subgroup G) : Set G))
    (hfusion : ∀ g : G,
      g * t * g⁻¹ ∈ normalizer ((K ⊔ conjugate K x : Subgroup G) : Set G) →
      ∃ m ∈ normalizer ((K ⊔ conjugate K x : Subgroup G) : Set G),
        g * t * g⁻¹ = m * t * m⁻¹)
    (hclass : {y : G | IsConj t y ∧
        y ∈ normalizer ((K ⊔ conjugate K x : Subgroup G) : Set G)} =
      {y : G | orderOf y = 2 ∧ y ∈ (K : Set G) ∪ conjugate K x})
    (hrA : TwoRankAtLeastTwo ((T : Subgroup G) ⊓ K : Subgroup G))
    (hrB : TwoRankAtLeastTwo ((T : Subgroup G) ⊓ conjugate K x : Subgroup G))
    (asc75 : ∀ (P : Sylow 2 G) (A B : Subgroup G),
      Asc75.Hypotheses P A B → Asc75.Conclusion A B) : False := by
  let L := conjugate K x
  let A := (T : Subgroup G) ⊓ K
  let B := (T : Subgroup G) ⊓ L
  let M := normalizer ((K ⊔ L : Subgroup G) : Set G)
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv ((MulAut.conj x⁻¹).subgroupMap K)
  have hmarked : ∀ y : G, orderOf y = 2 → y ∈ (K : Set G) ∪ L → IsConj t y := by
    intro y hy hmem
    have hh : y ∈ {y : G | IsConj t y ∧ y ∈ M} := by
      change y ∈ {y : G | IsConj t y ∧
        y ∈ normalizer ((K ⊔ conjugate K x : Subgroup G) : Set G)}
      rw [hclass]
      exact ⟨hy, hmem⟩
    exact hh.1
  obtain ⟨_, hclosed, hbound⟩ :=
    closed_union_and_transporter_bound T K L t hc ht hC hfusion hmarked
  have hd : Disjoint A B :=
    (disjoint_of_commuting_of_center_eq_bot hc hz).mono inf_le_right inf_le_right
  have hab : ⁅A, B⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono inf_le_right inf_le_right).trans hc.le)
  have hs := SourceCompletionInputs.source_hypotheses_of_closed_union T A B
    (rank_ne_bot hrA) (rank_ne_bot hrB) inf_le_left inf_le_left hab hrA hrB hclosed
  exact SourceCompletionInputs.false_of_disjoint_source_pair A B M
    (rank_ne_bot hrA) (rank_ne_bot hrB) hd (pair_normalizer_ne_top hc hz)
    hbound (asc75 T A B hs)

end CFSG.Quasithin.Chapter2.ShadowPair

end
