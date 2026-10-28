module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.Basic

/-!
# Restriction and proper-centralizer induction for Aschbacher 3.4

The intersection-generated subgroup of a restricted pair maps into the
ambient intersection-generated subgroup. This lets both clauses of strong
closure descend to a local subgroup, provided its Sylow subgroup is the actual
intersection with the fixed Sylow and the local normalizers preserve the
ambient factors.

Minimality then applies in the smaller group. Nonnesting excludes the second
source alternative and the actual dihedral/semidihedral model condition excludes
the third, forcing the local subgroup into the ambient generated subgroup.
The centralizer application also derives the normalizer alignment from source
(b), permutation of the pair. Its Sylow-placement and pair-permutation premises
remain obligations of the local-geometry producer; this module does not assert
unconditional source (d) or global strong closure (e).

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(d), printed p.95, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
universe u
variable {G : Type u} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Every generator for the restricted pair is an ambient pair transporter. -/
theorem intersectionGenerated_subgroupOf_le (K : Subgroup G) :
    intersectionGenerated (A₁.subgroupOf K) (A₂.subgroupOf K) ≤
      (intersectionGenerated A₁ A₂).subgroupOf K := by
  apply (closure_le _).mpr
  rintro g ⟨C, hC, D, hD, hcap⟩
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcap
  have hx := x.property
  obtain ⟨a, ha, he⟩ := hx.1
  have haU : (a : G) ∈ (A₁ : Set G) ∪ A₂ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
  have hxU : ((x : K) : G) ∈ (A₁ : Set G) ∪ A₂ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact Or.inl hx.2
    · exact Or.inr hx.2
  have he' : (g : G)⁻¹ * (a : G) * g = ((x : K) : G) := by
    simpa using congrArg Subtype.val he
  have hane : (a : G) ≠ 1 := by
    intro hone
    have hxone : (x : K) = 1 := Subtype.ext (by simpa [hone] using he'.symm)
    exact hxne (Subtype.ext hxone)
  exact transporter_mem_intersectionGenerated haU hane (he' ▸ hxU)

/-- Restrict the full source setup, retaining both relative normalizers and
the genuine locally generated subgroup. -/
theorem Hypotheses.restrict [Finite G] (h : Hypotheses S A₁ A₂)
    (K : Subgroup G) (P : Sylow 2 K)
    (hP : (P : Subgroup K) = (S : Subgroup G).subgroupOf K)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf K))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf K))
    (hN₁ : ∀ x : K, x ∈ P →
      x ∈ normalizer (A₁.subgroupOf K : Set K) → (x : G) ∈ normalizer (A₁ : Set G))
    (hN₂ : ∀ x : K, x ∈ P →
      x ∈ normalizer (A₂.subgroupOf K : Set K) → (x : G) ∈ normalizer (A₂ : Set G)) :
    Hypotheses P (A₁.subgroupOf K) (A₂.subgroupOf K) := by
  have hS (x : K) : x ∈ P ↔ (x : G) ∈ S := by
    change x ∈ (P : Subgroup K) ↔ (x : G) ∈ S
    rw [hP]
    rfl
  have hc : ⁅A₁.subgroupOf K, A₂.subgroupOf K⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    apply commutator_le.mpr
    intro x hx y hy
    apply Subtype.ext
    have hm := commutator_mem_commutator (G := G) (show (x : G) ∈ A₁ from hx)
      (show (y : G) ∈ A₂ from hy)
    rw [h.commute] at hm
    exact hm
  have hrank_ne {B : Subgroup K} (hr : TwoRankAtLeastTwo B) : B ≠ ⊥ := by
    obtain ⟨E, hE, _⟩ := hr
    have hcard := Subgroup.card_le_card_group E
    rw [hE] at hcard
    intro he
    rw [he] at hcard
    simp at hcard
  refine ⟨?_, ?_, hc, hr₁, hr₂, ?_, ?_, ?_⟩
  · intro x hx
    exact (hS x).mpr (h.left_le hx)
  · intro x hx
    exact (hS x).mpr (h.right_le hx)
  · refine ⟨?_, ?_⟩
    · intro x hx
      constructor
      · exact hx.elim (fun hx => left_le_intersectionGenerated (hrank_ne hr₁) hx)
          (fun hx => right_le_intersectionGenerated (hrank_ne hr₂) hx)
      · exact (hS x).mpr (hx.elim (fun hx => h.left_le hx) (fun hx => h.right_le hx))
    · intro x hx g hg hconj
      exact h.closed_in_generated.2 x hx g (intersectionGenerated_subgroupOf_le K hg)
        ⟨intersectionGenerated_subgroupOf_le K hconj.1, (hS _).mp hconj.2⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      refine ⟨(hS x).mpr (h.closed_in_left_normalizer.1 hx).1, ?_⟩
      intro a
      exact h.closed_in_left_normalizer.1 hx |>.2 (a : G)
    · intro x hx g _ hg
      exact h.closed_in_left_normalizer.2 x hx g (mem_top _) ⟨(hS _).mp hg.1,
        hN₁ _ hg.1 hg.2⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      refine ⟨(hS x).mpr (h.closed_in_right_normalizer.1 hx).1, ?_⟩
      intro a
      exact h.closed_in_right_normalizer.1 hx |>.2 (a : G)
    · intro x hx g _ hg
      exact h.closed_in_right_normalizer.2 x hx g (mem_top _) ⟨(hS _).mp hg.1,
        hN₂ _ hg.1 hg.2⟩

/-- If a Sylow element can only preserve a factor or send it to the other
factor, a nonnested local intersection forces preservation. This is the
normalizer comparison used immediately before source (d). -/
theorem normalizer_restriction_of_permuting
    {A B K : Subgroup G}
    (hperm : ∀ s ∈ S, conjugate A s = A ∨ conjugate A s = B)
    (hn : ¬ A ⊓ K ≤ B) (g : K) (hg : (g : G) ∈ S)
    (hN : g ∈ normalizer (A.subgroupOf K : Set K)) :
    (g : G) ∈ normalizer (A : Set G) := by
  rcases hperm g hg with he | he
  · exact (mem_normalizer_iff_conjugate_eq A g).mpr he
  · exfalso
    apply hn
    intro x hx
    have hlocal : (⟨x, hx.2⟩ : K) ∈ conjugate (A.subgroupOf K) g := by
      rw [(mem_normalizer_iff_conjugate_eq _ _).mp hN]
      exact hx.1
    obtain ⟨a, ha, hax⟩ := hlocal
    have hxconj : x ∈ conjugate A (g : G) := by
      refine mem_map.mpr ⟨(a : G), ha, ?_⟩
      simpa using congrArg Subtype.val hax
    rwa [he] at hxconj

/-- Apply minimality to a proper local subgroup after verifying the literal
restricted Sylow and normalizer data. The two nonnesting assumptions exclude
alternative (2); the model assumption excludes alternative (3). -/
theorem MinimalCounterexample.subgroup_le_generated [Finite G]
    (m : MinimalCounterexample S A₁ A₂)
    (K : Subgroup G) (hK : K ≠ ⊤) (P : Sylow 2 K)
    (hP : (P : Subgroup K) = (S : Subgroup G).subgroupOf K)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf K))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf K))
    (hN₁ : ∀ x : K, x ∈ P →
      x ∈ normalizer (A₁.subgroupOf K : Set K) → (x : G) ∈ normalizer (A₁ : Set G))
    (hN₂ : ∀ x : K, x ∈ P →
      x ∈ normalizer (A₂.subgroupOf K : Set K) → (x : G) ∈ normalizer (A₂ : Set G))
    (hn₁ : ¬ A₁ ⊓ K ≤ A₂) (hn₂ : ¬ A₂ ⊓ K ≤ A₁)
    (hmodel : ∀ g : K, conjugate (A₁.subgroupOf K) g = A₂.subgroupOf K →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf K)) :
    K ≤ intersectionGenerated A₁ A₂ := by
  have hcard : Nat.card K < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group K)
      (fun he => hK (K.eq_top_of_card_eq he))
  have hlocal := m.setup.restrict K P hP hr₁ hr₂ hN₁ hN₂
  rcases m.smaller hcard P (A₁.subgroupOf K) (A₂.subgroupOf K) hlocal with
    hgen | ⟨hn, _⟩ | he
  · intro x hx
    apply intersectionGenerated_subgroupOf_le K (x := ⟨x, hx⟩)
    rw [hgen]
    exact mem_top _
  · rcases hn with hn | hn
    · exact (hn₁ (fun x hx => hn (show (⟨x, hx.2⟩ : K) ∈ A₁.subgroupOf K from hx.1))).elim
    · exact (hn₂ (fun x hx => hn (show (⟨x, hx.2⟩ : K) ∈ A₂.subgroupOf K from hx.1))).elim
  · obtain ⟨g, hg, _⟩ := he.1
    exact (hmodel g hg he.2.1).elim

/-- The induction inference in source (d), for the actual centralizer and
its actual restricted factors. The local Sylow placement and the two
normalizer alignments must still be supplied by source (b)--(c). -/
theorem MinimalCounterexample.centralizer_alternative_of_restriction [Finite G]
    (m : MinimalCounterexample S A₁ A₂) (u : G)
    (P : Sylow 2 (centralizer ({u} : Set G)))
    (hP : (P : Subgroup (centralizer ({u} : Set G))) =
      (S : Subgroup G).subgroupOf (centralizer ({u} : Set G)))
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hN₁ : ∀ x : centralizer ({u} : Set G), x ∈ P →
      x ∈ normalizer (A₁.subgroupOf (centralizer ({u} : Set G)) :
        Set (centralizer ({u} : Set G))) → (x : G) ∈ normalizer (A₁ : Set G))
    (hN₂ : ∀ x : centralizer ({u} : Set G), x ∈ P →
      x ∈ normalizer (A₂.subgroupOf (centralizer ({u} : Set G)) :
        Set (centralizer ({u} : Set G))) → (x : G) ∈ normalizer (A₂ : Set G))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁)
    (hmodel : ∀ g : centralizer ({u} : Set G),
      conjugate (A₁.subgroupOf (centralizer ({u} : Set G))) g =
        A₂.subgroupOf (centralizer ({u} : Set G)) →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({u} : Set G)))) :
    centralizer ({u} : Set G) = ⊤ ∨
      centralizer ({u} : Set G) ≤ intersectionGenerated A₁ A₂ := by
  by_cases hK : centralizer ({u} : Set G) = ⊤
  · exact Or.inl hK
  · exact Or.inr (m.subgroup_le_generated _ hK P hP hr₁ hr₂ hN₁ hN₂ hn₁ hn₂ hmodel)

/-- The proper-centralizer induction step once source (b) and the local
Sylow placement have been established. Normalizer alignment is discharged
here from permutation of the two ambient factors and their nonnesting. -/
theorem MinimalCounterexample.centralizer_alternative_of_permuting [Finite G]
    (m : MinimalCounterexample S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁))
    (u : G) (P : Sylow 2 (centralizer ({u} : Set G)))
    (hP : (P : Subgroup (centralizer ({u} : Set G))) =
      (S : Subgroup G).subgroupOf (centralizer ({u} : Set G)))
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁)
    (hmodel : ∀ g : centralizer ({u} : Set G),
      conjugate (A₁.subgroupOf (centralizer ({u} : Set G))) g =
        A₂.subgroupOf (centralizer ({u} : Set G)) →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({u} : Set G)))) :
    centralizer ({u} : Set G) = ⊤ ∨
      centralizer ({u} : Set G) ≤ intersectionGenerated A₁ A₂ := by
  apply m.centralizer_alternative_of_restriction u P hP hr₁ hr₂
    (hn₁ := hn₁) (hn₂ := hn₂) (hmodel := hmodel)
  · intro x hx hN
    have hxS : (x : G) ∈ S := by
      change x ∈ (P : Subgroup _) at hx
      rw [hP] at hx
      exact hx
    exact normalizer_restriction_of_permuting
      (fun s hs => (hperm s hs).imp And.left And.left) hn₁ x hxS hN
  · intro x hx hN
    have hxS : (x : G) ∈ S := by
      change x ∈ (P : Subgroup _) at hx
      rw [hP] at hx
      exact hx
    exact normalizer_restriction_of_permuting
      (fun s hs => (hperm s hs).imp And.right And.right) hn₂ x hxS hN

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
