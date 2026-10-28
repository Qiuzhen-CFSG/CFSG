module

public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Product

/-!
# The family of conjugate Sylow intersections

The family `Δ = Qᴴ ∩ S` consists of the `H`-conjugates of `Q` contained in
`S`. It is invariant under conjugation by `S`. Each member inherits the
original tightly embedded setup. Distinct members are disjoint, and whenever
one normalizes another they commute, by I.7.2 and I.7.4.

These are the proved inputs to the maximal commuting-family argument of
Aschbacher--Smith, I.7.5, printed pp.426--427. No assertion of pairwise
commutation without the normalization hypothesis is made here.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section06To08
open Subgroup
variable {G : Type*} [Group G]

/-- The source notation `Qᴴ ∩ S`: conjugate subgroups contained in `S`. -/
def tightConjugateFamily (H Q S : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ S ∧ ∃ g : G, g ∈ H ∧ conjSubgroup Q g = A}

theorem TightPGroupSetup.mem_family {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) : Q ∈ tightConjugateFamily H Q S :=
  ⟨h.hQS, 1, H.one_mem, conjSubgroup_one Q⟩

theorem TightPGroupSetup.family_setup {K H Q S A : Subgroup G}
    (h : TightPGroupSetup K H Q S) (hA : A ∈ tightConjugateFamily H Q S) :
    ∃ L : Subgroup G, TightPGroupSetup L H A S := by
  obtain ⟨hAS, a, ha, rfl⟩ := hA
  exact ⟨conjSubgroup K a, h.conjugate ha h.hSp h.hSH hAS⟩

theorem family_exists_conjugator {H Q S A B : Subgroup G}
    (hA : A ∈ tightConjugateFamily H Q S)
    (hB : B ∈ tightConjugateFamily H Q S) :
    ∃ g : G, g ∈ H ∧ conjSubgroup A g = B := by
  obtain ⟨_, a, ha, rfl⟩ := hA
  obtain ⟨_, b, hb, rfl⟩ := hB
  refine ⟨b * a⁻¹, H.mul_mem hb (H.inv_mem ha), ?_⟩
  rw [conjSubgroup_conjSubgroup]
  simp only [inv_mul_cancel_right]

theorem TightPGroupSetup.family_conjugate {K H Q S A : Subgroup G}
    (h : TightPGroupSetup K H Q S) (hA : A ∈ tightConjugateFamily H Q S)
    {s : G} (hs : s ∈ S) : conjSubgroup A s ∈ tightConjugateFamily H Q S := by
  obtain ⟨hAS, a, ha, rfl⟩ := hA
  refine ⟨?_, s * a, H.mul_mem (h.hSH hs) ha, ?_⟩
  · have hn : conjSubgroup S s = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)
    exact (conjSubgroup_mono hAS s).trans_eq hn
  · exact (conjSubgroup_conjSubgroup Q a s).symm

variable [Finite G]

/-- Any two distinct members of the source family have trivial intersection. -/
theorem TightPGroupSetup.family_disjoint {K H Q S A B : Subgroup G}
    (h : TightPGroupSetup K H Q S)
    (hA : A ∈ tightConjugateFamily H Q S)
    (hB : B ∈ tightConjugateFamily H Q S) (hne : A ≠ B) : Disjoint A B := by
  obtain ⟨L, hL⟩ := h.family_setup hA
  obtain ⟨g, hg, heq⟩ := family_exists_conjugator hA hB
  have hBS : conjSubgroup A g ≤ S := heq ▸ hB.1
  have hne' : conjSubgroup A g ≠ A := heq ▸ hne.symm
  exact disjoint_iff.mpr (heq ▸ lemma_I_7_2_2 hL hg hBS hne')

/-- Distinct members of the source family commute whenever one normalizes
the other. This supplies the normalization step in the I.7.5 family argument. -/
theorem TightPGroupSetup.family_commuting_of_normalizes {K H Q S A B : Subgroup G}
    (h : TightPGroupSetup K H Q S)
    (hA : A ∈ tightConjugateFamily H Q S)
    (hB : B ∈ tightConjugateFamily H Q S) (hne : A ≠ B)
    (hn : B ≤ normalizer (A : Set G)) : A ≤ centralizer (B : Set G) := by
  obtain ⟨L, hL⟩ := h.family_setup hA
  obtain ⟨g, hg, heq⟩ := family_exists_conjugator hA hB
  have hBS : conjSubgroup A g ≤ S ⊓ normalizer (A : Set G) :=
    heq ▸ le_inf hB.1 hn
  have hne' : conjSubgroup A g ≠ A := heq ▸ hne.symm
  exact heq ▸ (lemma_I_7_4_commuting hL hg hne' hBS).2

end CFSG.Quasithin.ChapterI.Section06To08
