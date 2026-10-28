module
public import Stellmacher.SectionFour.LemmaFourSix

/-!
# Stellmacher (4.7): a critical pair with its first member outside C

Under the Section Four hypotheses, there is a critical pair (P,Pstar)
with P not contained in C and Pstar in the source family pZero S.
The conclusion preserves the source's noncontainment requirement.

Split on whether the global P-family is covered by the families over C
and M. Outside the cover, choose a member outside both families and use
(4.4) with k=0. In the cover case, (4.6) supplies a starred member Q over C
outside the family over M; (4.5) supplies its critical partner R. The
partner lies outside C because C normalizes its Baumann subgroup whereas
the critical partner of Q does not. Swap the critical pair to obtain
(R,Q), with Q in the starred part of pZero S.

Source: refs/latex/stellmacher-n-group.tex, statement and proof (4.7),
Journal of Algebra 190 (1997), journal p26. This is the distinct-maximal
branch prerequisite for (5.1).
-/

namespace Stellmacher.SectionFour
universe u

private theorem pSet_mono
    {G : Type u} [Group G] {U V S P : Subgroup G} (hUV : U ≤ V)
    (hP : P ∈ SectionThree.PSet U S) : P ∈ SectionThree.PSet V S :=
  ⟨⟨hP.1.1.trans hUV, hP.1.2⟩, hP.2⟩

private theorem partner_not_le_c
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (heven : Even (Nat.card G)) (P Q : Subgroup G)
    (hpair : (P,Q) ∈ Lambda S) (hPC : P ≤ cSubgroup S) : ¬ Q ≤ cSubgroup S := by
  intro hQC
  apply baumann_not_normalized_by_partner S heven P Q hpair hPC
  have hCcore : cSubgroup S ≤ Subgroup.normalizer (twoCoreAmbient (cSubgroup S) : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  exact hQC.trans (hCcore.trans (normalizer_le_normalizer_baumann _))

/-- Stellmacher (4.7), with the first member not contained in C. -/
public theorem lemma_four_seven
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) :
    ∃ P Pstar : Subgroup G,
      (P, Pstar) ∈ Lambda S ∧
      ¬ P ≤ cSubgroup S ∧
      Pstar ∈ pZero S := by
  let PT := SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G)
  let PC := SectionThree.PSet (cSubgroup S) (S : Subgroup G)
  let PM := SectionThree.PSet (mSubgroup S) (S : Subgroup G)
  by_cases hcover : PT = PC ∪ PM
  · have hnsubset := lemma_four_six S h hcover
    obtain ⟨Q, hQstarC, hQnotM⟩ := Set.not_subset.mp hnsubset
    have hQtop : Q ∈ PT := pSet_mono le_top hQstarC.1
    obtain ⟨R, _hRstarM, hQR, _⟩ := lemma_four_five S h
      (by simpa only [PT, PC, PM, Set.union_comm] using hcover) Q hQtop hQnotM
    have hRnotC : ¬ R ≤ cSubgroup S :=
      partner_not_le_c S h.even_order Q R hQR hQstarC.1.1.1
    have hRQ : (R, Q) ∈ Lambda S :=
      ⟨hQR.2.1, hQR.1, by simpa only [sup_comm] using hQR.2.2⟩
    exact ⟨R, Q, hRQ, hRnotC, Or.inl hQstarC⟩
  · have hsmall : PC ∪ PM ⊆ PT := by
      intro P hP
      rcases hP with hPC | hPM
      · exact pSet_mono le_top hPC
      · exact pSet_mono le_top hPM
    have hnsubset : ¬ PT ⊆ PC ∪ PM := fun hbig => hcover (Set.Subset.antisymm hbig hsmall)
    obtain ⟨P, hPtop, hPoutside⟩ := Set.not_subset.mp hnsubset
    have hPnotC : P ∉ PC := fun hPC => hPoutside (Or.inl hPC)
    have hPnotM : P ∉ PM := fun hPM => hPoutside (Or.inr hPM)
    obtain ⟨Pstar, hPstar0, hPPstar⟩ := lemma_four_four S h P hPtop hPnotM 0 (Or.inl rfl)
    have hPnotleC : ¬ P ≤ cSubgroup S := fun hPC =>
      hPnotC ⟨⟨hPC, hPtop.1.2⟩, hPtop.2⟩
    exact ⟨P, Pstar, hPPstar, hPnotleC, by simpa [pAt] using hPstar0⟩

end Stellmacher.SectionFour
