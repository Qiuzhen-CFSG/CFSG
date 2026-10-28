module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Orthogonal

/-!
# The native linear-five source branch

The exact orthogonal subgroup calculation places a zero-form elementary
subgroup of Q in E or in one of the two native F occurrences. A nonfirst-class
involution already positioned in X ∩ E bounds C(X) by the literal octad
stabilizer D. The proved global two-occurrence catalogue then controls N(X).
This discharges the occurrence and centralizer premises of the one-or-two-F
consumer, for either native occurrence and after any ambient conjugation.

The maximal-two-local corollary identifies the local with an actual conjugate
of the full generated linear-five normalizer or of max1. The input that the
nonfirst witness lies in E is the source positioning, not a replacement for
zero-form geometry. Other octad-image branches remain separate.

Source: Kleidman--Wilson, The Maximal Subgroups of J4 (1988), Proposition
2.2.2(i)--(ii), p.490, and the first paragraph of Proposition 2.2.3, p.491.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Subgroup LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB

private theorem conjugate_product (H : Subgroup Model) (g k : Model) :
    (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one (H : Subgroup Model) :
    H.map (MulAut.conj (1 : Model)).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (H : Set Model)).one_mem

/-- The same kernel seed exchanges the two literal occurrences. -/
theorem secondF_conjugate_seed : secondF.map (MulAut.conj seed).toMonoidHom = F := by
  rw [secondF,conjugate_product,seed_square,conjugate_one]

/-- The one-or-two consumer with the second native occurrence as its base. -/
theorem native_second_occurrence_normalizer (X : Subgroup Model)
    (hXF : X ≤ secondF) (hCD : centralizer (X : Set Model) ≤ D) :
    normalizer (X : Set Model) ≤ M_F.map (MulAut.conj seed).toMonoidHom ∨
      normalizer (X : Set Model) ≤ M := by
  have ho (g : Model) (h : secondF.map (MulAut.conj g).toMonoidHom ≤ D) :
      secondF.map (MulAut.conj g).toMonoidHom = secondF ∨
        secondF.map (MulAut.conj g).toMonoidHom =
          secondF.map (MulAut.conj seed).toMonoidHom := by
    rw [secondF,conjugate_product] at h
    have hh := global_conjugates_in_D (g*seed) h
    rw [secondF_conjugate_seed]
    simpa only [secondF,conjugate_product] using hh.symm
  have hi : secondF ⊓ secondF.map (MulAut.conj seed).toMonoidHom ≤ E := by
    rw [secondF_conjugate_seed,inf_comm]
    exact intersection_le_E
  have hh := ElementaryNormalizerCover.two_occurrence_normalizer_alternatives
    secondF X seed centralizer_secondF hXF hCD ho hi
  rwa [M_F_eq_fullNormalizer, map_equiv_normalizer_eq]

/-- Precise source centralizer bound after the nonfirst involution is in X ∩ E.
Only the actual octad placement and an element outside E are needed here. -/
theorem source_Q_centralizer_container (X : Subgroup Model)
    (hXQ : X ≤ Q) (hXE : ¬ X ≤ E) (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    centralizer (X : Set Model) ≤ D := by
  apply centralizer_le_D_of_le_M X hXQ hXE
  have ht1 : t ≠ 1 := by intro he; rw [he,orderOf_one] at ht2; omega
  exact (centralizer_le (Set.singleton_subset_iff.mpr htX)).trans
    (ElementaryNormalizerCover.kernel_nonfirst_centralizer_le_max1 t htE ht1 hnt)

/-- KW 2.2.2's F occurrence and KW 2.2.3's one-or-two argument, with every
native geometry premise discharged. The nonfirst witness retains its source
position in X ∩ E. -/
theorem source_zero_form_F_branch (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXQ : X ≤ Q) (hform : intrinsicElementaryForm X = 0) (hXE : ¬ X ≤ E)
    (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    ∃ g : Model, (g = 1 ∨ g = seed) ∧
      X ≤ F.map (MulAut.conj g).toMonoidHom ∧
      F.map (MulAut.conj g).toMonoidHom ≤ centralizer (X : Set Model) ∧
      centralizer (X : Set Model) ≤ D ∧
      (normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
        normalizer (X : Set Model) ≤ M) := by
  have hCD := source_Q_centralizer_container X hXQ hXE t htX htE ht2 hnt
  rcases zero_form_Q_placement X hXQ hform with h | h | h
  · exact (hXE h).elim
  · refine ⟨1,Or.inl rfl,?_,?_,hCD,?_⟩
    · rwa [conjugate_one]
    · rw [conjugate_one,← centralizer_F]
      exact centralizer_le h
    · rw [conjugate_one]
      exact native_two_occurrence_normalizer X h hCD
  · refine ⟨seed,Or.inr rfl,h,?_,hCD,native_second_occurrence_normalizer X h hCD⟩
    change secondF ≤ centralizer (X : Set Model)
    rw [← centralizer_secondF]
    exact centralizer_le h

/-- The whole zero-form octad branch, including the E alternative. -/
theorem source_zero_form_Q_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXQ : X ≤ Q) (hform : intrinsicElementaryForm X = 0)
    (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    normalizer (X : Set Model) ≤ M ∨
      ∃ g : Model, (g = 1 ∨ g = seed) ∧
        normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom := by
  by_cases hXE : X ≤ E
  · exact Or.inl (ElementaryNormalizerCover.normalizer_le_mathieu_of_nonfirst_kernel_involution
      X hXE t htX ht2 hnt)
  obtain ⟨g,hg,_,_,_,h | h⟩ := source_zero_form_F_branch X hXQ hform hXE t htX htE ht2 hnt
  · exact Or.inr ⟨g,hg,h⟩
  · exact Or.inl h

/-- The same source branch after any ambient conjugation, with literal
conjugators for the two possible linear-five normalizers. -/
theorem source_zero_form_Q_conjugate_normalizer
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXQ : X ≤ Q) (hform : intrinsicElementaryForm X = 0)
    (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) (k : Model) :
    normalizer (X.map (MulAut.conj k).toMonoidHom : Set Model) ≤
        M.map (MulAut.conj k).toMonoidHom ∨
      ∃ g : Model, (g = k ∨ g = k*seed) ∧
        normalizer (X.map (MulAut.conj k).toMonoidHom : Set Model) ≤
          M_F.map (MulAut.conj g).toMonoidHom := by
  rw [← map_equiv_normalizer_eq]
  rcases source_zero_form_Q_normalizer X hXQ hform t htX htE ht2 hnt with h | ⟨g,hg,h⟩
  · exact Or.inl (map_mono h)
  · refine Or.inr ⟨k*g,?_,?_⟩
    · rcases hg with rfl | rfl
      · exact Or.inl (mul_one k)
      · exact Or.inr rfl
    · rw [← conjugate_product]
      exact map_mono h

/-- The source maximal-two-local consumer: in this octad branch maximality
identifies the whole local with a proved Mathieu or linear-five normalizer. -/
theorem source_zero_form_Q_maximal_twoLocal
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXQ : X ≤ Q) (hform : intrinsicElementaryForm X = 0)
    (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) (k : Model)
    (hmax : IsMaximalTwoLocal
      (normalizer (X.map (MulAut.conj k).toMonoidHom : Set Model))) :
    normalizer (X.map (MulAut.conj k).toMonoidHom : Set Model) =
        M.map (MulAut.conj k).toMonoidHom ∨
      ∃ g : Model, (g = k ∨ g = k*seed) ∧
        normalizer (X.map (MulAut.conj k).toMonoidHom : Set Model) =
          M_F.map (MulAut.conj g).toMonoidHom := by
  have hFne : F ≠ ⊥ := by
    intro h
    have hc := F_card
    rw [h,card_bot] at hc
    omega
  have hlocal : IsTwoLocal M_F := by
    rw [M_F_eq_fullNormalizer]
    exact ⟨F,hFne,F_elementary.isPGroup 2,rfl⟩
  rcases source_zero_form_Q_conjugate_normalizer X hXQ hform t htX htE ht2 hnt k
    with h | ⟨g,hg,h⟩
  · exact Or.inl (hmax.eq_of_le
      (ElementaryNormalizerCover.embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k)) h)
  · exact Or.inr ⟨g,hg,hmax.eq_of_le (hlocal.map_equiv (MulAut.conj g)) h⟩

end Janko4.LocalStructure.LinearFive.Geometry
