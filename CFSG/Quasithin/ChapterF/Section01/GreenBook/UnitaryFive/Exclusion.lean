module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.RankObstruction
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Setup

/-!
# Excluding the nonexceptional unitary-five amalgams

The actual line parabolic contains a nontrivial normal two-subgroup and,
for every even prime power other than four, an elementary abelian subgroup
of odd-prime rank three. These two calculations exclude its embedding in
any finite quasithin group. Transport along the left parabolic equivalence
gives the recognition consumer. The same argument applies to extensions:
the base parabolic embeds in the extended endpoint, even though its normal
two-subgroup need not be normal in that endpoint.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12, final paragraph, printed p.264; compare A.2.18, printed p.40.
-/

public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive

open Theory.GroupTheory

namespace Model

variable {q : ℕ} (M : Model q)

/-- The concrete parabolic obstruction, with both matrix calculations discharged. -/
theorem not_quasithin_of_left_embedding
    (hq : IsPrimePow q) (heven : Even q) (hne : q ≠ 4)
    {G : Type*} [Group G] [Finite G]
    (f : M.leftParabolic →* G) (hf : Function.Injective f) :
    ¬ IsQuasithin G := by
  obtain ⟨p, hp, ho, _, hr⟩ := exists_odd_prime_parabolic_rank hq heven hne M
  exact Theory.Quasithin.not_quasithin_of_embedded_normal_two_rank f hf
    M.leftNormalTwoSubgroup M.leftNormalTwoSubgroup_ne_bot
    M.leftNormalTwoSubgroup_isPGroup p hp ho hr

/-- An actual line-parabolic embedding in a quasithin completion forces q = 4. -/
theorem field_size_eq_four_of_parabolic_embedding
    (hq : IsPrimePow q) (heven : Even q)
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    (f : M.leftParabolic →* G) (hf : Function.Injective f) : q = 4 := by
  by_contra hne
  exact M.not_quasithin_of_left_embedding hq heven hne f hf hG

/-- Recognition needs only the left endpoint isomorphism, with no rank or core premise. -/
theorem field_size_eq_four_of_parabolic_equiv
    (hq : IsPrimePow q) (heven : Even q)
    {G B R : Type*} [Group G] [Finite G] [Group B] [Group R]
    (hG : IsQuasithin G) (P : Subgroup G)
    {α : RankTwoAmalgam P B R} (e : RankTwoAmalgam.ParabolicEquiv α M.amalgam) :
    q = 4 :=
  M.field_size_eq_four_of_parabolic_embedding hq heven hG
    (P.subtype.comp e.left.symm.toMonoidHom)
    (Subtype.val_injective.comp e.left.symm.injective)

/-- An extension endpoint is sufficient: compose the base-parabolic embedding
with the actual endpoint equivalence and the completion's subgroup inclusion. -/
theorem field_size_eq_four_of_extended_parabolic_equiv
    (hq : IsPrimePow q) (heven : Even q)
    {G E B R D T : Type*} [Group G] [Finite G]
    [Group E] [Group B] [Group R] [Group D] [Group T]
    (hG : IsQuasithin G) (P : Subgroup G)
    {α : RankTwoAmalgam P B R} {β : RankTwoAmalgam E D T}
    (e : RankTwoAmalgam.ParabolicEquiv α β)
    (ι : M.leftParabolic →* E) (hι : Function.Injective ι) : q = 4 :=
  M.field_size_eq_four_of_parabolic_embedding hq heven hG
    ((P.subtype.comp e.left.symm.toMonoidHom).comp ι)
    ((Subtype.val_injective.comp e.left.symm.injective).comp hι)

/-- The U₅(2) extension branch of F.1.12 is impossible in a quasithin completion.
The extension may be arbitrary; only its genuine base-endpoint embedding is used. -/
theorem not_quasithin_of_two_extension
    (M : Model 2)
    {G E B R D T : Type*} [Group G] [Finite G]
    [Group E] [Group B] [Group R] [Group D] [Group T]
    (P : Subgroup G)
    {α : RankTwoAmalgam P B R} {β : RankTwoAmalgam E D T}
    (e : RankTwoAmalgam.ParabolicEquiv α β)
    (ι : M.leftParabolic →* E) (hι : Function.Injective ι) :
    ¬ IsQuasithin G := by
  intro hG
  have h := M.field_size_eq_four_of_extended_parabolic_equiv
    Nat.prime_two.isPrimePow (by decide) hG P e ι hι
  exact (by decide : (2 : ℕ) ≠ 4) h

end Model

/-- A unitary-five amalgam is identified with the concrete flag model by
three isomorphisms commuting with both overlap inclusions. -/
@[expose] def IsAmalgam {L B R : Type*} [Group L] [Group B] [Group R]
    (q : ℕ) (α : RankTwoAmalgam L B R) : Prop :=
  ∃ M : Model q, Nonempty (RankTwoAmalgam.Iso α M.amalgam)

/-- The finite-field construction supplies the actual marked model. -/
theorem standardModel_isAmalgam {q : ℕ} (hq : IsPrimePow q) (heven : Even q) :
    IsAmalgam q (standardModel hq heven).amalgam :=
  ⟨standardModel hq heven, ⟨RankTwoAmalgam.Iso.refl _⟩⟩

/-- The recognized unitary branch in a quasithin completion is the U₅(4)
amalgam, retaining both commuting squares of the recognition isomorphism. -/
theorem isAmalgam_four_of_quasithin
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    {G B R : Type*} [Group G] [Finite G] [Group B] [Group R]
    (hG : IsQuasithin G) (P : Subgroup G)
    {α : RankTwoAmalgam P B R} (h : IsAmalgam q α) : IsAmalgam 4 α := by
  obtain ⟨M, ⟨e⟩⟩ := h
  have hq4 := M.field_size_eq_four_of_parabolic_equiv hq heven hG P e.toParabolicEquiv
  subst q
  exact ⟨M, ⟨e⟩⟩

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive
