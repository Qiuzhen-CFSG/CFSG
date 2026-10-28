module

public import Theory.GroupTheory.ConjugationFamilyWeakClosure

/-!
# I.2. Structure of nonsplit extensions: fusion criteria

The normalizer criteria of Lemma I.2.4 hold for every conjugation family.
They are proved by induction on its normalizer-step decomposition, with the
reusable argument in `Theory.GroupTheory.ConjugationFamilyWeakClosure`.

This module currently exposes that argument. Identifying the family of
parabolic unipotent radicals in finite groups of Lie type is a separate input
needed for Lemma I.2.5; the general fusion criterion does not assert that
identification. The covering-group and module results I.2.1–I.2.3 also require
separate structural proofs.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §I.2, pp. 409–414 (PDF pp. 420–425).
-/

namespace CFSG.Quasithin.ChapterI.Section02

open SubgroupFusion

variable {G : Type*} [Group G]

/-- Lemma I.2.4(1), in the more general form for any conjugation family.
Normality in each relevant normalizer is expressed by normalizer containment. -/
public theorem lemma_I_2_4_1 (P Q : Subgroup G)
    (family : Subgroup G → Prop) (hfamily : ControlsFusion P family)
    (hQP : Q ≤ P)
    (hnorm : ∀ D, family D → Q ≤ D →
      Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (g : G) (hg : Q.map (MulAut.conj g).toMonoidHom ≤ P) :
    Q.map (MulAut.conj g).toMonoidHom = Q :=
  hfamily.weakly_closed hQP hnorm g hg

/-- Lemma I.2.4(2): a conjugation family with inclusion-reversing normalizers
consists of weakly closed subgroups. -/
public theorem lemma_I_2_4_2 (P Q : Subgroup G)
    (family : Subgroup G → Prop) (hfamily : ControlsFusion P family)
    (hQP : Q ≤ P) (hQ : family Q)
    (hnorm : ∀ D E, family D → family E → D ≤ E →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G))
    (g : G) (hg : Q.map (MulAut.conj g).toMonoidHom ≤ P) :
    Q.map (MulAut.conj g).toMonoidHom = Q :=
  hfamily.member_weakly_closed hQP hQ hnorm g hg

end CFSG.Quasithin.ChapterI.Section02
