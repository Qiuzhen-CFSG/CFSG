module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PositiveStar
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion.SinglePrime
public import Theory.GroupTheory.TwoPrimeSolvable
/-!
# Positive odd radicals of actual local components

The original odd radical of a nonquasisimple local component belongs to Xi⁺.
Its odd prime is greater than three, excluding the {2,3} branch of Xi⁻. In
the other branch the quotient automizer is solvable. Perfectness of the
component then makes its Frattini action trivial, contradicting the actual
quaternion subgroup in the Sylow intersection action supplied by A.3.6.

This argument does not use the ratio theorem 3.1.8. Source: the Xi⁺ step in
Aschbacher--Smith, Section 13.1, together with the intrinsic radical action
of A.3.6 and the definitions of Section 3.2.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem frattiniAction_eq_one_of_solvable_automizer
    (L X : Subgroup G) [Group.IsPerfect L]
    (hLX : L ≤ normalizer (X : Set G))
    (hs : Group.IsSolvable (xiQuotientAutomizer X)) :
    ∀ l : L, xiFrattiniAction L X hLX l = 1 := by
  let := hs
  let f : L →* xiQuotientAutomizer X :=
    (xiQuotientNormalizerAction X).rangeRestrict.comp (inclusion hLX)
  let := Group.IsPerfect.range f
  have hfsub : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf (l : L) : f l = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict l) 1)
  intro l
  have hq : xiQuotientNormalizerAction X (inclusion hLX l) = 1 :=
    congrArg Subtype.val (hf l)
  have hh := congrArg (quotientAut (frattini (XiQuotient X))) hq
  rw [map_one] at hh
  exact hh

theorem XiP_mem_XiPlus_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    XiP p L ∈ XiPlus G (T : Subgroup G) := by
  let hA := fun (D : Type u) [Group D] [Finite D] =>
    ChapterA.Section02.theoremA_knownSimple (G := D)
  let hC := fun (D : Type u) [Group D] [Finite D] =>
    ChapterA.Section02.theoremC_knownSimple (G := D)
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
  have hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hD hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hD hO hB
  have hQall : ∀ K ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK KnownSimple.IsKnownSimple ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :=
    fun _ hK => uniqueness_local_quotient_sqtk hG hK.2.2
  have hQ := hQall L hL
  obtain ⟨hp3,hodd⟩ := XiP_oddQuotient_of_A36 hA36 hL hQ hn ho hd
  have hXi : XiP p L ∈ Xi G (T : Subgroup G) :=
    lemma_1_3_3 hA36 hA38 hQall ⟨L,hL,hn,p,Fact.out,ho,hd,rfl⟩
  refine ⟨hXi,?_⟩
  rintro ⟨_,hsmall | ⟨_,haut⟩⟩
  · have hdq : p ∣ Nat.card (XiQuotient (XiP p L)) :=
      hodd.isPGroup.card_eq_or_dvd.resolve_left (Nat.ne_of_gt (hodd.one_lt_card Fact.out))
    rcases hsmall p Fact.out (hdq.trans (card_quotient_dvd_card (pCore 2 (XiP p L)))) with he | he <;> omega
  · let X := XiP p L
    let U : Subgroup G := (T : Subgroup G) ⊓ L
    have hLX : L ≤ normalizer (X : Set G) := XiP_invariant p L.le_normalizer
    let : Group.IsPerfect L := mem_L_isPerfect hL
    have hsol : Group.IsSolvable (xiQuotientAutomizer X) :=
      isSolvable_of_prime_dvd_card_eq_two_or_prime _ (by decide : Nat.Prime 5) haut
    have hall := frattiniAction_eq_one_of_solvable_automizer L X hLX hsol
    let ρ := xiFrattiniAction U X (inf_le_right.trans hLX)
    have hact (t : U) (a : XiFrattiniQuotient X) :
        xiFrattiniAction U X (inf_le_right.trans hLX) t a =
          xiFrattiniAction L X hLX (inclusion inf_le_right t) a := by
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction a using QuotientGroup.induction_on with
        | H a => rfl
    have he (t : U) : ρ t = 1 := by
      ext a
      change xiFrattiniAction U X (inf_le_right.trans hLX) t a = a
      rw [hact,hall]
      rfl
    have hsub : Subsingleton ρ.range := by
      refine ⟨?_⟩
      rintro ⟨a,⟨x,rfl⟩⟩ ⟨b,⟨y,rfl⟩⟩
      exact Subtype.ext ((he x).trans (he y).symm)
    obtain ⟨f,hf⟩ := (XiP_intersection_actions_of_A36 hA36 hL hQ hn ho hd).2
    have hs : Subsingleton (QuaternionGroup 2) := hf.subsingleton
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ≠ 1)
      (Subsingleton.elim _ _)
end CFSG.Quasithin.Chapter13.Section01
