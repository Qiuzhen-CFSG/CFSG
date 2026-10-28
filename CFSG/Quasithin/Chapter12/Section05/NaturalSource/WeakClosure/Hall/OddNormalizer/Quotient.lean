module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Setup
public import Theory.SpecificGroups.Classical.BinaryFiveRanks
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.PCoreCoverEquiv
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The actual exterior quotient excludes the exceptional odd-normalizer rows

The list in 4.4.3(2) is a list of actual quotient groups. The marked PSL₅(2)
has cubic rank at least two, unlike every binary PSL₂, and its order is
divisible by 31, unlike the other rows. For the unitary row it suffices that
PSU₃(3) is a section of GL₃(9); no unitary order classification is needed.

A subgroup covering L modulo O₂(L) inherits the marking through its literal
inclusion. This applies to the odd-actor residual and to the intersection
residual in the pushing-up configuration, without assuming their uniqueness.

Source: Aschbacher--Smith, 4.2.12--13 and 4.4.3--6, pp.610--612,619--620;
the PSL₅(2) use in 12.2.11(a), pp.798--799.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4.Section04

/-- The complete quotient list of 4.4.3(2). The triple cover retains both
its central quotient and its center of order three. -/
def OddNormalizerExceptionalQuotient (Q : Type*) [Group Q] : Prop :=
  (∃ n : ℕ, ClassicalGroup.IsPSL Q 2 (2 ^ n)) ∨
  ClassicalGroup.IsPSL Q 3 2 ∨ ClassicalGroup.IsPSL Q 4 2 ∨
  Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
  (IsQuasisimple Q ∧ Nat.card (center Q) = 3 ∧
    Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 6))) ∨
  ClassicalGroup.IsPSU Q 3 3

private theorem binary_five_card :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  calc
    _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
      simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hc
    _ = 9999360 := by decide

private theorem not_exceptional_of_binary_five {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :
    ¬ OddNormalizerExceptionalQuotient Q := by
  have hcard : Nat.card Q = 9999360 := (Nat.card_congr e.toEquiv).trans binary_five_card
  have h31 : 31 ∣ Nat.card Q := by rw [hcard]; decide
  rintro (⟨n, F, hF, hfin, hFcard, ⟨f⟩⟩ | h3 | h4 | h6 | h7 | hhat | hu)
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hFcard)
    have hge : 2 ≤ primeRank 3 Q := by
      rw [primeRank_equiv 3 e]
      exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
    have hle : primeRank 3 Q ≤ 1 := by
      rw [primeRank_equiv 3 (f.trans (Theory.PSL2.sl2QuotientEquiv F).symm)]
      exact Matrix.SL2.binary_odd_primeRank_le_one (by decide)
    omega
  · obtain ⟨F, _, _, hF, ⟨f⟩⟩ := h3
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF, Fin.prod_univ_succ] at hc
    rw [Nat.card_congr f.toEquiv, hc] at h31
    norm_num at h31
  · obtain ⟨F, _, _, hF, ⟨f⟩⟩ := h4
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF, Fin.prod_univ_succ] at hc
    rw [Nat.card_congr f.toEquiv, hc] at h31
    norm_num at h31
  · obtain ⟨h6⟩ := h6
    rw [Nat.card_congr h6.toEquiv, nat_card_alternatingGroup] at h31
    norm_num at h31
  · obtain ⟨h7⟩ := h7
    rw [Nat.card_congr h7.toEquiv, nat_card_alternatingGroup] at h31
    norm_num at h31
  · obtain ⟨_, hz, ⟨f⟩⟩ := hhat
    rw [card_eq_card_quotient_mul_card_subgroup (center Q), hz,
      Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at h31
    norm_num at h31
  · obtain ⟨F, _, _, J, hF, _, ⟨f⟩⟩ := hu
    have hd : Nat.card Q ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) := by
      rw [Nat.card_congr f.toEquiv]
      exact (card_map_dvd J.specialSubgroup Matrix.ProjGenLinGroup.mk).trans
        J.specialSubgroup.card_subgroup_dvd_card
    have hbad := h31.trans hd
    let : Fintype F := Fintype.ofFinite F
    rw [Matrix.card_GL_field (𝔽 := F) 3] at hbad
    have hF' : Fintype.card F = 9 := by simpa only [Nat.card_eq_fintype_card, Nat.reducePow] using hF
    norm_num [hF', Fin.prod_univ_succ] at hbad

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Every exceptional quotient in 4.4.3 is excluded by the original marking. -/
theorem ExteriorMarking.not_oddNormalizerExceptionalQuotient (a : ExteriorMarking D) :
    ¬ OddNormalizerExceptionalQuotient (L ⧸ pCore 2 L) :=
  not_exceptional_of_binary_five
    (a.quotientEquiv.trans Representation.SL5TenDimensional.projectiveEquiv)

/-- A literal cover inherits the marked quotient on each representative,
as well as exclusion of the full exceptional list. -/
theorem ExteriorMarking.cover_quotient (a : ExteriorMarking D)
    {I : Subgroup G} (hIL : I ≤ L)
    (hcover : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G)) :
    (∃ e : (I ⧸ pCore 2 I) ≃* Representation.SL5TenDimensional.Group,
      ∀ i : I, e (QuotientGroup.mk' (pCore 2 I) i) =
        a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hIL i))) ∧
      ¬ OddNormalizerExceptionalQuotient (I ⧸ pCore 2 I) := by
  obtain ⟨e, he⟩ := exists_pCoreQuotientEquiv_of_cover hIL hcover
  exact ⟨⟨e.trans a.quotientEquiv, fun i => congrArg a.quotientEquiv (he i)⟩,
    not_exceptional_of_binary_five
      (e.trans (a.quotientEquiv.trans Representation.SL5TenDimensional.projectiveEquiv))⟩

/-- The actual fixed residual of 4.4.5 has the same marked PSL₅(2)
quotient; no residual-uniqueness hypothesis is used. -/
theorem ExteriorMarking.oddActorResidual_quotient (a : ExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ a.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    (∃ e : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃*
        Representation.SL5TenDimensional.Group,
      ∀ i : oddActorResidual L A, e (QuotientGroup.mk' (pCore 2 _) i) =
        a.quotientEquiv (QuotientGroup.mk' (pCore 2 L)
          (inclusion ((oddActorResidual_le L A).trans inf_le_left) i))) ∧
      ¬ OddNormalizerExceptionalQuotient
        (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) := by
  exact a.cover_quotient ((oddActorResidual_le L A).trans inf_le_left)
    (a.centralizing_actor_cover h A hAM hodd hAV).1.subset

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
