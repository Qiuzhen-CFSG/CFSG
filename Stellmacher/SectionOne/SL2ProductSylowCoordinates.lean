module
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Theory.GroupTheory.CenterlessProduct
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow coordinates in a normal product of SL₂(2) factors

If E is a normal internal product of SL₂(2) subgroups, a Sylow subgroup S
meets each factor in order two. These intersections generate S ∩ E, which
is elementary abelian of order 2 to the number of factors. This is the
pure group calculation behind the offender inequality in Stellmacher (1.7),
Journal of Algebra 190 (1997), p.19, in `refs/latex/stellmacher-n-group.tex`.

First restrict S to a Sylow subgroup of E and use normality of each
order-six factor to compute its intersection. Distinct factors commute
and are centerless, hence are independent of the joins of the other
factors. Product counting gives |E|=6^n and order 2^n for the join R of
the intersections. The 2-group S ∩ E has order dividing 6^n, so its order
is at most 2^n. Since it contains R, they are equal. Commuting square-one
generators make this join elementary abelian. This argument uses genuine
family independence, not just pairwise trivial intersections.
-/

namespace Stellmacher.SectionOne
open RankOneThreeGroupAssembly

private theorem elementary_iSup_card_two
    {G I : Type*} [Group G] [Finite G]
    (Q : I → Subgroup G) (hcard : ∀ i, Nat.card (Q i) = 2)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ Q i → y ∈ Q j → Commute x y) :
    IsElementaryAbelian 2 ↥(⨆ i, Q i) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc (i : I) : IsCyclic (Q i) := isCyclic_of_prime_card (hcard i)
  have hQQ : (⨆ i, Q i) ≤ Subgroup.centralizer (⨆ i, Q i : Subgroup G) := by
    apply iSup_le
    intro i
    rw [Subgroup.le_centralizer_iff]
    apply iSup_le
    intro j
    by_cases hij : i = j
    · subst j
      let _ : IsCyclic (Q i) := hcyc i
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcomm hij x y hx hy).eq
  let R : Subgroup G := ⨆ i, Q i
  let _ : IsMulCommutative R := Subgroup.le_centralizer_iff_isMulCommutative.mp hQQ
  have hpow : ∀ x ∈ R, x ^ 2 = 1 := by
    intro x hx
    change x ∈ (⨆ i, Q i : Subgroup G) at hx
    rw [Subgroup.iSup_eq_closure] at hx
    apply Subgroup.closure_induction (p := fun x _ => x ^ 2 = 1) ?_ ?_ ?_ ?_ hx
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have hh := pow_card_eq_one' (x := (⟨x, hi⟩ : Q i))
      rw [hcard i] at hh
      exact congrArg Subtype.val hh
    · simp
    · intro x y hx hy hxp hyp
      have hxy : Commute x y := by
        have hh := (IsMulCommutative.is_comm (M := R)).comm
          (⟨x, by simpa only [R, Subgroup.iSup_eq_closure] using hx⟩ : R)
          (⟨y, by simpa only [R, Subgroup.iSup_eq_closure] using hy⟩ : R)
        exact congrArg Subtype.val hh
      rw [hxy.mul_pow, hxp, hyp, one_mul]
    · intro x _ hx
      simp [inv_pow, hx]
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  exact Subtype.ext (hpow x x.property)

private theorem coordinates_of_card_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E : Subgroup G)
    (F : Finset (Subgroup G)) (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsSL2Two D)
    (hcoord : ∀ D ∈ F, Nat.card ↥((S : Subgroup G) ⊓ D) = 2) :
    IsElementaryAbelian 2 ↥((S : Subgroup G) ⊓ E) ∧
    ((S : Subgroup G) ⊓ E) =
      ⨆ D : {D : Subgroup G // D ∈ F}, (S : Subgroup G) ⊓ D.val ∧
    Nat.card ↥((S : Subgroup G) ⊓ E) = 2 ^ F.card := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let _ : Fintype I := Fintype.ofFinite I
  have hIcard : Fintype.card I = F.card := Fintype.card_coe F
  let H : I → Subgroup G := fun i => i.val
  let Q : I → Subgroup G := fun i => (S : Subgroup G) ⊓ i.val
  have hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact hprod.2.2.2 i i.property j j.property
      (fun heq => hij (Subtype.ext heq)) x hx y hy
  have hind : iSupIndep H := Subgroup.iSupIndep_of_centerless_of_pairwise_commute H
    (fun i => center_eq_bot_of_isSL2Two (hF i i.property)) hcomm
  have hQcomm : Pairwise fun i j => ∀ x y : G, x ∈ Q i → y ∈ Q j → Commute x y := by
    intro i j hij x y hx hy
    exact hcomm hij x y hx.2 hy.2
  have hcardE : Nat.card E = 6 ^ F.card := by
    rw [hprod.1]
    have hh := Subgroup.natCard_iSup_of_iSupIndep H hcomm hind
    simpa [H, hIcard,
      show ∀ i : I, Nat.card (H i) = 6 from fun i => isSL2Two_card (hF i i.property)] using hh
  let R : Subgroup G := ⨆ i, Q i
  have hRcard : Nat.card R = 2 ^ F.card := by
    have hh := Subgroup.natCard_iSup_of_iSupIndep Q hQcomm
      (hind.mono (fun i => inf_le_right))
    simpa [R, hIcard, show ∀ i : I, Nat.card (Q i) = 2 from fun i => hcoord i i.property] using hh
  have hRle : R ≤ (S : Subgroup G) ⊓ E := by
    refine iSup_le fun i => le_inf inf_le_left ?_
    exact inf_le_right.trans (by rw [hprod.1]; exact le_iSup H i)
  have hTcard : Nat.card ↥((S : Subgroup G) ⊓ E) ≤ 2 ^ F.card := by
    have hp := S.isPGroup'.to_le (show (S : Subgroup G) ⊓ E ≤ (S : Subgroup G) from inf_le_left)
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdiv : 2 ^ n ∣ 6 ^ F.card := by
      rw [← hn, ← hcardE]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (2 ^ n) (3 ^ F.card) :=
      (show Nat.Coprime 2 3 by decide).pow n F.card
    have hdiv2 : 2 ^ n ∣ 2 ^ F.card := by
      apply hcop.dvd_of_dvd_mul_right
      simpa only [← mul_pow, show 2 * 3 = 6 from rfl] using hdiv
    have hnle := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hdiv2
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  have heq : R = (S : Subgroup G) ⊓ E :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hRcard]; exact hTcard)
  refine ⟨?_, heq.symm, ?_⟩
  · rw [← heq]
    exact elementary_iSup_card_two Q (fun i => hcoord i i.property) hQcomm
  · rw [← heq]
    exact hRcard

public theorem sl2_product_sylow_coordinates
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E : Subgroup G) (hEnormal : E.Normal)
    (F : Finset (Subgroup G)) (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsSL2Two D) :
    IsElementaryAbelian 2 ↥((S : Subgroup G) ⊓ E) ∧
    ((S : Subgroup G) ⊓ E) =
      ⨆ D : {D : Subgroup G // D ∈ F}, (S : Subgroup G) ⊓ D.val ∧
    Nat.card ↥((S : Subgroup G) ⊓ E) = 2 ^ F.card ∧
    ∀ D ∈ F, Nat.card ↥((S : Subgroup G) ⊓ D) = 2 := by
  let _ : E.Normal := hEnormal
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal E
  have hcoord (D : Subgroup G) (hDF : D ∈ F) :
      Nat.card ↥((S : Subgroup G) ⊓ D) = 2 := by
    have hDE : D ≤ E := by
      rw [hprod.1]
      exact le_iSup (fun i : {i : Subgroup G // i ∈ F} => i.val) ⟨D, hDF⟩
    let _ : (D.subgroupOf E).Normal := hprod.2.1 D hDF
    have hDcard : Nat.card (D.subgroupOf E) = 6 := by
      rw [natCard_subgroupOf_eq D E hDE]
      exact isSL2Two_card (hF D hDF)
    have hh := natCard_inf_sylow_normal_card_six T (D.subgroupOf E) hDcard
    have hinf : (T : Subgroup E) ⊓ D.subgroupOf E =
        ((S : Subgroup G) ⊓ D).subgroupOf E := by
      rw [hT]
      rfl
    rw [hinf, natCard_subgroupOf_eq _ E (inf_le_right.trans hDE)] at hh
    exact hh
  obtain ⟨helem, hgen, hcard⟩ := coordinates_of_card_two S E F hprod hF hcoord
  exact ⟨helem, hgen, hcard, hcoord⟩

end Stellmacher.SectionOne
