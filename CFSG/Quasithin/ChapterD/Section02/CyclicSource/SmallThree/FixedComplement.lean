module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplementBudget
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplementCancellation
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportOrders
public import Theory.PGroupCore

/-!
# Fixed complements for the D.2.25 small-three branch

For the canonical order-three factors, an involution either swaps two
factors or normalizes all factors. In the swap case, the transposition
support lemma saturates its displacement and fixes the complement. In the
normalized case, inversion of one factor contributes a binary displacement
line. If the canonical fixed complement were moved, the remaining line is
an inverted three-core support. The cancellation lemma then constructs a
new canonical factor supported in the fixed complement, contradicting the
canonical family. Thus every noncentral source small-support involution fixes the
canonical complement.

The theorem leaves the residual three-core mover as an explicit premise;
`CyclicSource.RestrictedInverter` supplies it from the original Fitting,
odd-complement and full-movement hypotheses.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.25, printed p.190, `refs/quasithin.pdf`.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
  [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

private theorem inverted_threeCore_cubic (t x : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V)=4)
    (hx : x∈pCore 3 G) (hne : x≠1) (hinv : t*x*t⁻¹=x⁻¹) : x^3=1 := by
  have hp : IsPGroup 3 (pCore 3 G) := pCore_isPGroup
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hodd : Odd (orderOf x) :=
    (show Odd (Nat.card (pCore 3 G)) from hn.symm ▸ (by decide : Odd 3).pow).of_dvd_nat ((pCore 3 G).orderOf_dvd_natCard hx)
  have hf : fixingSubgroup G (Set.univ : Set V)=⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α:=V)
    intro v
    simpa only [one_smul] using ((mem_fixingSubgroup_iff (M:=G)).mp hg v trivial)
  have ho := invertedOddElement_order_three_or_five_of_small_involution_support
    (V:=V) x t hne hodd ht hinv (by rw [hcard]) hf
  have hd : 3 ∣ orderOf x := by
    have hh := hp.dvd_orderOf (g:=(⟨x,hx⟩:pCore 3 G))
      (fun he => hne (congrArg Subtype.val he))
    rwa [←orderOf_injective (pCore 3 G).subtype (pCore 3 G).subtype_injective] at hh
  have hthree : orderOf x=3 := by
    rcases ho with he | he
    · exact he
    · rw [he] at hd
      norm_num at hd
  rw [←hthree]
  exact pow_orderOf_eq_one x

/-- The local fixed-complement conclusion of D.2.25. The residual witness
is supplied on the actual fixed subrepresentation by cyclic preparation. -/
theorem fixed_complement_of_residual_witness
    (t : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V)=4)
    (hsplit : IsCompl (commutatorAction (smallSupportGroup G V 1) V)
      (FixedPoints.subgroup (smallSupportGroup G V 1) V))
    (hnoncentral : ¬ ∀ y∈smallSupportGroup G V 1, Commute t y)
    (hwitness : Nat.card (commutatorSubgroup (Subgroup.zpowers t) V
        (FixedPoints.subgroup (smallSupportGroup G V 1) V))=2 →
      ∃x∈pCore 3 G, t*x*t⁻¹=x⁻¹ ∧
        ∃v∈FixedPoints.subgroup (smallSupportGroup G V 1) V,x • v≠v) :
    ∀v∈FixedPoints.subgroup (smallSupportGroup G V 1) V,t • v=v := by
  classical
  by_cases hnorm : ∀ P ∈ smallSupportFactors G V 1,
      t∈Subgroup.normalizer (P:Set G)
  swap
  · exact fixed_complement_of_transposition t ht hcard hsplit hnorm
  have hnot : ¬ ∀ P∈smallSupportFactors G V 1,∀p∈P,Commute t p := by
    intro hh
    apply hnoncentral
    have hle : smallSupportGroup G V 1 ≤ Subgroup.centralizer ({t}:Set G) := by
      rw [smallSupportGroup_eq_iSup]
      apply iSup_le
      intro P p hp
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hh P P.property p hp).symm.eq
    intro y hy
    exact (show Commute y t from Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  push Not at hnot
  obtain ⟨P,hP,p,hp,htp⟩ := hnot
  have hiP := (centralizes_or_inverts_prime_subgroup_of_sq_eq_one P
    (by rw [hP.2.1]; decide) t ht.2 (hnorm P hP)).resolve_left
      (fun hh => htp (hh p hp))
  by_contra! hm
  obtain ⟨hline,hothers⟩ := normalized_inverted_factor_budget t ht hcard hnorm hP hiP hm
  obtain ⟨x,hx,hinv,v,hv,hmx⟩ := hwitness hline
  have hne : x≠1 := by intro he; rw [he,one_smul] at hmx; exact hmx rfl
  have hx3 := inverted_threeCore_cubic (V:=V) t x ht hcard hx hne hinv
  have hxcentral := inverted_cubic_centralizes_factors (V:=V) t x ht hx3 hinv hnorm
  have hxother : ∀ Z∈smallSupportFactors G V 1,Z≠P →
      ∀w∈commutatorAction Z V,x • w=w := by
    intro Z hZ hZP
    apply ActionSupport.inverted_cubic_fixes_fixed_support t x ht hx3 hinv
    · intro w hw
      have hn : x∈Subgroup.normalizer (Z:Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
          (fun z hz => (hxcentral Z hZ z hz).symm.eq))
      have hs := commutatorAction_isInvariant_of_normalizing_actor
        (V:=V) (Subgroup.zpowers x) Z (Subgroup.zpowers_le.mpr hn)
      exact (hs.invariant ⟨x,Subgroup.mem_zpowers x⟩ w).mp hw
    · exact hothers Z hZ hZP
  let W := FixedPoints.subgroup (smallSupportGroup G V 1) V
  let _ : IsInvariant G V W := canonical_fixed_isInvariant
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat (by decide : Odd 3)
    (orderOf_dvd_of_pow_eq_one hx3)
  have hfour := ActionSupport.inverted_support_card_four_on_restriction W t x ht hodd hinv hline ⟨v,hv,hmx⟩
  exact smallThree_fixedComplement_cancellation hP x ((pCore_le_fitting G 3) hx)
    hx3 (hxcentral P hP) hxother hsplit.symm.sup_eq_top hfour
end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
