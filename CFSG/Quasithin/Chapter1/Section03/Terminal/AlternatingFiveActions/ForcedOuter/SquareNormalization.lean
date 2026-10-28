module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter.Setup
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CenterlessProduct
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Quasithin.Rank

/-!
# Squares preserve the swapped A₅ component

The image of the relative C-component B in H/O₂(H) is isomorphic to its
intrinsic quotient B/O₂(B), hence to the actual alternating group A₅.
It is therefore an ordinary, centerless component. Three distinct such
components commute and contain an embedded product of three order-three
subgroups. Strong quasithinness excludes that product, since odd-prime rank
does not increase on quotienting by the two-core.

If an element's square moved the quotient component, its first three
conjugates would be distinct. Thus every square preserves the image, and
normalizer transport through the solvable two-core lifts this to B. Applying
this to the supplied actors in N_T(P) gives the required source assertion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 1.3.9(1), printed p.514/PDF p.531;
the component-orbit rank argument specializes Proposition A.3.8(3), pp.45–46.
-/

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.ForcedOuter

private theorem center_bot_of_a5 {D : Type*} [Group D]
    (e : D ≃* alternatingGroup (Fin 5)) : center D = ⊥ := by
  apply bot_unique
  intro x hx
  have hz := (centerCongr e ⟨x, hx⟩).property
  change e x ∈ center (alternatingGroup (Fin 5)) at hz
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  exact mem_bot.mpr (e.injective (hz.trans e.map_one.symm))

private theorem rank_three_of_distinct_a5_components
    {D : Type*} [Group D] [Finite D] (L : Fin 3 → Subgroup D)
    (hc : ∀ i, IsComponent D (L i)) (hn : Function.Injective L)
    (e : ∀ i, L i ≃* alternatingGroup (Fin 5)) : 3 ≤ primeRank 3 D := by
  classical
  have hcomm : Pairwise fun i j => ∀ x y : D, x ∈ L i → y ∈ L j → Commute x y := by
    intro i j hij x y hx hy
    have hh := (hc i).commutator_eq_bot_of_ne (hc j) (fun he => hij (hn he))
    exact (commutator_eq_bot_iff_le_centralizer.mp hh hx y hy).symm
  have hind := iSupIndep_of_centerless_of_pairwise_commute L
    (fun i => center_bot_of_a5 (e i)) hcomm
  have hdiv (i : Fin 3) : 3 ∣ Nat.card (L i) := by
    rw [Nat.card_congr (e i).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  choose z hz using fun i => exists_prime_orderOf_dvd_card' (G := L i) 3 (hdiv i)
  let C (i : Fin 3) := zpowers (z i)
  let (i : Fin 3) : CommGroup (C i) := IsCyclic.commGroup
  have hcard (i : Fin 3) : Nat.card (C i) = 3 := (Nat.card_zpowers (z i)).trans (hz i)
  let f : (∀ i, L i) →* D := noncommPiCoprod hcomm
  have hf : Function.Injective f := injective_noncommPiCoprod_of_iSupIndep hind
  let g : (∀ i, C i) →* D :=
    { toFun := fun a => f (fun i => (a i : L i))
      map_one' := f.map_one
      map_mul' := fun a b => f.map_mul _ _ }
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 3) ?_ ?_ g
  · intro a b hab
    have he : (fun i => (a i : L i)) = fun i => (b i : L i) := hf hab
    funext i
    exact Subtype.ext (congrFun he i)
  · intro a
    funext i
    change a i ^ 3 = 1
    simpa only [hcard i] using pow_card_eq_one' (x := a i)
  · rw [Nat.card_pi]
    simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem squares_normalize_a5_component
    {D : Type*} [Group D] [Finite D] {L : Subgroup D}
    (hL : IsComponent D L) (e : L ≃* alternatingGroup (Fin 5))
    (hrank : primeRank 3 D ≤ 2) (s : D) : s ^ 2 ∈ normalizer L := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change L.conjBy (s ^ 2) = L
  by_contra h2
  have h1 : L.conjBy s ≠ L := by
    intro he
    apply h2
    rw [pow_two, conjBy_mul, he, he]
  have h21 : L.conjBy (s ^ 2) ≠ L.conjBy s := by
    intro he
    have hh := congrArg (fun K : Subgroup D => K.conjBy s⁻¹) he
    rw [pow_two, conjBy_mul, conjBy_inv, conjBy_inv] at hh
    exact h1 hh
  let a : Fin 3 → D := ![1, s, s ^ 2]
  let C : Fin 3 → Subgroup D := fun i => L.conjBy (a i)
  have hc : ∀ i, IsComponent D (C i) := fun i => hL.map_conj (a i)
  have hn : Function.Injective C := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [C, a] at hij
    all_goals try simp only [conjBy_one] at hij
    · rfl
    · exact (h1 hij.symm).elim
    · exact (h2 hij.symm).elim
    · exact (h1 hij).elim
    · rfl
    · exact (h21 hij.symm).elim
    · exact (h2 hij).elim
    · exact (h21 hij).elim
    · rfl
  let ei (i : Fin 3) : C i ≃* alternatingGroup (Fin 5) :=
    ((MulAut.conj (a i)).subgroupMap L).symm.trans e
  have hge := rank_three_of_distinct_a5_components C hc hn ei
  omega

variable {G : Type*} [Group G] [Finite G]
variable {𝒦 : GroupClass} {p : ℕ} {T X P H B : Subgroup G}

/-- Every square in the actual complement normalizer preserves the A₅
C-component, using only the supplied local source hypotheses. -/
public theorem SourceInput.squares_normalize (h : SourceInput 𝒦 p T X P H B) :
    ∀ s ∈ T ⊓ normalizer P, s ^ 2 ∈ normalizer B := by
  let A := B.subgroupOf H
  let Q := H ⧸ pCore 2 H
  let q : H →* Q := QuotientGroup.mk' (pCore 2 H)
  let L : Subgroup Q := A.map q
  have hA : A.IsCComponent := h.component.2
  let := pCore_isNilpotent (p := 2) (G := H)
  have hL : L.IsCComponent := hA.map_quotient (pCore 2 H)
  let eB : (A ⧸ pCore 2 A) ≃* XiQuotient B :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe h.component.1)
      (pCore_map_iso 2 _)
  let e : L ≃* alternatingGroup (Fin 5) :=
    (cComponentTwoCoreQuotientEquiv hA).symm.trans (eB.trans h.alternating_five.some)
  have hcenter : center L = ⊥ := center_bot_of_a5 e
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup L := e.isSimpleGroup_congr.mpr inferInstance
  let : Group.IsPerfect L := hL.perfect
  have hordinary : IsComponent Q L := by
    refine ⟨hL.subnormal, ?_⟩
    exact { simple := ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot).isSimpleGroup_congr.mpr inferInstance }
  have hrank : primeRank 3 Q ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin 3 (by decide) (by decide))
  intro s hs
  have hTH : T ≤ H := h.generated ▸ le_sup_right
  let sH : H := ⟨s, hTH hs.1⟩
  have hm := squares_normalize_a5_component hordinary e hrank (q sH)
  have hmA : sH ^ 2 ∈ normalizer A := by
    rw [← normalizer_cComponent_quotient hA (pCore 2 H)]
    change q (sH ^ 2) ∈ normalizer L
    simpa only [map_pow] using hm
  rw [← subgroupOf_normalizer_eq h.component.1] at hmA
  exact hmA

end CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
