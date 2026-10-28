module

public import CFSG.Quasithin.Chapter2.Section01To03.Elementary
public import CFSG.Quasithin.Chapter1.Defs
public import Theory.GroupTheory.PGroup.SylowNormalizerOrbit
public import Theory.GroupTheory.PGroup.NormalCyclicFour
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
public import Theory.SpecificGroups.DihedralEightProduct

/-!
# The normalizer maximality step in the final A₆ shadow

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, p.570, the completion following Lemma 2.5.27.

For a local pair `(U,L)` of maximal base order, an element `x` normalizing
`A` but outside `U` enlarges `U` inside the two-group `T ∩ ⟨L,x⟩`.
If `|S| ≤ 2|U|`, its order is at least that of the Sylow subgroup `S` of
`H ∈ Γ*`. Since `A` is a nontrivial normal two-subgroup of its normalizer,
that normalizer belongs to `Γ`, and the superscript-star maximality puts
it in `Γ*` as well.

These are conditional finite-group steps. This module does not yet prove
Lemmas 2.5.21–27, construct the required `A ≅ E₁₆` and local pair, or
deduce characteristic two for `N_G(A)`. Those premises must be discharged
before concluding the source contradiction. The characteristic-two family
in the final normalizer lemma is the actual `Chapter1.He`.
-/

namespace CFSG.Quasithin.Chapter2

open Subgroup

variable {G : Type*} [Group G]
variable {E : Set (Subgroup G)} {M H N U L : Subgroup G}

/-- Transport superscript-star maximality using a local pair with globally
maximal first-coordinate order and the required lower bound on the 2-part.
This uses neither the subscript-star condition nor a supposed inclusion
between the two starred families. -/
public theorem gammaStar_of_largest_localPair_of_twoPart_le
    (hH : H ∈ gammaStar E M) (hN : twoCore N ≠ ⊥)
    (hpair : (U, L) ∈ localPairsIn E M N)
    (hmax : ∀ V ∈ localBases E M, Nat.card V ≤ Nat.card U)
    (hsize : twoPart H ≤ twoPart N) : N ∈ gammaStar E M := by
  refine ⟨⟨⟨hN, (U, L), hpair⟩, (U, L), hpair, hmax⟩, ?_⟩
  intro J hJ
  exact (hH.2 J hJ).trans hsize

variable [Finite G]

private theorem two_mul_card_le_of_lt {U R : Subgroup G} (hlt : U < R) :
    2 * Nat.card U ≤ Nat.card R := by
  have hzero : U.relIndex R ≠ 0 := (U.subgroupOf R).index_ne_zero_of_finite
  have hone : U.relIndex R ≠ 1 := fun he => hlt.not_ge (relIndex_eq_one.mp he)
  have htwo : 2 ≤ U.relIndex R := by omega
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) U R bot_le hlt.le
  simp only [relIndex_bot_left] at hcard
  calc
    2 * Nat.card U = Nat.card U * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card U * U.relIndex R := Nat.mul_le_mul_left _ htwo
    _ = Nat.card R := hcard

/-- The p.570 maximality step, from the actual local pair, an outside
normalizing element, and the index-two size bound. In the source
`U = N_S(A)`, `L = N_H(A)`, and `I = ⟨L,x⟩`. Membership of `N_G(A)` in
either `Γ` or a starred family is derived, not assumed. -/
public theorem normalizer_mem_gammaStar_of_crossing_element
    (hH : H ∈ gammaStar (Chapter1.He G) M)
    (S : Sylow 2 H) (A T : Subgroup G)
    (hAne : A ≠ ⊥) (hA : IsPGroup 2 A) (hT : IsPGroup 2 T)
    (hpair : (U, L) ∈ localPairs (Chapter1.He G) M)
    (hmax : ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hLN : L ≤ normalizer (A : Set G)) (hUT : U ≤ T)
    {x : G} (hxT : x ∈ T) (hxN : x ∈ normalizer (A : Set G)) (hxU : x ∉ U)
    (hsize : Nat.card (S : Subgroup H) ≤ 2 * Nat.card U) :
    normalizer (A : Set G) ∈ gammaStar (Chapter1.He G) M := by
  let I : Subgroup G := L ⊔ zpowers x
  let R : Subgroup G := T ⊓ I
  have hIN : I ≤ normalizer (A : Set G) := sup_le hLN (zpowers_le.mpr hxN)
  have hUR : U ≤ R := le_inf hUT (hpair.2.2.2.1.trans le_sup_left)
  have hxR : x ∈ R :=
    ⟨hxT, (le_sup_right : zpowers x ≤ I) (mem_zpowers x)⟩
  have hlt : U < R := lt_of_le_not_ge hUR (fun hRU => hxU (hRU hxR))
  have hRp : IsPGroup 2 R :=
    hT.of_injective (inclusion (show R ≤ T from inf_le_left))
      (inclusion_injective _)
  have hRbeta : R ∈ beta M := beta_mono hpair.1 hUR hRp
  have hbound : twoPart H ≤ twoPart (normalizer (A : Set G)) := by
    calc
      twoPart H = Nat.card (S : Subgroup H) := S.card_eq_multiplicity.symm
      _ ≤ 2 * Nat.card U := hsize
      _ ≤ Nat.card R := two_mul_card_le_of_lt hlt
      _ ≤ twoPart (normalizer (A : Set G)) :=
        beta_card_le_twoPart hRbeta (inf_le_right.trans hIN)
  have hcore : twoCore (normalizer (A : Set G)) ≠ ⊥ := by
    intro he
    have hle : A ≤ twoCore (normalizer (A : Set G)) :=
      le_pCoreIn_of_normalizes hA A.le_normalizer le_rfl
    exact hAne (bot_unique (he ▸ hle))
  exact gammaStar_of_largest_localPair_of_twoPart_le hH hcore
    ⟨hpair, hLN⟩ hmax hbound

/-- The final restriction from `C₄`, `C₈`, or `Q₈` to `C₄`, once the source
has constructed the embedding in `C₂ × D₈`. This does not assert the
rank-one classification or the existence of that embedding. -/
public theorem cyclicFour_of_shadow_alternatives_of_embedding
    {C : Type*} [Group C]
    (hc : Nonempty (C ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (C ≃* Multiplicative (ZMod 8)) ∨ Nonempty (C ≃* QuaternionGroup 2))
    (f : C →* Multiplicative (ZMod 2) × DihedralGroup 4)
    (hf : Function.Injective f) : Nonempty (C ≃* Multiplicative (ZMod 4)) := by
  rcases hc with hfour | height
  · exact hfour
  rcases height with height | hquaternion
  · obtain ⟨eight⟩ := height
    exact False.elim (DihedralEightProduct.not_injective_cyclicEight
      (f.comp eight.symm.toMonoidHom) (hf.comp eight.symm.injective))
  · obtain ⟨quaternion⟩ := hquaternion
    exact False.elim (DihedralEightProduct.not_injective_quaternionEight
      (f.comp quaternion.symm.toMonoidHom) (hf.comp quaternion.symm.injective))

/-- Once Lemma 2.5.27 is supplied, obtain the normal cyclic four required
at the start of the final construction. Apply this in the group `P = S`
with `C = S_C.subgroupOf S`, retaining relative normality. -/
public theorem exists_normal_cyclicFour_of_shadow_alternatives
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (C : Subgroup P) [C.Normal]
    (hc : Nonempty (C ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (C ≃* Multiplicative (ZMod 8)) ∨ Nonempty (C ≃* QuaternionGroup 2)) :
    ∃ V : Subgroup P, V.Normal ∧ V ≤ C ∧
      Nonempty (V ≃* Multiplicative (ZMod 4)) := by
  have hdata : 4 ≤ Nat.card C ∧
      ∀ x y : C, orderOf x = 2 → orderOf y = 2 → x = y := by
    rcases hc with hc | hc
    · obtain ⟨e⟩ := hc
      let : IsCyclic C := isCyclic_of_injective e.toMonoidHom e.injective
      refine ⟨?_, fun _ _ hx hy => IsCyclic.eq_of_orderOf_eq_two hx hy⟩
      rw [Nat.card_congr e.toEquiv]
      norm_num
    rcases hc with hc | hc
    · obtain ⟨e⟩ := hc
      let : IsCyclic C := isCyclic_of_injective e.toMonoidHom e.injective
      refine ⟨?_, fun _ _ hx hy => IsCyclic.eq_of_orderOf_eq_two hx hy⟩
      rw [Nat.card_congr e.toEquiv]
      norm_num
    · obtain ⟨e⟩ := hc
      refine ⟨?_, ?_⟩
      · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
        norm_num
      · intro x y hx hy
        apply e.injective
        exact QuaternionGroup.eq_of_orderOf_eq_two _ _
          ((e.orderOf_eq x).trans hx) ((e.orderOf_eq y).trans hy)
  exact hP.exists_normal_cyclicFour_of_unique_involutions C hdata.1 hdata.2

end CFSG.Quasithin.Chapter2
