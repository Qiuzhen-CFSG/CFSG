module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoFourFusion
public import Theory.GroupTheory.PGroup.ThreeInvolutionExponent

/-!
# Automorphisms of the centralizer of a fused normal four

Under elementary two-rank at most two, the centralizer of a normal four has
exactly three involutions, all central. If the four is the unique normal four
in a Sylow subgroup with one central involution, ambient fusion of the four
induces automorphisms transitive on those involutions. Indeed, conjugation to
the central Sylow involution embeds the centralizer back into the Sylow group.
Its image has index two; uniqueness of the normal four makes the embedding
preserve the four, and therefore the whole centralizer.

For a nonabelian centralizer the intrinsic three-involution theorem then
puts all its squares in the four. This is the fusion input for the minus-type
core case of Janko–Thompson, Math. Z. 113 (1970), §4, p.389, under the stronger
elementary rank bound used here.
-/

open Subgroup

namespace Sylow

/-- Every injective self-embedding into the Sylow of the index-two centralizer
of its unique normal four has image equal to that centralizer. -/
public theorem range_eq_centralizer_of_injective_of_unique_normal_four
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hi : (centralizer (E : Set S)).index = 2)
    (f : centralizer (E : Set S) →* S) (hf : Function.Injective f) :
    f.range = centralizer (E : Set S) := by
  let C := centralizer (E : Set S)
  have hEC : E ≤ C := le_centralizer E
  let F := E.subgroupOf C
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hEC
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hE
  have hfr : Nat.card f.range = Nat.card C :=
    (Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩).toEquiv).symm
  have hfi : f.range.index = 2 := by
    have h₁ := f.range.card_mul_index
    have h₂ := C.card_mul_index
    rw [hfr] at h₁
    rw [hi] at h₂
    have hp := Nat.card_pos (α := C)
    nlinarith
  let : f.range.Normal := f.range.normal_of_index_eq_two hfi
  let : IsElementaryAbelian 2 (F.map f) := IsElementaryAbelian.map f
  have hFc : f.range ≤ centralizer (F.map f : Set S) := by
    rintro _ ⟨c, rfl⟩ _ ⟨e, he, rfl⟩
    have hc : (e : S) * (c : S) = (c : S) * (e : S) := c.property e he
    simpa only [map_mul] using congrArg f (show e * c = c * e from Subtype.ext hc)
  have hFm : F.map f ≤ f.range := map_le_range f F
  have hFE : F.map f = E := hunique _
    (normal_four_of_normal_centralizing_overgroup hrank (F.map f) f.range
      (by rwa [card_map_of_injective hf]) hFm hFc)
    inferInstance (by rwa [card_map_of_injective hf])
  apply eq_of_le_of_card_ge
  · simpa only [hFE] using hFc
  · exact hfr.ge

/-- Ambient fusion of the normal four gives transitive automorphisms on the
three involutions in its centralizer. -/
public theorem centralizer_involutions_automorphism_transitive_of_four_fusion
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    ∀ x y : centralizer (E : Set S), orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (E : Set S)), a x = y := by
  let C := centralizer (E : Set S)
  have hi := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ E hE
  have hzE : z ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight
    hrank E hE (by simpa only [hz] using pow_orderOf_eq_one z)
      (center_le_centralizer _ hzc)
  have hxE (x : C) (hx : orderOf x = 2) : (x : S) ∈ E :=
    mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
      (congrArg Subtype.val (by simpa only [hx] using pow_orderOf_eq_one x)) x.property
  have hto (x : C) (hx : orderOf x = 2) :
      ∃ a : MulAut C, (a x : S) = z := by
    have hxcenter : x ∈ center C := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (c.property x (hxE x hx)).symm
    have hconj : IsConj ((x : S) : G) (z : G) :=
      hfusion ⟨x, hxE x hx⟩ ⟨z, hzE⟩
        (fun he => (orderOf_eq_prime_iff.mp hx).2 (Subtype.ext (show (x : S) = 1 from congrArg (fun e : E => (e : S)) he)))
        (fun he => (orderOf_eq_prime_iff.mp hz).2 (congrArg Subtype.val he))
    obtain ⟨f, hf, hfx⟩ :=
      S.exists_injective_hom_of_central_isConj C x hxcenter z hzc hconj
    have hr := S.range_eq_centralizer_of_injective_of_unique_normal_four
      hrank E hE hunique hi f hf
    let g : C →* C := f.codRestrict C (fun c => by change f c ∈ centralizer (E : Set S); rw [← hr]; exact ⟨c, rfl⟩)
    have hg : Function.Injective g := fun _ _ he => hf (congrArg Subtype.val he)
    exact ⟨MulEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, hfx⟩
  intro x y hx hy
  obtain ⟨a, ha⟩ := hto x hx
  obtain ⟨b, hb⟩ := hto y hy
  refine ⟨a.trans b.symm, ?_⟩
  change b.symm (a x) = y
  apply b.injective
  rw [b.apply_symm_apply]
  exact Subtype.ext (ha.trans hb.symm)

/-- In the nonabelian case, full fusion of the unique normal four forces all
squares in its centralizer to belong to the four. -/
public theorem centralizer_squares_mem_four_of_fusion
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G))
    (hnonab : ¬ IsMulCommutative (centralizer (E : Set S))) :
    ∀ x : centralizer (E : Set S), (x : S) ^ 2 ∈ E := by
  classical
  let C := centralizer (E : Set S)
  let F := E.subgroupOf C
  have hEC : E ≤ C := le_centralizer E
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hEC
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hE
  have hmem (x : C) (hx : x ^ 2 = 1) : (x : S) ∈ E :=
    mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
      (congrArg Subtype.val hx) x.property
  have hcentral (x : C) (hx : x ^ 2 = 1) : x ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property x (hmem x hx)).symm
  have hthree : Nat.card {x : C // orderOf x = 2} = 3 := by
    let e : {x : C // orderOf x = 2} ≃ {x : F // x ≠ 1} :=
      { toFun := fun x => ⟨⟨x, hmem x (by simpa only [x.property] using pow_orderOf_eq_one x.val)⟩,
          fun he => (orderOf_eq_prime_iff.mp x.property).2 (congrArg Subtype.val he)⟩
        invFun := fun x => ⟨x.val, orderOf_eq_prime
          (elemPow_eq_one_of_isElementaryAbelian _ x.val.property)
          (fun he => x.property (Subtype.ext he))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let : Fintype F := Fintype.ofFinite F
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, hF]
    simp
  have htrans := S.centralizer_involutions_automorphism_transitive_of_four_fusion
    hrank hZ E hE hunique z hz hzc hfusion
  have hexp := (S.isPGroup'.to_subgroup C).exponent_four_of_transitive_three_involutions
    hnonab hcentral hthree htrans
  intro x
  exact hmem (x ^ 2) (by simpa only [← pow_mul] using hexp x)

end Sylow
