module
public import Glauberman.FixedNormalPairCounting
public import Theory.GroupTheory.SubgroupTransport.Restriction
public import Theory.Frattini.CentralElementarySupplement

/-!
# Restricting a fixed-normal-free pair

Let Q=S intersect T and R be its preimage under the specified isomorphism
S≃T. The sharp maximum-abelian replacement from4.3 implies RQ=S: otherwise
J(R) lies in Q, equal maximum orders identify J(R)=J(Q), and their common
normal subgroup contradicts the fixed-normal-free condition.

The restricted isomorphism retains that condition because R and Q generate
S. At the elementary terminal branch, central elementary supplements over
R intersect Q identify the embedded Frattini subgroups of R and Q. The same
fixed-normal obstruction forces them to vanish. The construction of those
supplements from the strict maximum-order drop, and the lower-index
inheritance in the equal-order case, remain separate steps of the recursion.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition4.4,
printedpp45–46. This module proves the generation, fixed-normal inheritance,
and terminal Frattini steps with literal ambient maps.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
private theorem thompson_map_injective (f : G →* H) (hf : Function.Injective f)
    (R : Subgroup G) :
    (thompsonSubgroup R).map f = thompsonSubgroup (R.map f) := by
  rw [←thompsonSubgroup_top_map_subtype R,
    ←thompsonSubgroup_top_map_subtype (R.map f),
    ←thompsonSubgroup_top_map_mulEquiv (R.equivMapOfInjective f hf)]
  simp only [map_map]
  rfl

private theorem thompson_subgroupOf {S R : Subgroup G} (hRS : R ≤ S) :
    (thompsonSubgroup R).subgroupOf S = thompsonSubgroup (R.subgroupOf S) := by
  apply map_injective S.subtype_injective
  rw [map_subgroupOf_eq_of_le ((thompsonSubgroup_le R).trans hRS),
    thompson_map_injective S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hRS]

theorem thompson_image {S : Subgroup G} {T : Subgroup H} (φ : S ≃* T)
    (R : Subgroup G) (hRS : R ≤ S) :
    image φ (thompsonSubgroup R) = thompsonSubgroup (image φ R) := by
  rw [image,thompson_subgroupOf hRS,thompson_map_injective _ (ambientHom_injective φ)]
  rfl

omit [Finite G] [Finite H] in
theorem maximum_abelian_image {S : Subgroup G} {T : Subgroup H} (φ : S ≃* T)
    {R A : Subgroup G} (hRS : R ≤ S) (hA : A ∈ thompsonAbelianSubgroups R) :
    image φ A ∈ thompsonAbelianSubgroups (image φ R) := by
  have ha : A.subgroupOf S ∈ thompsonAbelianSubgroups (R.subgroupOf S) := by
    apply (maximum_abelian_map_iff_of_injective S.subtype S.subtype_injective).mp
    rwa [map_subgroupOf_eq_of_le (hA.1.trans hRS),map_subgroupOf_eq_of_le hRS]
  exact maximum_abelian_map_of_injective (ambientHom φ) (ambientHom_injective φ) ha

variable {S T : Subgroup G}

omit [Finite G] in
private theorem no_fixed_normal_ambient (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (R : Subgroup G) (hRS : R ≤ S) (hn : S ≤ normalizer (R : Set G))
    (hfix : image φ R = R) : R = ⊥ := by
  let _ : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  have hh := hno (R.subgroupOf S) inferInstance (by
    rw [map_subgroupOf_eq_of_le hRS,map_map]
    exact hfix)
  have hm := congrArg (Subgroup.map S.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hRS,Subgroup.map_bot] using hm

private theorem normalizes_thompson (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (thompsonSubgroup R : Set G) := by
  rw [←thompsonSubgroup_top_map_subtype R]
  let _ := allAbelianThompson_top_characteristic (G := R)
  exact normalizer_le_normalizer_characteristic_image R _

/-- The two next-row members generate S. This is the first, nonformal
step in the restriction argument of Niles4.4. -/
theorem preimage_intersection_generates (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (hQne : S ⊓ T ≠ ⊥)
    (hTn : T ≤ normalizer (S ⊓ T : Set G))
    (hfamily : thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups T)
    (hsupplement : ∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = S) :
    image φ.symm (S ⊓ T) ⊔ (S ⊓ T) = S := by
  let Q := S ⊓ T
  let R := image φ.symm Q
  have hRS : R ≤ S := image_le φ.symm Q
  have hRmap : image φ R = Q := image_symm φ.symm Q inf_le_right
  have hRn : S ≤ normalizer (R : Set G) := normalizes_image φ.symm Q inf_le_right hTn
  have hRne : R ≠ ⊥ := by
    intro he
    have hm : image φ R = ⊥ := by rw [he]; simp [image,subgroupOf]
    exact hQne (hRmap.symm.trans hm)
  have hRfamily : ∀ A, A ∈ thompsonAbelianSubgroups R → A ∈ thompsonAbelianSubgroups S := by
    intro A hA
    have ha := maximum_abelian_image φ hRS hA
    rw [hRmap] at ha
    have hat := hfamily ha
    have hback := maximum_abelian_image φ.symm le_rfl hat
    rw [image_self,image_symm φ A (hA.1.trans hRS)] at hback
    exact hback
  by_contra hnot
  have hJRQ : thompsonSubgroup R ≤ Q := by
    apply sSup_le
    intro A hA
    by_contra hAQ
    have hgen := hsupplement A (hRfamily A hA) hAQ
    apply hnot
    apply le_antisymm (sup_le hRS inf_le_left)
    calc
      S = A ⊔ Q := hgen.symm
      _ ≤ R ⊔ Q := sup_le (hA.1.trans le_sup_left) le_sup_right
  have hJle : thompsonSubgroup R ≤ thompsonSubgroup Q := by
    apply sSup_le
    intro A hA
    have hAS := hRfamily A hA
    have hAQ := (le_sSup hA).trans hJRQ
    exact le_sSup ⟨hAQ,hAS.2.1,fun B hB hBc => hAS.2.2 B (hB.trans inf_le_left) hBc⟩
  have hcard : Nat.card (thompsonSubgroup Q) = Nat.card (thompsonSubgroup R) := by
    calc
      Nat.card (thompsonSubgroup Q) = Nat.card (image φ (thompsonSubgroup R)) :=
        congrArg (fun U : Subgroup G => Nat.card U)
          ((thompson_image φ R hRS).trans (congrArg thompsonSubgroup hRmap)).symm
      _ = Nat.card (thompsonSubgroup R) :=
        Nat.card_congr (imageEquiv φ (thompsonSubgroup R)
          ((thompsonSubgroup_le R).trans hRS)).toEquiv.symm
  have hJeq : thompsonSubgroup R = thompsonSubgroup Q := eq_of_le_of_card_ge hJle hcard.le
  have hfix : image φ (thompsonSubgroup R) = thompsonSubgroup R := by
    exact (thompson_image φ R hRS).trans ((congrArg thompsonSubgroup hRmap).trans hJeq.symm)
  have hbot := no_fixed_normal_ambient φ hno (thompsonSubgroup R)
    ((thompsonSubgroup_le R).trans hRS) (hRn.trans (normalizes_thompson R)) hfix
  exact allAbelianThompson_ne_bot R hRne hbot

omit [Finite G] in
/-- The restricted isomorphism retains the exact fixed-normal-free clause
once its domain and range generate the preceding member. -/
theorem restricted_pair_no_fixed_normal (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (R : Subgroup G) (hRS : R ≤ S) (hgen : R ⊔ image φ R = S)
    (A : Subgroup R) [A.Normal]
    (hfix : (A.map (imageEquiv φ R hRS).toMonoidHom).map (image φ R).subtype =
      A.map R.subtype) : A = ⊥ := by
  let ψ := imageEquiv φ R hRS
  let N := A.map R.subtype
  change (A.map ψ.toMonoidHom).map (image φ R).subtype = N at hfix
  have hNR : N ≤ R := map_subtype_le A
  have hnR : R ≤ normalizer (N : Set G) := by
    have h := A.le_normalizer_map R.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using h
  have hnQ : image φ R ≤ normalizer (N : Set G) := by
    let _ : (A.map ψ.toMonoidHom).Normal := (inferInstance : A.Normal).map _ ψ.surjective
    have h := (A.map ψ.toMonoidHom).le_normalizer_map (image φ R).subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hfix] using h
  have hnS : S ≤ normalizer (N : Set G) := by
    calc
      S = R ⊔ image φ R := hgen.symm
      _ ≤ normalizer (N : Set G) := sup_le hnR hnQ
  have hlocal : N.subgroupOf S = A.map (inclusion hRS) := by
    apply map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le (hNR.trans hRS),map_map,subtype_comp_inclusion]
  have hNfix : image φ N = N := by
    calc
      image φ N = (A.map ψ.toMonoidHom).map (image φ R).subtype := by
        rw [image,hlocal,map_map,map_map]
        rfl
      _ = N := hfix
  have hNb := no_fixed_normal_ambient φ hno N (hNR.trans hRS) hnS hNfix
  apply map_injective R.subtype_injective
  exact hNb.trans (Subgroup.map_bot _).symm

/-- The Frattini collapse at the elementary terminal case of Niles4.4.
The two central elementary supplements are supplied by maximum-order
replacement when the next intersection has smaller maximum abelian order. -/
theorem elementary_of_restricted_central_supplements (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (R Q D U V : Subgroup G) (hRS : R ≤ S)
    (hRn : S ≤ normalizer (R : Set G)) (hmap : image φ R = Q)
    (hR : IsPGroup 2 R) (hQ : IsPGroup 2 Q)
    (hU : IsElementaryAbelian 2 U) (hV : IsElementaryAbelian 2 V)
    (hUc : U ≤ centralizer (R : Set G)) (hVc : V ≤ centralizer (Q : Set G))
    (hRgen : R = U ⊔ D) (hQgen : Q = V ⊔ D) : IsElementaryAbelian 2 Q := by
  have hRF := frattini_map_eq_of_central_elementary_supplement R D U hR hU hUc hRgen
  have hQF := frattini_map_eq_of_central_elementary_supplement Q D V hQ hV hVc hQgen
  have heq : (frattini R).map R.subtype = (frattini Q).map Q.subtype := hRF.trans hQF.symm
  have hfix : image φ ((frattini R).map R.subtype) = (frattini R).map R.subtype := by
    rw [image_frattini φ R hRS,hmap]
    exact heq.symm
  have hn : S ≤ normalizer ((frattini R).map R.subtype : Set G) :=
    hRn.trans (normalizer_le_normalizer_characteristic_image R (frattini R))
  have hb := no_fixed_normal_ambient φ hno ((frattini R).map R.subtype)
    ((map_subtype_le _).trans hRS) hn hfix
  have hQb : frattini Q = ⊥ := by
    apply map_injective Q.subtype_injective
    exact heq.symm.trans (hb.trans (Subgroup.map_bot _).symm)
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hQb

end Glauberman
