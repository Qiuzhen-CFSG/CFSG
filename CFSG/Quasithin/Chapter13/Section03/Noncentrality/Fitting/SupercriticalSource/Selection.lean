module

public import Theory.GroupAction.SupercriticalTwoPerfect
public import CFSG.Quasithin.ChapterA.Section01.Coprime
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Residual
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupAction.QuotientConjugation

/-!
# The actual supercritical selection in 13.3.14(d)

The star projection has a two-group kernel, so it identifies the image of
O₂(L₊) with the embedded two-core of its star image. Apply A.1.21 to the
actual odd prime core. Coprime detection preserves the nontrivial two-core
action on the selected characteristic subgroup; two-perfectness rules out
its cyclic model. A.1.25 then gives rank two and exactly the elementary
plane or exponent-p extraspecial quotient in the definition of Ξ.

The chosen subgroup is embedded back into H/O₂(H), is characteristic there,
and carries the original conjugation action. No actor or Ξ-membership
conclusion is assumed.

Source: Aschbacher–Smith, Lemma 13.3.14(d), printed p.892.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]

theorem rank_two_and_model
    (hp : Odd p) (hP : IsPGroup p P) (hr : primeRank p P ≤ 2)
    {A : Type*} [Group A] (hA : IsPPerfect 2 A)
    (a : A →* MulAut P) (hm : (pCore 2 A).map a ≠ ⊥)
    (X : Subgroup P) (hX : IsSupercriticalPSubgroup p X) :
    primeRank p X = 2 ∧ Chapter1.XiOddQuotient p X := by
  have hnc := hX.not_isCyclic_of_twoPerfect_movement hp hP hA a hm
  have hrl := hX.primeRank_eq_of_le_two hP hp hr
  have hrx : primeRank p X = 2 := by
    by_contra hne
    have hxle : primeRank p X ≤ 1 := by omega
    apply hnc
    exact (hP.to_subgroup X).isCyclic_of_odd_of_elementary_card_le hp
      (fun E hE => by
        let : IsElementaryAbelian p E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hxle E)
  let : Nontrivial X := Nontrivial.of_not_isCyclic hnc
  have hexp : Monoid.exponent X = p :=
    ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hX.exponent_dvd_p).resolve_left
      (Nat.ne_of_gt Monoid.one_lt_exponent)
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  refine ⟨hrx, ?_⟩
  rcases ChapterA.rankTwo_models hp2 (hP.to_subgroup X) hexp hrx hX.derived_le_center with
    ⟨hc, _⟩ | ⟨hc, he, _⟩
  · let : IsElementaryAbelian p X := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
      exponent_dvd_p := hX.exponent_dvd_p }
    exact Or.inl ⟨inferInstance, hc⟩
  · exact Or.inr ⟨he, hc, hexp⟩

variable {G : Type*} [Group G] [Finite G]

theorem star_twoCore_image (H Lplus : Subgroup G) (hLH : Lplus ≤ H) :
    (pCore 2 Lplus).map (starMap H Lplus hLH) = (star H Lplus hLH).pCoreIn 2 := by
  let f := starMap H Lplus hLH
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 H).comap (inclusion hLH) := by
      ext x
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLH)
  have hk' : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  have hh := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hk'
  have hi : (pCore 2 Lplus).map f.rangeRestrict = pCore 2 f.range := by
    rw [← hh, map_comap_eq_self_of_surjective f.rangeRestrict_surjective]
  have he := congrArg (map f.range.subtype) hi
  have hf : f.range.subtype.comp f.rangeRestrict = f := by ext; rfl
  rw [map_map, hf] at he
  exact he

omit [Fact p.Prime] in
theorem original_core_moves_of_star_core_moves
    (H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (hm : ¬ (star H Lplus hLH).pCoreIn 2 ≤ centralizer (pCore p (Star H) : Set (Star H))) :
    (pCore 2 Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut (pCore p (Star H))).comp
        (starMap H Lplus hLH)) ≠ ⊥ := by
  intro hz
  apply hm
  rw [← star_twoCore_image H Lplus hLH, ← MulAut.conjNormal_ker_eq_centralizer]
  apply (Subgroup.map_eq_bot_iff _).mp
  simpa only [map_map] using hz

theorem exists_star_supercritical
    (H Lplus : Subgroup G) (hLH : Lplus ≤ H) (hL : IsPPerfect 2 Lplus)
    (hp : Odd p) (hr : primeRank p (pCore p (Star H)) ≤ 2)
    (hm : (pCore 2 Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut (pCore p (Star H))).comp
        (starMap H Lplus hLH)) ≠ ⊥) :
    ∃ (X : Subgroup (pCore p (Star H))) (hX : IsSupercriticalPSubgroup p X),
      letI : X.Characteristic := hX.characteristic
      let D := X.map (pCore p (Star H)).subtype
      D.Characteristic ∧ D ≤ pCore p (Star H) ∧
      primeRank p D = 2 ∧ Chapter1.XiOddQuotient p D ∧
      (pCore 2 Lplus).map
        ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)) ≠ ⊥ := by
  let P := pCore p (Star H)
  let a := (MulAut.conjNormal : Star H →* MulAut P).comp (starMap H Lplus hLH)
  obtain ⟨X, hX⟩ := ChapterA.lemma_A_1_21_1 (pCore_isPGroup (p := p) (G := Star H)) hp
  let : X.Characteristic := hX.characteristic
  let D := X.map P.subtype
  let : D.Characteristic := inferInstance
  let e : X ≃* D := X.equivMapOfInjective P.subtype P.subtype_injective
  obtain ⟨hrX, hmodel⟩ := rank_two_and_model hp pCore_isPGroup hr hL a hm X hX
  refine ⟨X, hX, inferInstance, map_subtype_le X, ?_, hmodel.of_mulEquiv e, ?_⟩
  · exact (primeRank_congr p e).symm.trans hrX
  · intro hz
    apply hX.two_image_ne_bot hp pCore_isPGroup a _ pCore_isPGroup hm
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro l hl
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    have hh := (Subgroup.map_eq_bot_iff _).mp hz hl
    have he := congrArg (fun f : MulAut D => (f (e z) : Star H)) hh
    exact he

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
