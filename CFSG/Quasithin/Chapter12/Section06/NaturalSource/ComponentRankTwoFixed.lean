module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoCore
public import Theory.GroupAction.ComponentRankAction
public import Theory.GroupAction.InnerFixedEmbedding

/-!
# The original cubic actors in the actual model fixed group

Rank saturation makes the centralizer of the selected simple component
prime to three, so the literal X-hat action range has cubic rank at most
two. Transport that range through the chosen component isomorphism.
When the model's cubic-actor theorem makes the original E9 inner, its
faithful action lifts into the fixed group of the same V-hat involution.
The lift retains the original Sylow, action map and conjugation equation.

The last theorem applies a model fixed-group rank bound. Its two explicit
model premises are discharged in ComponentRankTwoNonlinear; the earlier
TI and nonsingular-centralizer source hypotheses remain unchanged.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832, condition (*).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- Rank saturation bounds the literal action range, before any model transport. -/
theorem SourceHypothesis.original_rank_two_action_rank
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) : primeRank 3 a.action.range ≤ 2 := by
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hzB : center B = ⊥ := center_eq_bot_of_simple_perfect
  have hcop := Theory.GroupAction.ComponentRankAction.centralizer_coprime B
    (p := 3) (by rw [hzB,card_bot]; decide)
    (by rw [←c.three_rank_eq_star,hr]) (S.original_star_three_rank D hZ z hz hH)
  have hk : Nat.Coprime 3 (Nat.card B.normalizerMonoidHom.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (B : Set (Nonabelian.Setup.Hstar H)))).toEquiv]
    exact hcop
  have hb := (primeRank_le_of_surjective_of_coprime 3 B.normalizerMonoidHom.rangeRestrict
    B.normalizerMonoidHom.rangeRestrict_surjective hk).trans
      ((primeRank_subgroup_le 3 _).trans (S.original_star_three_rank D hZ z hz hH))
  rw [a.range_eq_star_normalizer_map]
  exact (primeRank_mono 3 (map_le_range _ _)).trans hb


include hz hTV hTz hbound hH hn a in
/-- The original Sylow E9 lifts into the model's actual fixed group whenever
rank saturation makes its cubic actors inner. The conjugation equation keeps
the original action, Sylow and model marking. -/
theorem SourceHypothesis.original_rank_two_model_fixed_embedding
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {B : Type*} [Group B] [Finite B]
    (e : Nonabelian.Setup.star H c.K ≃* B)
    (hi : ∀ A : Subgroup (MulAut B), MulAut.innerSubgroup B ≤ A →
      primeRank 3 A ≤ 2 → ∀ b ∈ A, (∃ m : ℕ, b^(3^m) = 1) →
        b ∈ MulAut.innerSubgroup B)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    ∃ α : MulAut B, orderOf α = 2 ∧
      (∃ R : Sylow 2 B, ∀ x ∈ R, α x = x) ∧
      ∃ f : P →* α.fixedSubgroup, Function.Injective f ∧
        ∀ x, MulAut.conj (f x).val = MulAut.congr e (a.residualSylowAction P x) := by
  let A := a.action.range.map (MulAut.congr e).toMonoidHom
  have hinner : MulAut.innerSubgroup B ≤ A := by
    rw [←MulAut.map_innerSubgroup_congr e,←a.component_image]
    exact map_mono (map_le_range _ _)
  have hrA : primeRank 3 A ≤ 2 := by
    exact (primeRank_equiv 3 ((MulAut.congr e).subgroupMap a.action.range)).ge.trans
      (S.original_rank_two_action_rank D hZ z hz hTV hTz hbound hH hn c a hTI hns hr)
  let U := (V.subgroupOf c.localActor).map a.action
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by
    rw [show Nat.card U = 2 from a.module_card])
  let α := MulAut.congr e (t : MulAut (Nonabelian.Setup.star H c.K))
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq _).trans
    ((Subgroup.orderOf_coe t).trans ht)
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow
    D hZ z hz hTV hTz hbound hH hn c a
  let Q := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : ∀ x ∈ Q, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e ((t : MulAut _) (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hR t t.property x hx]
  let ρ := (MulAut.congr e).toMonoidHom.comp (a.residualSylowAction P)
  have hρ : Function.Injective ρ := (MulAut.congr e).injective.comp
    (S.original_rank_two_sylow_faithful D hZ z hz hTV hTz hbound hH hn c a hTI hns hr P)
  let := (S.original_point_residual_sylow D hZ z hz hTz P).1
  have hiρ : ρ.range ≤ MulAut.innerSubgroup B := by
    rintro _ ⟨x,rfl⟩
    apply hi A hinner hrA (ρ x)
    · exact mem_map_of_mem _ ⟨_,rfl⟩
    · refine ⟨1,?_⟩
      have hx : x^3 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val x.property)
      simp only [pow_one,←map_pow,hx,map_one]
  have hcρ (x : P) : α * ρ x = ρ x * α := by
    have hAX : (D.fullSetup hZ T z).L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
    have hx : a.residualSylowAction P x ∈
        ((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action :=
      ⟨⟨x.val.val,hAX x.val.property⟩,x.val.property,rfl⟩
    exact (map_mul (MulAut.congr e) _ _).symm.trans
      ((congrArg (MulAut.congr e) (a.residual_centralizes hx t t.property)).trans
        (map_mul (MulAut.congr e) _ _))
  let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
    S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup B := e.symm.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hzB : center B = ⊥ := center_eq_bot_of_simple_perfect
  obtain ⟨f,hf,hfρ⟩ := MulAut.exists_injective_fixed_lift hzB α ρ hρ hiρ hcρ
  exact ⟨α,hα,⟨Q,hQ⟩,f,hf,hfρ⟩

include hz hTV hTz hbound hH hn a in
/-- The model fixed-group bound contradicts the same original E9, with both
model calculations supplied independently. -/
theorem SourceHypothesis.original_rank_two_fixed_rank_contradiction
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {B : Type*} [Group B] [Finite B]
    (e : Nonabelian.Setup.star H c.K ≃* B)
    (hi : ∀ A : Subgroup (MulAut B), MulAut.innerSubgroup B ≤ A →
      primeRank 3 A ≤ 2 → ∀ b ∈ A, (∃ m : ℕ, b^(3^m) = 1) →
        b ∈ MulAut.innerSubgroup B)
    (hfixed : ∀ (R : Sylow 2 B) (α : MulAut B), orderOf α = 2 →
      (∀ x ∈ R, α x = x) → primeRank 3 α.fixedSubgroup ≤ 1) : False := by
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  obtain ⟨α,hα,⟨R,hR⟩,f,hf,_⟩ := S.original_rank_two_model_fixed_embedding
    D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e hi P
  obtain ⟨hP,hcard⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  let : IsElementaryAbelian 3 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hl : 2 ≤ primeRank 3 α.fixedSubgroup :=
    IsElementaryAbelian.primeRank_ge_of_card f.range
      ((Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard)
  have hu := hfixed R α hα hR
  omega

end CFSG.Quasithin.Chapter12.Section06
