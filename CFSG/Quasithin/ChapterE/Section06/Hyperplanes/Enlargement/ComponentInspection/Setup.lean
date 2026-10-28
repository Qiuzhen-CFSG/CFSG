module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# The actual component and Sylow action in E.6.22

I.3.1(1),(2), specialized to trivial odd core, puts a centralizer component
in the orbit of an ambient component. The proved Sylow action from E.6.5
fixes each such component, so its orbit is a single component. Restriction
then retains ordinary component membership in the fixed subgroup of the
actual induced action. The hyperplane and corank-two bounds make that
action trivial or of order two.

The intrinsic centralizer inspection contracts below are outstanding model
calculations, not source theorems. They concern only involutions fixing an
actual Sylow subgroup pointwise. Source: Aschbacher--Smith, combined manuscript
(1 March 2004), printed p.254, with I.3.1 on pp.414--415.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open ComponentBalance Components Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V A U L X : Subgroup G}

/-- I.3.1(1),(2) specialized to O(H)=1: the 2-layer is the ordinary layer.
The equality retains both generated orbits; it does not assert containment
in a single component. -/
def EarlierBalance (K : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsKGroup K H →
    pPrimeCore 2 H = ⊥ → ∀ P D : Subgroup H, IsPGroup 2 P →
      CentralizerComponent P D → ∃ J : Subgroup H,
        IsComponent H J ∧ componentOrbit D (componentLayer H) = componentOrbit J P

/-- An involution action with an actual pointwise fixed Sylow subgroup. -/
def SylowCentralAction {Y : Type u} [Group Y] (P : Subgroup (MulAut Y)) : Prop :=
  ∃ S : Sylow 2 Y, ∀ a : P, ∀ x : S, (a : MulAut Y) (x : Y) = x

/-- The nonexceptional intrinsic calculation: these involution fixed groups
have no ordinary component. No persistence conclusion is a hypothesis. -/
def NoCentralInvolutionComponent (Y : Type u) [Group Y] : Prop :=
  ∀ P : Subgroup (MulAut Y), Nat.card P = 2 → SylowCentralAction P →
    ∀ D : Subgroup Y, ¬ ComponentIn (FixedPoints.subgroup P Y) D

/-- The exceptional intrinsic calculation, retaining the actual A5 model. -/
def CentralInvolutionFive (Y : Type u) [Group Y] : Prop :=
  ∀ P : Subgroup (MulAut Y), Nat.card P = 2 → SylowCentralAction P →
    ∀ D : Subgroup Y, ComponentIn (FixedPoints.subgroup P Y) D → IsAlternating D 5

private theorem centralizer_isKGroup (h : HypothesisE61 K T M V)
    (hAV : A ≤ V) (hne : A ≠ ⊥) : IsKGroup K (centralizer (A : Set G)) := by
  let _ := h.elementary
  have hn := h.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (A : Set G)) from
      ⟨A, hne, (IsElementaryAbelian.isPGroup 2 V).to_le hAV, rfl⟩)
  exact (IsKGroup.equiv (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set G)))).mp
    (hn.isKGroup.subgroup ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))))

omit [Finite G] in
private theorem centralizerComponent_subgroupOf {H : Subgroup G}
    (hUH : U ≤ H) (hCH : centralizer (U : Set G) ≤ H)
    (hL : CentralizerComponent U L) :
    CentralizerComponent (U.subgroupOf H) (L.subgroupOf H) := by
  let P := U.subgroupOf H
  let C := centralizer (P : Set H)
  let D := centralizer (U : Set G)
  let e : C ≃* D :=
    { toFun := fun x => ⟨x.val.val, by
        intro u hu
        exact congrArg Subtype.val (x.property ⟨u, hUH hu⟩ hu)⟩
      invFun := fun x => ⟨⟨x.val, hCH x.property⟩, by
        intro u hu
        exact Subtype.ext (x.property u hu)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have he : (L.subgroupOf D).map e.symm.toMonoidHom = (L.subgroupOf H).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  refine ⟨?_, he ▸ hL.2.map_equiv e.symm⟩
  intro l hl p hp
  exact Subtype.ext (hL.1 hl p hp)

/-- I.3.1 gives a containing ordinary component because the actual central
Sylow action fixes every component, rather than permuting several factors. -/
theorem exists_containing_component (h : HypothesisE61 K T M V)
    (hb : EarlierBalance K) (ho : OddCoreFree V)
    (hA : A ∈ obstructionFamily M V) (hUV : U ≤ V) (hAU : A ≤ U)
    (hL : CentralizerComponent U L) :
    ∃ X : Subgroup G, L ≤ X ∧ CentralizerComponent A X := by
  let _ := h.elementary
  let H := centralizer (A : Set G)
  have hUH : U ≤ H := hUV.trans
    (V.le_centralizer.trans (Subgroup.centralizer_le hA.1))
  have hCH : centralizer (U : Set G) ≤ H := Subgroup.centralizer_le hAU
  have hLH : L ≤ H := hL.1.trans hCH
  let P := U.subgroupOf H
  let D := L.subgroupOf H
  obtain ⟨J, hJ, hOrbit⟩ := hb H (centralizer_isKGroup h hA.1 hA.2.1)
    (ho A hA.1 hA.2.1) P D
    (((IsElementaryAbelian.isPGroup 2 V).to_le hUV).comap_subtype)
    (centralizerComponent_subgroupOf hUH hCH hL)
  let X := J.map H.subtype
  have hXJ : X.subgroupOf H = J := by
    change (J.map H.subtype).comap H.subtype = J
    exact J.comap_map_eq_self_of_injective H.subtype_injective
  have hX : CentralizerComponent A X := by
    refine ⟨map_subtype_le J, ?_⟩
    change IsComponent H (X.subgroupOf H)
    rwa [hXJ]
  have hN := component_normalized_by_V h hA hX
  have hPN : P ≤ normalizer (J : Set H) := by
    have hn : P ≤ (normalizer (X : Set G)).subgroupOf H := fun _ hp => hN (hUV hp)
    rwa [subgroupOf_normalizer_eq hX.1,
      hXJ] at hn
  have hDX : D ≤ J := (le_componentOrbit D (componentLayer H)).trans
    (hOrbit.le.trans (iSup_conjugates_le_of_le_normalizer J P J le_rfl hPN))
  refine ⟨X, ?_, hX⟩
  intro l hl
  exact ⟨⟨l, hLH hl⟩, hDX hl, rfl⟩

/-- The exact index bound behind the order-two action on the larger component. -/
theorem hyperplane_relative_index_le_two [IsElementaryAbelian 2 V]
    (hU : IsHyperplane V U) (hAU : A ≤ U) (hc : subgroupCorank V A ≤ 2) :
    A.relIndex U ≤ 2 := by
  have hpow (B : Subgroup G) : B.relIndex V = 2 ^ subgroupCorank V B := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank V B
  have ht := relIndex_mul_relIndex A U V hAU hU.1
  rw [hpow U, hU.2, hpow A] at ht
  have hp : 2 ^ subgroupCorank V A ≤ 4 :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hc).trans (by decide)
  omega

/-- The actual image of U in Aut(X), including the fixed-subgroup component
and pointwise fixed Sylow subgroup. Its order is bounded by |U:A|. -/
theorem small_action (h : HypothesisE61 K T M V)
    (hU : IsHyperplane V U) (hAU : A ≤ U) (hc : subgroupCorank V A ≤ 2)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent U L)
    (hLX : L ≤ X) (hX : CentralizerComponent A X) :
    ∃ P : Subgroup (MulAut X), Nat.card P ≤ 2 ∧ SylowCentralAction P ∧
      ComponentIn (FixedPoints.subgroup P X) (L.subgroupOf X) := by
  let _ := h.elementary
  obtain ⟨hN, S, _, hfix⟩ := component_sylow_action h hA hX rfl
  let f : U →* MulAut X := X.normalizerMonoidHom.comp (inclusion (hU.1.trans hN))
  let P := f.range
  let C := centralizer (U : Set G)
  let F := FixedPoints.subgroup P X
  let D := L.subgroupOf X
  have fixed_iff (x : X) : x ∈ F ↔ (x : G) ∈ C := by
    constructor
    · intro hx u hu
      have he := congrArg Subtype.val (hx ⟨f ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩⟩)
      change u * (x : G) * u⁻¹ = x at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hx a
      obtain ⟨u, hu⟩ := a.property
      apply Subtype.ext
      change (a.val x : G) = x
      rw [← hu]
      change (u : G) * (x : G) * (u : G)⁻¹ = x
      exact mul_inv_eq_iff_eq_mul.mpr (hx u u.property)
  have hker : A.subgroupOf U ≤ f.ker := by
    intro a ha
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr ((hX.1 x.property) a ha)
  have hcard : Nat.card P ≤ 2 := by
    rw [← index_ker]
    have hi : f.ker.index ≤ (A.subgroupOf U).index :=
      index_antitone hker
    exact hi.trans (hyperplane_relative_index_le_two hU hAU hc)
  have hcentral : SylowCentralAction P := by
    refine ⟨S, ?_⟩
    intro a x
    obtain ⟨u, hu⟩ := a.property
    rw [← hu]
    apply Subtype.ext
    exact hfix u (hU.1 u.property) x
  let e : (X.subgroupOf C) ≃* F :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩,
        (fixed_iff ⟨x.val.val, x.property⟩).mpr x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, (fixed_iff x.val).mp x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hDF : D ≤ F := fun _ hx => (fixed_iff _).mpr (hL.1 hx)
  have hDC := hL.2.subgroupOf
    (show L.subgroupOf C ≤ X.subgroupOf C from fun _ hx => hLX hx)
  have he : ((L.subgroupOf C).subgroupOf (X.subgroupOf C)).map e.toMonoidHom =
      D.subgroupOf F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  exact ⟨P, hcard, hcentral, hDF, he ▸ hDC.map_equiv e⟩

omit [Finite G] in
private theorem component_top_of_trivial_action {Y : Type u} [Group Y] [IsQuasisimple Y]
    {P : Subgroup (MulAut Y)} {D : Subgroup Y}
    (hD : ComponentIn (FixedPoints.subgroup P Y) D) (hP : P = ⊥) : D = ⊤ := by
  have hf : FixedPoints.subgroup P Y = ⊤ := by
    subst P
    apply top_unique
    intro x _ a
    have ha : (a : MulAut Y) = 1 := a.property
    change (a : MulAut Y) x = x
    rw [ha]
    rfl
  rw [hf] at hD
  have hd : IsComponent Y D := by
    have hh := hD.2.map_equiv (topEquiv : (⊤ : Subgroup Y) ≃* Y)
    have he : (D.subgroupOf ⊤).map (topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom = D := by
      exact map_subgroupOf_eq_of_le le_top
    rwa [he] at hh
  have ht : IsComponent Y (⊤ : Subgroup Y) :=
    ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  exact hd.eq_of_le ht le_top

/-- Transfer a proved nonexceptional model centralizer calculation to the
actual containing component. The inspection premise remains to be supplied. -/
theorem component_eq_of_inspection (h : HypothesisE61 K T M V)
    (hU : IsHyperplane V U) (hAU : A ≤ U) (hc : subgroupCorank V A ≤ 2)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent U L)
    (hLX : L ≤ X) (hX : CentralizerComponent A X)
    (hi : NoCentralInvolutionComponent X) : L = X := by
  let _ : IsQuasisimple X := (show IsComponentIn X (centralizer (A : Set G)) from hX).quasisimple
  obtain ⟨P, hp, hs, hD⟩ := small_action h hU hAU hc hA hL hLX hX
  by_cases hb : P = ⊥
  · exact le_antisymm hLX (subgroupOf_eq_top.mp (component_top_of_trivial_action hD hb))
  · let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hb
    have hp2 : Nat.card P = 2 := by have := Finite.one_lt_card (α := P); omega
    exact (hi P hp2 hs _ hD).elim

/-- The exceptional intrinsic inspection transports the actual A5
isomorphism, not just the central quotient of the smaller component. -/
theorem component_eq_or_five_of_inspection (h : HypothesisE61 K T M V)
    (hU : IsHyperplane V U) (hAU : A ≤ U) (hc : subgroupCorank V A ≤ 2)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent U L)
    (hLX : L ≤ X) (hX : CentralizerComponent A X)
    (hi : CentralInvolutionFive X) : L = X ∨ IsAlternating L 5 := by
  let _ : IsQuasisimple X := (show IsComponentIn X (centralizer (A : Set G)) from hX).quasisimple
  obtain ⟨P, hp, hs, hD⟩ := small_action h hU hAU hc hA hL hLX hX
  by_cases hb : P = ⊥
  · exact Or.inl (le_antisymm hLX (subgroupOf_eq_top.mp (component_top_of_trivial_action hD hb)))
  · let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hb
    have hp2 : Nat.card P = 2 := by have := Finite.one_lt_card (α := P); omega
    obtain ⟨e⟩ := hi P hp2 hs _ hD
    exact Or.inr ⟨(subgroupOfEquivOfLe hLX).symm.trans e⟩

/-- The E.6.21 odd-core input excludes central three-covers without replacing
a quotient identification by an unsupported isomorphism of the component. -/
theorem not_three_cover (ho : OddCoreFree V) (hAV : A ≤ V) (hne : A ≠ ⊥)
    (hX : CentralizerComponent A X) (n : ℕ) : ¬ IsAlternatingCover X n := by
  intro hm
  obtain ⟨_, ⟨e⟩, _⟩ := hm
  have hz : Nat.card (center X) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hi := Subgroup.IsSubnormal.pPrimeCore_eq_bot (ho A hAV hne)
    (X.subgroupOf (centralizer (A : Set G))) hX.2.1
  have hcore : pPrimeCore 2 X = ⊥ := by
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hX.1)
    simpa only [hi, Subgroup.map_bot] using he.symm
  have hb : center X = ⊥ := pPrimeCore_eq_bot_iff.mp hcore _ inferInstance (by rw [hz]; decide)
  have hh : Nat.card (center X) = 1 := by rw [hb]; simp
  omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
