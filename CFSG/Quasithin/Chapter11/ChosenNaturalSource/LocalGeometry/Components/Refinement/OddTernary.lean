module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.OddTernary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstTernary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondSmallSporadic
public import Theory.SpecificGroups.SU3.Quasisimplicity

/-!
# Both-normalizer refinement of the odd prime ternary rows

The actual relative embedding forces field four and containing prime five
for both signs, retaining the special linear and unitary coverings. At the
first normalizer the existing literal Sylow actor on the smaller two-core
quotient contradicts the original natural point-fixer calculation.

At the second normalizer full V₂, including C_V(L), has binary dimension
at most six. The central quotient of every signed ternary field-five
carrier has order divisible by 125. A proper action kernel in K has central
image in its quasisimple two-core quotient, forcing 125 to divide the action
image order. The orders of GL(d,2), d ≤ 6, exclude this. A kernel with full
image modulo the two-core instead has two-group quotient, so perfectness
makes the action trivial. The original natural L₂ action contradicts that
triviality. No faithful K-action or irreducibility of full V₂ is assumed.

The preceding quotient markings and natural-cover maps belong to
qt-d-1222-natural-flag-cartan; qt-d-1222-natural-local-geometry retains
their final discharge. The relative-components owner retains the other
carrier cases and the field-four triangle before full 11.1.1--11.1.3 assembly.
Source: Aschbacher--Smith 11.0.3 and 11.1.1--11.1.2, printed pp.760--765,
combined manuscript of 1 March 2004. The imported order and model results
retain their source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem no_oneTwentyFive_in_small_GL {d : ℕ} (hd : d ≤ 6) :
    ¬ 125 ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  interval_cases d <;> rw [Matrix.card_GL_field] <;>
    norm_num [Fin.prod_univ_succ]

private theorem small_action_trivial {A W : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] [IsQuasisimple (A ⧸ pCore 2 A)]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (h125 : 125 ∣ (center (A ⧸ pCore 2 A)).index)
    (ρ : Representation (ZMod 2) A W) (hd : Module.finrank (ZMod 2) W ≤ 6)
    (a : A) : ρ a = 1 := by
  let φ := ρ.asGroupHom
  let N := φ.ker
  let q := QuotientGroup.mk' (pCore 2 A)
  let : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  have hfull : N.map q = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with h | h
    · have hN : N ≤ (center (A ⧸ pCore 2 A)).comap q := map_le_iff_le_comap.mp h
      have hdiv : 125 ∣ Nat.card φ.range := by
        have hi : 125 ∣ N.index := by
          have hd := index_dvd_of_le hN
          rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at hd
          exact h125.trans hd
        simpa only [N,index_ker] using hi
      let R := φ.range
      let : Finite R := Finite.of_surjective _ φ.rangeRestrict_surjective
      let σ : Representation (ZMod 2) R W :=
        { toFun r := r.val.val
          map_one' := rfl
          map_mul' _ _ := rfl }
      have hf : Function.Injective σ := Units.val_injective.comp Subtype.val_injective
      exact (no_oneTwentyFive_in_small_GL hd
        (hdiv.trans (Representation.card_dvd_card_GL_of_injective σ hf))).elim
    · exact h
  have hs : N ⊔ pCore 2 A = ⊤ := by
    have he := congrArg (comap q) hfull
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he
  let : Group.IsNilpotent (A ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N (pCore 2 A) pCore_isPGroup hs).isNilpotent
  have hN : N = ⊤ := top_unique (by simpa only [solvableResidual_eq_top] using
    solvableResidual_le_of_solvable_quotient N)
  have ha : a ∈ N := hN ▸ mem_top a
  exact congrArg Units.val ha


private theorem projective_five_data {A : Type*} [Group A] [Finite A]
    (hm : ClassicalGroup.IsPSL A 3 5 ∨ ClassicalGroup.IsPSU A 3 5) :
    IsQuasisimple A ∧ center A = ⊥ ∧ 125 ∣ Nat.card A := by
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : IsQuasisimple PSL(3,F) := inferInstance
    refine ⟨IsQuasisimple.of_mulEquiv e.symm,?_,?_⟩
    · apply _root_.eq_bot_iff.mpr
      intro a ha
      exact e.map_eq_one_iff.mp
        ((Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)).le
          ((centerCongr e) ⟨a,ha⟩).property)
    · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
      rw [hF] at hc
      norm_num [Fin.prod_univ_succ] at hc
      have he : Nat.card PSL(3,F) = 372000 := by omega
      rw [Nat.card_congr e.toEquiv,he]
      decide
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv A e.toEquiv
    have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj 5 1 (by decide) (by simpa using hF) (by simpa using hconj)
    let : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) :=
      J.projective_isQuasisimple_of_fixed_card (by decide : 2 < 5) hF hfixed
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hF hfixed
    refine ⟨IsQuasisimple.of_mulEquiv e.symm,?_,?_⟩
    · apply _root_.eq_bot_iff.mpr
      intro a ha
      have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
        rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
          with hz | hz
        · exact hz
        · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
      exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨a,ha⟩).property)
    · rw [Nat.card_congr e.toEquiv]
      exact J.cube_dvd_card_projective hF hfixed

private theorem central_cover_data {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    [IsQuasisimple A] (q : A →* H) (hq : Function.Surjective q)
    (hk : q.ker ≤ center A) (hz : center H = ⊥) (hd : 125 ∣ Nat.card H) :
    125 ∣ (center A).index := by
  have he : q.ker = center A := by
    apply le_antisymm hk
    intro a ha
    have hc : q a ∈ center H := by
      apply mem_center_iff.mpr
      intro b
      obtain ⟨b,rfl⟩ := hq b
      simpa only [←map_mul] using congrArg q (mem_center_iff.mp ha b)
    exact hz.le hc
  rw [←he,index_ker,MonoidHom.range_eq_top.mpr hq,card_top]
  exact hd

private theorem signed_five_data {A : Type*} [Group A] [Finite A] (u : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign A u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign A u 3 5) :
    IsQuasisimple A ∧ 125 ∣ (center A).index := by
  rcases hm with hm | hm
  · have hp : ClassicalGroup.IsPSL A 3 5 ∨ ClassicalGroup.IsPSU A 3 5 := by
      cases u with
      | false => exact .inl hm
      | true => exact .inr hm
    obtain ⟨hq,hz,hd⟩ := projective_five_data hp
    exact ⟨hq,by simpa [hz] using hd⟩
  · cases u with
    | false =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
      obtain ⟨_,hz,hd⟩ := projective_five_data
        (A := PSL(3,F)) (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
      refine ⟨inferInstance,?_⟩
      let q := (PSL3.projection F).comp e.toMonoidHom
      apply central_cover_data q ((PSL3.projection_surjective F).comp e.surjective) ?_ hz hd
      intro a ha
      apply mem_center_iff.mpr
      intro b
      apply e.injective
      have hk : e a ∈ center SL(3,F) := by
        rw [← PSL3.projection_ker]
        exact ha
      simpa only [map_mul] using mem_center_iff.mp hk (e b)
    | true =>
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
        simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
          J.conj 5 1 (by decide) (by simpa using hF) (by simpa using hconj)
      let : IsQuasisimple J.specialSubgroup :=
        J.special_isQuasisimple_of_fixed_card (by decide : 2 < 5) hF hfixed
      let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
      obtain ⟨_,hz,hd⟩ := projective_five_data
        (A := ProjectiveSpecialUnitaryMatrixGroup J)
        (.inr ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨MulEquiv.refl _⟩⟩)
      refine ⟨inferInstance,?_⟩
      let q := J.specialToProjective.comp e.toMonoidHom
      apply central_cover_data q (J.specialToProjective_surjective.comp e.surjective) ?_ hz hd
      intro a ha
      apply mem_center_iff.mpr
      intro b
      apply e.injective
      simpa only [map_mul,MulEquiv.coe_toMonoidHom] using mem_center_iff.mp
        (J.specialToProjective_ker_le_center ha) (e b)


open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The first-normalizer refinement for every odd prime ternary model,
with both parameter restrictions derived from the actual embedding. -/
theorem first_refinement_of_odd_ternary
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K) {r : ℕ} (hr : r.Prime) (ho : Odd r) (u : Bool)
    (hmodel : IsPSLSign (K ⧸ pCore 2 K) u 3 r ∨ IsSLSign (K ⧸ pCore 2 K) u 3 r) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  by_cases he : f.Li 0 = K
  · exact .equal (by simpa using he)
  obtain ⟨hn,rfl⟩ := flag_odd_ternary_parameters D S f 0 hm hK hLK hr ho u hmodel
  exact (first_component_not_ternary D S f hm hn hfix hK
    (lt_of_le_of_ne hLK he) u hmodel).elim

/-- The entire original natural plane excludes both signs and both covers
of the odd ternary row, without an action-faithfulness hypothesis on K. -/
theorem second_not_odd_ternary
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (u : Bool) :
    ¬ (IsPSLSign (K ⧸ pCore 2 K) u 3 r ∨ IsSLSign (K ⧸ pCore 2 K) u 3 r) := by
  intro hmodel
  obtain ⟨hn,rfl⟩ := flag_odd_ternary_parameters D S f 1 hm hK hLK hr ho u hmodel
  obtain ⟨hq,h125⟩ := signed_five_data u hmodel
  let : IsQuasisimple (K ⧸ pCore 2 K) := hq
  let B := K.subgroupOf (normalizer (f.Vi 1 : Set G))
  let : Group.IsPerfect B := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  have hdim : Module.finrank (ZMod 2) (Additive (f.Vi 1)) ≤ 6 := by
    simpa only [hn] using second_cover_finrank_le D S f p hp hk
  let ρ := (flagAction f 1).comp (inclusion hK.1)
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier
    (![1,0]) (![0,1]) (by simp) (by simp)
  obtain ⟨a,rfl⟩ := hπ g
  obtain ⟨v,hv⟩ := hp (![1,0])
  have he : flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v = v :=
    LinearMap.congr_fun (small_action_trivial h125 ρ hdim ⟨a,hLK a.property⟩) v
  have ha := hact a v
  rw [he,hv] at ha
  have hg' : specialLinearNatural 2 (π a) (![1,0]) = (![0,1]) := hg
  rw [hg'] at ha
  have hz := congrFun ha 0
  simp at hz

/-- The second-index source refinement in all odd prime ternary carriers. -/
theorem second_refinement_of_odd_ternary
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (u : Bool)
    (hmodel : IsPSLSign (K ⧸ pCore 2 K) u 3 r ∨ IsSLSign (K ⧸ pCore 2 K) u 3 r) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 1 S.field.degree :=
  (second_not_odd_ternary D S f hm hK hLK π hπ p hp hact hk hr ho u hmodel).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
