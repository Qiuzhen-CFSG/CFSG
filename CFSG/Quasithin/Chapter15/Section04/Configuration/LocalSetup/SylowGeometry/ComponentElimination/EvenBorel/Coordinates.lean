module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Models
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Matrix coordinates for the actual ordinary component product

Distinct ordinary components commute. In characteristic two their genuine
PSL₂ models have trivial center, so multiplication identifies their product
with SL₂(F) × SL₂(F). Finite-field uniqueness puts both factors over the
same field. Sylow conjugacy then aligns the actual intersection with U
with the upper-unipotent product. These constructions do not place a Borel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.4.20, ordinary-component paragraph on printed p.1164.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open Matrix.SpecialLinearGroup
variable {G : Type*} [Group G]

/-- Both genuine PSL₂ models are identified with SL₂ over the same finite
characteristic-two field. No simple-group family tag is used. -/
theorem even_pair_factor_models {H K U : Subgroup G}
    (d : OrdinaryComponentPair H K U) {n : ℕ}
    (hm : ∀ i, ClassicalGroup.IsPSL (d.factor i) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ ∀ i, Nonempty (d.factor i ≃* SL(2,F)) := by
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm false
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  refine ⟨F,hF,hfin,inferInstance,hcard,?_⟩
  intro i
  obtain ⟨E,hE,hEfin,hEcard,⟨e⟩⟩ := hm i
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hEcard)
  let σ : E ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hEcard.trans hcard.symm)
  exact ⟨(e.trans (Theory.PSL2.sl2QuotientEquiv E).symm).trans
    (Atlas.fieldEquivSL 2 σ)⟩

private theorem ordinary_pair_commute {H K U : Subgroup G}
    (d : OrdinaryComponentPair H K U) :
    d.factor false ≤ centralizer (d.factor true : Set G) := by
  have hne : (d.factor false).subgroupOf H ≠ (d.factor true).subgroupOf H := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [map_subgroupOf_eq_of_le (d.le_overgroup false),
      map_subgroupOf_eq_of_le (d.le_overgroup true)] at hh
    exact Bool.false_ne_true (d.action.distinct hh)
  apply commutator_eq_bot_iff_le_centralizer.mp
  have he := congrArg (Subgroup.map H.subtype)
    ((d.component false).commutator_eq_bot_of_ne (d.component true) hne)
  simpa only [map_commutator, map_subgroupOf_eq_of_le (d.le_overgroup false),
    map_subgroupOf_eq_of_le (d.le_overgroup true), Subgroup.map_bot] using he

/-- Multiplication of the actual components constructs the matrix product
isomorphism. The evaluation formula preserves both component embeddings. -/
theorem even_pair_coordinates {H K U : Subgroup G}
    (d : OrdinaryComponentPair H K U) {n : ℕ}
    (hm : ∀ i, ClassicalGroup.IsPSL (d.factor i) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (c₀ : d.factor false ≃* SL(2,F)) (c₁ : d.factor true ≃* SL(2,F))
        (e : K ≃* (SL(2,F) × SL(2,F))),
        ∀ a b, (e.symm (a,b) : G) = (c₀.symm a : G) * (c₁.symm b : G) := by
  obtain ⟨F,hF,hfin,hchar,hcard,hc⟩ := even_pair_factor_models d hm
  obtain ⟨c₀⟩ := hc false
  obtain ⟨c₁⟩ := hc true
  have hcomm := ordinary_pair_commute d
  have hd : Disjoint (d.factor false) (d.factor true) := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    have hz : (⟨x,hx⟩ : d.factor false) ∈ center (d.factor false) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp (hcomm y.property) x hy).symm)
    have hz' : c₀ ⟨x,hx⟩ ∈ center SL(2,F) := (centerCongr c₀ ⟨_,hz⟩).property
    rw [Theory.PSL2.sl2_center_eq_bot F, mem_bot] at hz'
    exact congrArg Subtype.val (c₀.injective (hz'.trans c₀.map_one.symm))
  obtain ⟨m,hmul⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcomm
  let e : K ≃* (SL(2,F) × SL(2,F)) :=
    ((MulEquiv.subgroupCongr d.product.symm).trans m.symm).trans (c₀.prodCongr c₁)
  exact ⟨F,hF,hfin,hchar,hcard,c₀,c₁,e,fun a b => hmul (c₀.symm a) (c₁.symm b)⟩

/-- The permutation of the actual factors normalizes their actual product. -/
theorem ordinary_pair_normalized {H K U : Subgroup G}
    (d : OrdinaryComponentPair H K U) : U ≤ normalizer (K : Set G) := by
  intro u hu
  apply mem_normalizer_iff_map_conj_eq.mpr
  change K.map (MulAut.conj u).toMonoidHom = K
  rw [← d.product, Subgroup.map_sup, d.action.conjugation ⟨u,hu⟩ false,
    d.action.conjugation ⟨u,hu⟩ true]
  have hne := (d.action.permutation ⟨u,hu⟩).injective.ne Bool.false_ne_true
  cases h₀ : d.action.permutation ⟨u,hu⟩ false <;>
    cases h₁ : d.action.permutation ⟨u,hu⟩ true <;> simp_all [sup_comm]

/-- For H=KU the component product is relatively normal in H. -/
theorem ordinary_pair_normal_in_product {H K U : Subgroup G}
    (d : OrdinaryComponentPair H K U) (hH : K ⊔ U = H) :
    (K.subgroupOf H).Normal := by
  have hKH : K ≤ H := hH ▸ le_sup_left
  apply (normal_subgroupOf_iff_le_normalizer hKH).mpr
  rw [← hH]
  exact sup_le K.le_normalizer (ordinary_pair_normalized d)

private theorem product_isPGroup {A B : Type*} [Group A] [Group B]
    {p : ℕ} (P : Subgroup A) (Q : Subgroup B)
    (hP : IsPGroup p P) (hQ : IsPGroup p Q) : IsPGroup p (P.prod Q) := by
  intro x
  obtain ⟨a,ha⟩ := hP ⟨x.val.1,x.property.1⟩
  obtain ⟨b,hb⟩ := hQ ⟨x.val.2,x.property.2⟩
  refine ⟨a + b, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change x.val.1 ^ p ^ (a + b) = 1
    have h := congrArg Subtype.val ha
    change x.val.1 ^ p ^ a = 1 at h
    rw [pow_add, pow_mul, h, one_pow]
  · change x.val.2 ^ p ^ (a + b) = 1
    have h := congrArg Subtype.val hb
    change x.val.2 ^ p ^ b = 1 at h
    rw [Nat.add_comm a b, pow_add, pow_mul, h, one_pow]

/-- The literal product of upper-unipotent groups is a Sylow subgroup. -/
noncomputable def evenRootProductSylow (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Sylow 2 (SL(2,F) × SL(2,F)) :=
  { (upperUnipotent F).prod (upperUnipotent F) with
    isPGroup' := by
      exact product_isPGroup _ _
        (upperUnipotentSylow F 2).isPGroup' (upperUnipotentSylow F 2).isPGroup'
    is_maximal' := by
      intro W hW hRW
      have h₀ : W.map (MonoidHom.fst _ _) = upperUnipotent F := by
        apply (upperUnipotentSylow F 2).is_maximal' (hW.map _)
        intro x hx
        exact ⟨(x,1), hRW ⟨hx, one_mem _⟩, rfl⟩
      have h₁ : W.map (MonoidHom.snd _ _) = upperUnipotent F := by
        apply (upperUnipotentSylow F 2).is_maximal' (hW.map _)
        intro x hx
        exact ⟨(1,x), hRW ⟨one_mem _, hx⟩, rfl⟩
      apply le_antisymm ?_ hRW
      intro x hx
      exact ⟨h₀ ▸ mem_map_of_mem (MonoidHom.fst _ _) hx,
        h₁ ▸ mem_map_of_mem (MonoidHom.snd _ _) hx⟩ }

@[simp] theorem coe_evenRootProductSylow (F : Type*) [Field F] [Finite F] [CharP F 2] :
    (evenRootProductSylow F : Subgroup (SL(2,F) × SL(2,F))) =
      (upperUnipotent F).prod (upperUnipotent F) := rfl

private theorem relative_normal_sylow [Finite G] {H K U : Subgroup G}
    (hKH : K ≤ H) [hK : (K.subgroupOf H).Normal]
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K).map K.subtype = U ⊓ K := by
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal (K.subgroupOf H)
  let e := subgroupOfEquivOfLe hKH
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q',?_⟩
  have hmaps : (Q' : Subgroup K).map K.subtype =
      ((Q : Subgroup (K.subgroupOf H)).map (K.subgroupOf H).subtype).map H.subtype := by
    change ((Q : Subgroup (K.subgroupOf H)).map e.toMonoidHom).map K.subtype = _
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hmaps,hQ,map_inf _ _ _ H.subtype_injective,hP,map_subgroupOf_eq_of_le hKH]

/-- Align the actual Sylow intersection with the literal matrix root product.
The root image is exactly U ∩ K, rather than an arbitrary two-subgroup. -/
theorem even_pair_sylow_coordinates [Finite G] {H K U : Subgroup G}
    (d : OrdinaryComponentPair H K U) (hH : K ⊔ U = H)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    {n : ℕ} (hm : ∀ i, ClassicalGroup.IsPSL (d.factor i) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ e : K ≃* (SL(2,F) × SL(2,F)),
        ((upperUnipotent F).prod (upperUnipotent F)).map
          (K.subtype.comp e.symm.toMonoidHom) = U ⊓ K := by
  obtain ⟨F,hF,hfin,hchar,hcard,c₀,c₁,e₀,he₀⟩ := even_pair_coordinates d hm
  let : (K.subgroupOf H).Normal := ordinary_pair_normal_in_product d hH
  obtain ⟨Q,hQ⟩ := relative_normal_sylow (hH ▸ le_sup_left) P hP
  let Q₀ := Q.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,F) × SL(2,F)) Q₀ (evenRootProductSylow F)
  let e := e₀.trans (MulAut.conj g)
  have he : (Q : Subgroup K).map e.toMonoidHom =
      (upperUnipotent F).prod (upperUnipotent F) := by
    have hh := congrArg (fun S : Sylow 2 (SL(2,F) × SL(2,F)) =>
      (S : Subgroup (SL(2,F) × SL(2,F)))) hg
    change ((Q : Subgroup K).map e₀.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    rw [Subgroup.map_map] at hh
    exact hh
  have hb : ((upperUnipotent F).prod (upperUnipotent F)).map e.symm.toMonoidHom = Q := by
    rw [← he, Subgroup.map_map]
    simp
  refine ⟨F,hF,hfin,hchar,hcard,e,?_⟩
  rw [← Subgroup.map_map, hb, hQ]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
