module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.LocalData
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Full involution geometry in the cubic centralizer

Let M = C_G(⟨y⟩), where y has order three in the selected component, and
let V be the literal root four-group restricted to M. Restricting the marked
A₄ × A₅ normalizer gives |N_M(V)| = 36. The Sylow normalizer congruence then
makes V Sylow in M. The A₄ factor fuses its three nonidentity elements, and
Sylow conjugacy reaches every involution of M.

For a root involution u, the TI calculation identifies C_G(u) with the
selected E₄ × A₅ centralizer. Restricting to M gives E₄ × C₃, hence order
twelve and exponent dividing six. These constructions supply every field
of `CubicLocalGeometry`, without an ambient order or simplicity assumption.
The quotient recognition and source-theorem assembly remain downstream.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262.
The A₅ cubic-centralizer argument reuses the normalizer calculation in
`Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer`,
as in the sibling `SecondNormalizer.NormalRoot` calculation.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer.Geometry
open InvolutionGeometry

private theorem a5_cubic_card (b : A5) (hb : orderOf b = 3) :
    Nat.card (centralizer ({b} : Set A5)) = 3 := by
  have he : centralizer ({b} : Set A5) = centralizer (zpowers b : Set A5) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [he]
  let P := zpowers b
  have hP : Nat.card P = 3 := by rw [Nat.card_zpowers, hb]
  have hPC : P ≤ centralizer (P : Set A5) := P.le_centralizer
  have hCN := centralizer_le_normalizer (P : Set A5)
  have hn := alternatingGroup.FiveLocalGeometry.cubic_normalizer_card (MulEquiv.refl A5) P hP
  have hd := card_dvd_of_le hCN
  rw [hn] at hd
  have hle := Nat.le_of_dvd (by omega : 0 < 6) hd
  have hp := card_dvd_of_le hPC
  rw [hP] at hp
  have hpos : 0 < Nat.card (centralizer (P : Set A5)) := Nat.card_pos
  have hne : Nat.card (centralizer (P : Set A5)) ≠ 6 := by
    intro hc
    have he := eq_of_le_of_card_ge hCN (by omega)
    obtain ⟨a, ha, x, hx, hm⟩ :=
      alternatingGroup.FiveLocalGeometry.exists_noncommuting_normalizer (MulEquiv.refl A5) P hP
    have haC : a ∈ centralizer (P : Set A5) := he.symm ▸ ha
    exact hm (haC x hx).symm
  change Nat.card (centralizer (P : Set A5)) = 3
  omega

private def centralizerEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (a : H) : centralizer ({a} : Set H) ≃* centralizer ({e a} : Set K) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨e.symm x, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x z := Subtype.ext (e.map_mul x z)

private def pureCentralizerEquiv (A B : Type*) [Group A] [Group B] (b : B) :
    centralizer ({((1 : A), b)} : Set (A × B)) ≃* (A × centralizer ({b} : Set B)) where
  toFun x := (x.val.1, ⟨x.val.2, mem_centralizer_singleton_iff.mpr
    (congrArg Prod.snd (mem_centralizer_singleton_iff.mp x.property))⟩)
  invFun x := ⟨(x.1, x.2), mem_centralizer_singleton_iff.mpr (Prod.ext
    (by simp) (mem_centralizer_singleton_iff.mp x.2.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def coordinateCentralizerEquiv {H A B : Type*} [Group H] [Group A] [Group B]
    (e : H ≃* A × B) (y : H) (b : B) (he : e y = (1,b)) :
    centralizer ({y} : Set H) ≃* A × centralizer ({b} : Set B) :=
  (centralizerEquiv e y).trans ((MulEquiv.subgroupCongr (congrArg
    (fun a => centralizer ({a} : Set (A × B))) he)).trans (pureCentralizerEquiv A B b))

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private def restrictCentralizerEquiv (H : Subgroup G) (y : G) (hy : y ∈ H) :
    H.subgroupOf (cubicCentralizer y) ≃* centralizer ({(⟨y,hy⟩ : H)} : Set H) where
  toFun x := ⟨⟨x.val.val, x.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (x.val.property y (mem_zpowers y)).symm)⟩
  invFun x := ⟨⟨x.val.val, by
    change x.val.val ∈ centralizer (zpowers y : Set G)
    rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
private theorem pure_coordinate {A B : Type*} [Group A] [Group B]
    (H : Subgroup G) (e : H ≃* A × B) {y : G}
    (hy : y ∈ ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).map
      (H.subtype.comp e.symm.toMonoidHom)) (hyo : orderOf y = 3) :
    ∃ b : B, orderOf b = 3 ∧ (e.symm (1,b) : G) = y := by
  obtain ⟨⟨a,b⟩, hab, he⟩ := hy
  have ha : a = 1 := hab.1
  subst a
  refine ⟨b, ?_, he⟩
  let f : B →* G := H.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr A B))
  have hf : Function.Injective f := Subtype.val_injective.comp
    (e.symm.injective.comp (fun a b h => congrArg Prod.snd h))
  have ho := orderOf_injective f hf b
  change orderOf (e.symm (1,b) : G) = _ at ho
  change (e.symm (1,b) : G) = y at he
  rw [he, hyo] at ho
  exact ho.symm

private theorem normalizer_coordinate (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) :
    ∃ b : A5, orderOf b = 3 ∧ (S.normalizerEquiv.symm (1,b) : G) = y := by
  apply pure_coordinate _ S.normalizerEquiv _ hyo
  rwa [S.normalizer_component]

private theorem centralizer_coordinate (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) :
    ∃ b : A5, orderOf b = 3 ∧ (S.model.equiv.symm (1,b) : G) = y := by
  apply pure_coordinate _ S.model.equiv _ hyo
  rwa [S.component_eq] at hy

/-- The relative normalizer of the literal root four-group has order 36. -/
theorem root_normalizer_card (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) :
    Nat.card (normalizer (centralizerRoot S y : Set (cubicCentralizer y))) = 36 := by
  obtain ⟨b,hb,hby⟩ := normalizer_coordinate S hy hyo
  let N := normalizer (rootCore S.t : Set G)
  have hyN : y ∈ N := hby ▸ (S.normalizerEquiv.symm (1,b)).property
  have he : S.normalizerEquiv (⟨y,hyN⟩ : N) = (1,b) := by
    apply S.normalizerEquiv.symm.injective
    simpa only [MulEquiv.symm_apply_apply] using (Subtype.ext hby.symm :
      (⟨y,hyN⟩ : N) = S.normalizerEquiv.symm (1,b))
  rw [centralizerRoot, ← subgroupOf_normalizer_eq (rootCore_le_cubicCentralizer S hy)]
  rw [Nat.card_congr (restrictCentralizerEquiv N y hyN).toEquiv,
    Nat.card_congr (coordinateCentralizerEquiv S.normalizerEquiv ⟨y,hyN⟩ b he).toEquiv,
    Nat.card_prod, a5_cubic_card b hb, nat_card_alternatingGroup]
  norm_num

/-- The root four-group is Sylow in the full cubic centralizer. -/
theorem root_sylow (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) :
    ∃ P : Sylow 2 (cubicCentralizer y), (P : Subgroup _) = centralizerRoot S y := by
  have hV : Nat.card (centralizerRoot S y) = 2 ^ 2 := centralizerRoot_card S hy
  have hn := Sylow.card_normalizer_modEq_card hV
  rw [root_normalizer_card S hy hyo] at hn
  have hnot : ¬ 2 ∣ (centralizerRoot S y).index := by
    intro hd
    have hc := (centralizerRoot S y).card_mul_index
    rw [hV] at hc
    obtain ⟨k,hk⟩ := hd
    change 36 % 8 = Nat.card (cubicCentralizer y) % 8 at hn
    rw [← hc, hk] at hn
    omega
  exact ⟨(IsPGroup.of_card hV).toSylow hnot, rfl⟩

/-- Restrict the marked involution centralizer to the cubic centralizer. -/
theorem root_involution_centralizer (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3)
    (u : cubicCentralizer y) (hu : u ∈ centralizerRoot S y) (huo : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set (cubicCentralizer y))) = 12 ∧
      ∀ x : centralizer ({u} : Set (cubicCentralizer y)), x ^ 6 = 1 := by
  have hne : (u : G) ≠ 1 := by
    intro h
    have h1 : u = 1 := Subtype.ext h
    simp [h1] at huo
  have hCu := S.model.centralizer_eq_of_mem_rootCore S.other hu hne
  have hK : centralizer ({u} : Set (cubicCentralizer y)) =
      (involutionCentralizer S.t).subgroupOf (cubicCentralizer y) := by
    ext x
    change x ∈ centralizer ({u} : Set (cubicCentralizer y)) ↔
      (x : G) ∈ involutionCentralizer S.t
    rw [← hCu]
    simp only [involutionCentralizer, mem_centralizer_singleton_iff, Subtype.ext_iff]
    rfl
  obtain ⟨b,hb,hby⟩ := centralizer_coordinate S hy hyo
  have hyC := component_le_involutionCentralizer S hy
  have he : S.model.equiv ⟨y,hyC⟩ = (1,b) := by
    apply S.model.equiv.symm.injective
    simpa only [MulEquiv.symm_apply_apply] using (Subtype.ext hby.symm :
      (⟨y,hyC⟩ : involutionCentralizer S.t) = S.model.equiv.symm (1,b))
  let e := (MulEquiv.subgroupCongr hK).trans
    ((restrictCentralizerEquiv (involutionCentralizer S.t) y hyC).trans
      (coordinateCentralizerEquiv S.model.equiv ⟨y,hyC⟩ b he))
  constructor
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_E4, a5_cubic_card b hb]
  · intro x
    apply e.injective
    rw [map_pow, map_one]
    apply Prod.ext
    · have hs : (e x).1 ^ 2 = 1 := by
        have hs : ∀ a : E4, a ^ 2 = 1 := by decide +kernel
        exact hs _
      change (e x).1 ^ 6 = 1
      rw [show 6 = 2 * 3 from rfl, pow_mul, hs, one_pow]
    · have hs := pow_card_eq_one' (x := (e x).2)
      rw [a5_cubic_card b hb] at hs
      change (e x).2 ^ 6 = 1
      rw [show 6 = 3 * 2 from rfl, pow_mul, hs, one_pow]

private theorem a4_involutions_isConj (a b : A4) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  apply GLS3.Chapter5.SchurPresentation.alternating_involution_isConj_of_card_support_eq
    (congrArg Subtype.val ha2) (congrArg Subtype.val hb2)
  · intro h
    simp [h] at ha
  · rw [← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) a ha,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) b hb]

/-- The A₄ factor fuses the three nonidentity root elements inside M. -/
theorem root_involutions_conjugate (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3)
    (u v : cubicCentralizer y) (hu : u ∈ centralizerRoot S y)
    (hv : v ∈ centralizerRoot S y) (huo : orderOf u = 2) (hvo : orderOf v = 2) :
    IsConj u v := by
  obtain ⟨b,hb,hby⟩ := normalizer_coordinate S hy hyo
  let N := normalizer (rootCore S.t : Set G)
  let f : A4 →* G := N.subtype.comp
    (S.normalizerEquiv.symm.toMonoidHom.comp (MonoidHom.inl A4 A5))
  have hf : Function.Injective f := Subtype.val_injective.comp
    (S.normalizerEquiv.symm.injective.comp (fun a b h => congrArg Prod.fst h))
  have hfC (a : A4) : f a ∈ cubicCentralizer y := by
    change f a ∈ centralizer (zpowers y : Set G)
    rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    rw [← hby]
    have hc : (a, (1 : A5)) * (1,b) = (1,b) * (a,1) := by simp
    have hh := congrArg (fun z => (S.normalizerEquiv.symm z : G)) hc
    simpa only [map_mul, coe_mul, f, MonoidHom.comp_apply, MonoidHom.inl_apply,
      MulEquiv.coe_toMonoidHom, coe_subtype] using hh
  let fM : A4 →* cubicCentralizer y := f.codRestrict _ hfC
  have hfM : Function.Injective fM := by
    intro a c h
    apply hf
    exact congrArg (fun z : cubicCentralizer y => (z : G)) h
  have lift (x : cubicCentralizer y) (hx : x ∈ centralizerRoot S y) :
      ∃ a : A4, fM a = x := by
    change (x : G) ∈ rootCore S.t at hx
    rw [← S.normalizer_core] at hx
    obtain ⟨⟨a,c⟩, hac, he⟩ := hx
    have hc : c = 1 := hac.2
    subst c
    exact ⟨a, Subtype.ext he⟩
  obtain ⟨a,ha⟩ := lift u hu
  obtain ⟨c,hc⟩ := lift v hv
  have hao : orderOf a = 2 := (orderOf_injective fM hfM a).symm.trans (ha ▸ huo)
  have hco : orderOf c = 2 := (orderOf_injective fM hfM c).symm.trans (hc ▸ hvo)
  simpa only [ha, hc] using fM.map_isConj (a4_involutions_isConj a c hao hco)

/-- All five clauses required by the literal cubic quotient recognition. -/
theorem nonempty_cubicLocalGeometry (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) :
    Nonempty (CubicLocalGeometry S y) := by
  obtain ⟨P,hP⟩ := root_sylow S hy hyo
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := centralizerRoot S y) 2
    (by rw [centralizerRoot_card S hy]; decide)
  have huo : orderOf (u : cubicCentralizer y) = 2 := (orderOf_coe u).trans hu
  obtain ⟨hcard,hpow⟩ := root_involution_centralizer S hy hyo u u.property huo
  refine ⟨⟨⟨P,hP⟩, u, u.property, huo, hcard, hpow, ?_⟩⟩
  intro x hx
  obtain ⟨v,hv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) hx
  have hvm : (v : cubicCentralizer y) ∈ centralizerRoot S y := hP ▸ v.property
  have hvo : orderOf (v : cubicCentralizer y) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hv
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  exact hv.trans (root_involutions_conjugate S hy hyo v u hvm u.property hvo huo)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer.Geometry
