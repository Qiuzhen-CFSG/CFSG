module
public import Theory.GroupTheory.UniqueFixedCosetCounting
public import Mathlib.GroupTheory.Sylow

/-!
# Commuting-class comparison and unique fixed cosets

Compare the entire long centralizer with its model centralizer, and only the
local short centralizer with the entire model short centralizer. Literal
endpoint fusion compares the two commuting-class fibers. Double counting
commuting pairs balances these fibers without assuming the order of the
ambient short centralizer. Extremality supplies fixed cosets, and equality
of the total incidence count makes each fixed coset unique.

This is the orbit/stabilizer step of Aschbacher--Smith F.4.42, printed p.295
(`refs/quasithin.pdf`), expressed without choosing orbit representatives.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient

private theorem conjugate_order {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- Whole long-centralizer comparison and local short-centralizer comparison
balance the commuting-class incidences. Sylow extremality supplies a fixed
coset for every long involution; equality of the incidence count proves
uniqueness. No ambient short-centralizer order equality is assumed. -/
theorem unique_fixed_of_centralizer_comparison
    {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
    (z t : G) (ze te : E) (hz : orderOf z = 2)
    (X : Subgroup (centralizer ({t} : Set G)))
    (eZ : centralizer ({z} : Set G) ≃* centralizer ({ze} : Set E))
    (eX : X ≃* centralizer ({te} : Set E))
    (hZ : ∀ a : centralizer ({z} : Set G),
      IsConj t a.val ↔ IsConj te (eZ a).val)
    (hX : ∀ a : X, IsConj z a.val.val ↔ IsConj ze (eX a).val)
    (hSylow : ∃ S : Sylow 2 (centralizer ({t} : Set G)),
      (S : Subgroup (centralizer ({t} : Set G))) ≤ X) :
    ∀ a : centralizer ({t} : Set G), IsConj z a.val →
      ∃! q : centralizer ({t} : Set G) ⧸ X, a • q = q := by
  let M := centralizer ({t} : Set G)
  let p : M → Prop := fun a => IsConj z a.val
  have hcZ := Nat.card_congr eZ.toEquiv
  have hcX := Nat.card_congr eX.toEquiv
  have hfZ : Nat.card (CommutingClassIncidence.Fiber z t) =
      Nat.card (CommutingClassIncidence.Fiber ze te) :=
    Nat.card_congr (eZ.toEquiv.subtypeEquiv hZ)
  have hfX : Nat.card {a : X // p a.val} =
      Nat.card (CommutingClassIncidence.Fiber te ze) :=
    Nat.card_congr (eX.toEquiv.subtypeEquiv hX)
  have hG := CommutingClassIncidence.balance z t
  have hE := CommutingClassIncidence.balance ze te
  have hcount : Nat.card {a : M // p a} * Nat.card X =
      Nat.card M * Nat.card {a : X // p a.val} := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := centralizer ({z} : Set G)))
    change Nat.card (centralizer ({z} : Set G)) *
        (Nat.card (CommutingClassIncidence.Fiber t z) * Nat.card X) = _
    calc
      _ = (Nat.card (centralizer ({z} : Set G)) *
          Nat.card (CommutingClassIncidence.Fiber t z)) * Nat.card X := by ring
      _ = (Nat.card M * Nat.card (CommutingClassIncidence.Fiber z t)) * Nat.card X := by rw [hG]
      _ = Nat.card M * (Nat.card (centralizer ({te} : Set E)) *
          Nat.card (CommutingClassIncidence.Fiber ze te)) := by rw [hfZ,hcX]; ring
      _ = Nat.card M * (Nat.card (centralizer ({ze} : Set E)) *
          Nat.card (CommutingClassIncidence.Fiber te ze)) := by rw [hE]
      _ = _ := by rw [←hcZ,←hfX]; ring
  apply UniqueFixedCoset.unique_of_class_count X p _ _ hcount
  · intro g a
    have h : IsConj a.val ((g*a*g⁻¹ : M) : G) := isConj_iff.mpr ⟨g.val,rfl⟩
    exact ⟨fun hh => hh.trans h.symm,fun hh => hh.trans h⟩
  · intro a ha
    have ha2 : orderOf a = 2 := by
      rw [←Subgroup.orderOf_coe]
      exact (conjugate_order ha).symm.trans hz
    have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,ha2,pow_one])
    obtain ⟨R,hR⟩ := hp.exists_le_sylow
    obtain ⟨S,hSX⟩ := hSylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M R S
    have hga : g*a*g⁻¹ ∈ X := by
      apply hSX
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR (mem_zpowers a))
    refine ⟨QuotientGroup.mk g⁻¹,?_⟩
    rw [MulAction.Quotient.smul_mk,QuotientGroup.eq]
    change (a*g⁻¹)⁻¹*g⁻¹ ∈ X
    convert X.inv_mem hga using 1
    group

private def swapSubgroupOf {G : Type*} [Group G] (A B : Subgroup G) :
    A.subgroupOf B ≃* B.subgroupOf A where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem fusion_at_involution
    {G E : Type*} [Group G] [Group E] (P Q : Subgroup G)
    (f : P →* E) (g : Q →* E) (hf : Function.Injective f) (hg : Function.Injective g)
    (t : P) (ht : orderOf t.val = 2)
    (hfusion : ∀ a : Q, orderOf a.val = 2 →
      (IsConj t.val a.val ↔ IsConj (f t) (g a))) (a : Q) :
    IsConj t.val a.val ↔ IsConj (f t) (g a) := by
  constructor
  · intro h
    exact (hfusion a ((conjugate_order h).symm.trans ht)).mp h
  · intro h
    have ha : orderOf a.val = 2 := by
      rw [Subgroup.orderOf_coe,←orderOf_injective g hg]
      exact (conjugate_order h).symm.trans
        ((orderOf_injective f hf t).trans ((Subgroup.orderOf_coe t).symm.trans ht))
    exact (hfusion a ha).mpr h

/-- Literal endpoint fusion gives unique fixed cosets in the ambient short
centralizer. The long centralizer is entire; the short comparison is only
inside P. These are the two distinct hypotheses of F.4.42. -/
theorem unique_fixed_of_endpoint_fusion
    {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
    (P Q : Subgroup G) (f : P →* E) (g : Q →* E)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (t : P) (z : Q) (ht : orderOf t.val = 2) (hz : orderOf z.val = 2)
    (hCz : centralizer ({z.val} : Set G) ≤ Q)
    (hmapZ : ((centralizer ({z.val} : Set G)).subgroupOf Q).map g =
      centralizer ({g z} : Set E))
    (hmapT : ((centralizer ({t.val} : Set G)).subgroupOf P).map f =
      centralizer ({f t} : Set E))
    (hfusion : ∀ x : P, ∀ y : Q, orderOf x.val = 2 → orderOf y.val = 2 →
      (IsConj x.val y.val ↔ IsConj (f x) (g y)))
    (hSylow : ∃ S : Sylow 2 (centralizer ({t.val} : Set G)),
      (S : Subgroup (centralizer ({t.val} : Set G))) ≤
        P.subgroupOf (centralizer ({t.val} : Set G))) :
    ∀ a : centralizer ({t.val} : Set G), IsConj z.val a.val →
      ∃! q : centralizer ({t.val} : Set G) ⧸
        P.subgroupOf (centralizer ({t.val} : Set G)), a • q = q := by
  let eZ := (subgroupOfEquivOfLe hCz).symm.trans
    (((centralizer ({z.val} : Set G)).subgroupOf Q).equivMapOfInjective g hg |>.trans
      (MulEquiv.subgroupCongr hmapZ))
  let eX := (swapSubgroupOf P (centralizer ({t.val} : Set G))).trans
    (((centralizer ({t.val} : Set G)).subgroupOf P).equivMapOfInjective f hf |>.trans
      (MulEquiv.subgroupCongr hmapT))
  apply unique_fixed_of_centralizer_comparison z.val t.val (g z) (f t) hz
    (P.subgroupOf (centralizer ({t.val} : Set G))) eZ eX _ _ hSylow
  · intro a
    exact fusion_at_involution P Q f g hf hg t ht
      (fun y hy => hfusion t y ht hy) ⟨a.val,hCz a.property⟩
  · intro a
    apply fusion_at_involution Q P g f hg hf z hz
      (fun x hx => ⟨fun h => ((hfusion x z hx hz).mp h.symm).symm,
        fun h => ((hfusion x z hx hz).mpr h.symm).symm⟩) ⟨a.val.val,a.property⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient
