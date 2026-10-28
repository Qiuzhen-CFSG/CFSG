module
public import Theory.GroupTheory.HomSupExtension
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
/-!
# Two local symmetric-three quotients

Extend one quotient across a normalized cubic factor and pair it with a second
quotient. A two-subgroup surviving only in the first projection forces the whole
product; the joint kernel is a two-group. This is the local product argument in
Aschbacher–Smith, *The Classification of Quasithin Groups*, II, §13.7, p. 940.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G B : Type*} [Group G] [Group B]

/-- Extend a quotient over a normalized factor killed by that quotient. -/
theorem exists_sup_extension_of_inf_le_kernel (A X : Subgroup G)
    (hn : A ≤ normalizer (X : Set G))
    (f : A →* B) (hf : Function.Surjective f) (hk : X.subgroupOf A ≤ f.ker) :
    ∃ q : (A ⊔ X : Subgroup G) →* B, Function.Surjective q ∧
      q.ker = (X ⊔ f.ker.map A.subtype).subgroupOf (A ⊔ X) ∧
      ∀ a : A, q (inclusion le_sup_left a) = f a := by
  let Y := f.ker.map A.subtype
  let N := X ⊔ Y
  have hYA : Y ≤ A := map_subtype_le _
  have hAY : A ≤ normalizer (Y : Set G) := by
    have hh := f.ker.le_normalizer_map A.subtype
    simpa only [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hAN : A ≤ normalizer (N : Set G) :=
    (le_inf hn hAY).trans (normalizer_inf_normalizer_le_normalizer_sup X Y)
  have hker : f.ker = N.subgroupOf A := by
    apply le_antisymm
    · intro a ha
      exact (show Y ≤ N from le_sup_right) (mem_map_of_mem A.subtype ha)
    · intro a ha
      have hp : a.val ∈ (Y : Set G) * (X : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right Y X (hYA.trans hn),sup_comm]
        exact ha
      obtain ⟨y,hy,x,hx,he⟩ := hp
      have hxA : x ∈ A := by
        have hh := A.mul_mem (A.inv_mem (hYA hy)) a.property
        rwa [←he,inv_mul_cancel_left] at hh
      obtain ⟨b,hb,hby⟩ := hy
      have ha' : a = b * (⟨x,hxA⟩ : A) := by
        apply Subtype.ext
        change a.val = b.val * x
        change b.val = y at hby
        rw [hby]
        exact he.symm
      rw [ha']
      exact f.ker.mul_mem hb (hk hx)
  obtain ⟨q,hq,hqk,hqa⟩ := MonoidHom.exists_sup_extension hAN f hf hker
  have hsup : A ⊔ X = A ⊔ N := by
    dsimp [N]
    rw [←sup_assoc,sup_eq_left.mpr (hYA.trans le_sup_left)]
  let e := MulEquiv.subgroupCongr hsup
  refine ⟨q.comp e.toMonoidHom,hq.comp e.surjective,?_,?_⟩
  · ext x
    change q (e x) = 1 ↔ x.val ∈ N
    exact (show e x ∈ q.ker ↔ x.val ∈ N by rw [hqk];rfl)
  · intro a
    exact hqa a

/-- A two-element surviving in only one projection forces the full product. -/
theorem symmetricThree_prod_surjective_of_independent_two_group
    (f g : G →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (P : Subgroup G) (hp : IsPGroup 2 P)
    (hPg : P ≤ g.ker) (hPf : ¬ P ≤ f.ker) :
    Function.Surjective (f.prod g) := by
  let N := g.ker.map f
  let : N.Normal := (inferInstance : g.ker.Normal).map f hf
  have hPne : P.map f ≠ ⊥ := by
    intro he
    exact hPf ((Subgroup.map_eq_bot_iff _).mp he)
  have htwo : 2 ∣ Nat.card N := by
    have hpm := hp.map f
    rcases hpm.card_eq_or_dvd with hc | hd
    · exact (hPne (card_eq_one.mp hc)).elim
    · exact hd.trans (card_dvd_of_le (map_mono hPg))
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have hd : Nat.card N ∣ 6 := hcard ▸ N.card_subgroup_dvd_card
  have hpos := Nat.card_pos (α := N)
  have hle : Nat.card N ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hn : Nat.card N = 2 ∨ Nat.card N = 6 := by
    interval_cases hc : Nat.card N <;> omega
  have htop : N = ⊤ := by
    rcases hn with h2 | h6
    · have hN : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by simpa using h2)
      have hc : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
        have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id _) Function.surjective_id
          (show IsPGroup 2 (MonoidHom.id (Equiv.Perm (Fin 3))).ker from
            IsPGroup.of_card (n := 0) (by simp))
        simpa using hh.symm
      have hlecore : N ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨inferInstance,hN⟩
      have hbot : N = ⊥ := bot_unique (hlecore.trans hc.le)
      rw [hbot,card_bot] at h2
      contradiction
    · exact N.eq_top_of_card_eq (h6.trans hcard.symm)
  intro y
  obtain ⟨x,hx⟩ := hg y.2
  have hmem : y.1 * (f x)⁻¹ ∈ N := by rw [htop];trivial
  obtain ⟨k,hkg,hkf⟩ := hmem
  refine ⟨k*x,Prod.ext ?_ ?_⟩
  · change f (k*x) = y.1
    rw [map_mul,hkf,inv_mul_cancel_right]
  · change g (k*x) = y.2
    rw [map_mul,show g k = 1 from hkg,one_mul,hx]

/-- Two actual S₃ quotients, with a cubic normal factor and an independent
local two-group, identify the quotient by the two-core of their join. -/
theorem symmetricThree_product_quotient_of_local_maps [Finite G]
    (A X : Subgroup G) (hn : A ≤ normalizer (X : Set G))
    (f : A →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hXA : X.subgroupOf A ≤ f.ker)
    (g : (A ⊔ X : Subgroup G) →* Equiv.Perm (Fin 3))
    (hg : Function.Surjective g)
    (hXg : IsPGroup 2 (X.subgroupOf (A ⊔ X) ⊓ g.ker : Subgroup (A ⊔ X : Subgroup G)))
    (hXcard : Nat.card ((X.subgroupOf (A ⊔ X)).map g) = 3)
    (P : Subgroup G) (hp : IsPGroup 2 P)
    (hPg : P.subgroupOf (A ⊔ X) ≤ g.ker)
    (hPf : ¬ P.subgroupOf A ≤ f.ker) :
    Nonempty (((A ⊔ X : Subgroup G) ⧸ pCore 2 (A ⊔ X : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let J := A ⊔ X
  let R := f.ker.map A.subtype
  have hRJ : R ≤ J := (map_subtype_le _).trans le_sup_left
  have hXJ : X ≤ J := le_sup_right
  obtain ⟨q,hq,hqk,hqa⟩ := exists_sup_extension_of_inf_le_kernel A X hn f hf hXA
  have hRP : IsPGroup 2 (R.subgroupOf J) := (hk.map A.subtype).comap_subtype
  have hRN : R.subgroupOf J ≤ normalizer (X.subgroupOf J : Set J) :=
    (comap_mono ((map_subtype_le _).trans hn)).trans (le_normalizer_comap J.subtype)
  obtain ⟨n,hncard⟩ := (hRP.map g).exists_card_eq
  have hdis : Disjoint ((X.subgroupOf J).map g) ((R.subgroupOf J).map g) :=
    disjoint_of_coprime_natCard (by
      rw [hXcard,hncard]
      exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hprodker : IsPGroup 2 (q.prod g).ker := by
    rw [MonoidHom.ker_prod,hqk,subgroupOf_sup hXJ hRJ]
    exact join_inf_ker_isPGroup_of_disjoint_images g (X.subgroupOf J)
      (R.subgroupOf J) hRN hXg hRP hdis
  have hPq : ¬ P.subgroupOf J ≤ q.ker := by
    intro hh
    apply hPf
    intro a ha
    have hx : q (inclusion (show A ≤ J from le_sup_left) a) = 1 :=
      hh (show inclusion (show A ≤ J from le_sup_left) a ∈ P.subgroupOf J from ha)
    rwa [hqa] at hx
  have hprod := symmetricThree_prod_surjective_of_independent_two_group q g hq hg
    (P.subgroupOf J) hp.comap_subtype hPg hPq
  let e := (q.prod g).pCoreQuotientEquiv hprod hprodker
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
    SymmetricThreeProduct.twoCore_eq_bot).trans QuotientGroup.quotientBot)⟩

end Subgroup
