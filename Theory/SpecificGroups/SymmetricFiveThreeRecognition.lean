module
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
import all Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.InvertedCubicTwoExtension
public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Recognizing S₅ × S₃ from a normal A₅ and a cubic

Let K ≃ A₅ and X ≃ C₃ be commuting normal subgroups of a finite group
with trivial two-core. If G/KX is a noncyclic two-group, then G ≃ S₅ × S₃.
The centralizer of K, modulo X, embeds in G/KX. Schur–Zassenhaus and the
three-coset action make that centralizer either X or S₃. The sign of the
five-point action rules out X. The normal S₃ splits off its centralizer;
noncyclicity then forces the complementary A₅ extension to be S₅.

The internal import of FiveExtensionAction is used only to establish the
kernel specification of its existing action. Its public boundary is unchanged.

Source: Aschbacher–Smith, 12.6.31(3), printed pp.836–837,
refs/quasithin.pdf. The original-actor application is in
Chapter12.Section06.NaturalSource.AbelianNormalProduct.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.Alternating.FiveExtensionAction
variable {H : Type*} [Group H] (K : Subgroup H) [K.Normal]

private theorem action_kernel (eK : K ≃* alternatingGroup (Fin 5)) :
    (action K eK).ker = centralizer (K : Set H) := by
  rw [action, MonoidHom.ker_comp_of_injective _ _ symmetricAutEquiv.symm.injective,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr eK).injective,
    MulAut.conjNormal_ker_eq_centralizer]

private theorem sign_action_kernel (eK : K ≃* alternatingGroup (Fin 5)) :
    (Equiv.Perm.sign.comp (action K eK)).ker = K ⊔ centralizer (K : Set H) := by
  have hmap : K.map (action K eK) = alternatingGroup (Fin 5) := by
    ext s
    constructor
    · rintro ⟨k,hk,rfl⟩
      rw [show action K eK k = eK ⟨k,hk⟩ from action_on_subgroup K eK ⟨k,hk⟩]
      exact (eK ⟨k,hk⟩).property
    · intro hs
      obtain ⟨k,hk⟩ := eK.surjective ⟨s,hs⟩
      exact ⟨k,k.property,(action_on_subgroup K eK k).trans (congrArg Subtype.val hk)⟩
  change (alternatingGroup (Fin 5)).comap (action K eK) = _
  rw [←hmap,comap_map_eq,action_kernel]
end Theory.SpecificGroups.Alternating.FiveExtensionAction

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_two_extension_dichotomy (X : Subgroup G) [X.Normal]
    (hX : Nat.card X = 3) (hquot : IsPGroup 2 (G ⧸ X))
    (hzero : pCore 2 G = ⊥) : X = ⊤ ∨ Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hcop : Nat.Coprime (Nat.card X) X.index := by
    obtain ⟨n,hn⟩ := hquot.exists_card_eq
    change Nat.Coprime (Nat.card X) (Nat.card (G ⧸ X))
    rw [hX,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨P,hP⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hi : P.index = 3 := hP.index_eq_card.trans hX
  have hp : IsPGroup 2 P := hquot.of_surjective hP.symm.QuotientMulEquiv.toMonoidHom
    hP.symm.QuotientMulEquiv.surjective
  by_cases hP0 : P = ⊥
  · exact Or.inl (by simpa only [hP0,sup_bot_eq] using hP.sup_eq_top)
  · let T : Sylow 2 G := hp.toSylow (by rw [hi]; decide)
    have hproper : pCore 2 G < (T : Subgroup G) := by
      rw [hzero]
      exact bot_lt_iff_ne_bot.mpr hP0
    obtain ⟨e⟩ := sylow_index_three_core_quotient T hi hproper
    exact Or.inr ⟨((QuotientGroup.quotientMulEquivOfEq hzero).trans QuotientGroup.quotientBot).symm.trans e⟩

omit [Finite G] in
private theorem centralizer_cubic_two_quotient (K X : Subgroup G) [K.Normal] [X.Normal]
    (hc : X ≤ centralizer (K : Set G)) (hz : center K = ⊥)
    (hq : IsPGroup 2 (G ⧸ (K ⊔ X))) :
    IsPGroup 2 (centralizer (K : Set G) ⧸ X.subgroupOf (centralizer (K : Set G))) := by
  let C := centralizer (K : Set G)
  let f : C →* G ⧸ (K ⊔ X) := (QuotientGroup.mk' (K ⊔ X)).comp C.subtype
  have hk : f.ker = X.subgroupOf C := by
    ext c
    change QuotientGroup.mk' (K ⊔ X) c.val = 1 ↔ c.val ∈ X
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    constructor
    · intro hm
      obtain ⟨k,hk,x,hx,he⟩ := mem_sup_of_normal_left.mp hm
      have hkC : k ∈ C := by
        have hh := C.mul_mem c.property (C.inv_mem (hc hx))
        rwa [←he,mul_inv_cancel_right] at hh
      have hkz : (⟨k,hk⟩ : K) ∈ center K :=
        mem_center_iff.mpr (fun y => Subtype.ext (hkC y y.property))
      have hk1 : k = 1 := congrArg (fun a : K => (a : G)) (mem_bot.mp (hz ▸ hkz))
      have hxeq : x = c.val := by simpa only [hk1,one_mul] using he
      exact hxeq ▸ hx
    · exact fun hx => (show X ≤ K ⊔ X from le_sup_right) hx
  let g := QuotientGroup.lift (X.subgroupOf C) f hk.ge
  exact hq.of_injective g ((QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm)


/-- A normal five-point component and a commuting cubic, with independent
binary quotient directions, recognize the full symmetric product. -/
public theorem symmetric_five_three_of_normal_five_cubic
    (K X : Subgroup G) [K.Normal] [X.Normal]
    (eK : K ≃* alternatingGroup (Fin 5))
    (hX : Nat.card X = 3) (hc : X ≤ centralizer (K : Set G))
    (hquot : IsPGroup 2 (G ⧸ (K ⊔ X))) (hzero : pCore 2 G = ⊥)
    (hncyc : ¬ IsCyclic (G ⧸ (K ⊔ X))) :
    Nonempty (G ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) := by
  classical
  let C := centralizer (K : Set G)
  let Y := X.subgroupOf C
  have hz : center K = ⊥ := by
    apply bot_unique
    intro k hk
    have he : eK k = 1 := mem_bot.mp ((alternatingGroup.center_eq_bot
      (by simp : 4 ≤ Nat.card (Fin 5))).le ((centerCongr eK) ⟨k,hk⟩).property)
    exact mem_bot.mpr (eK.map_eq_one_iff.mp he)
  have hCzero : pCore 2 C = ⊥ := by
    rw [pCore_eq_comap_of_normal,hzero,MonoidHom.comap_bot]
    exact C.subtype.ker_eq_bot C.subtype_injective
  have hY : Nat.card Y = 3 := (Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv).trans hX
  have hCY := centralizer_cubic_two_quotient K X hc hz hquot
  rcases cubic_two_extension_dichotomy Y hY hCY hCzero with htop | heC
  · have hCX : C = X := by
      apply le_antisymm ?_ hc
      intro c hcm
      exact htop.ge (mem_top (⟨c,hcm⟩ : C))
    let f := Equiv.Perm.sign.comp (Theory.SpecificGroups.Alternating.FiveExtensionAction.action K eK)
    have hker : f.ker = K ⊔ X := by
      rw [Theory.SpecificGroups.Alternating.FiveExtensionAction.sign_action_kernel]
      exact congrArg (K ⊔ ·) hCX
    let q := QuotientGroup.lift (K ⊔ X) f hker.ge
    exact (hncyc (isCyclic_of_injective q
      ((QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm))).elim
  · obtain ⟨eC⟩ := heC
    let N := centralizer (C : Set G)
    obtain ⟨e,he⟩ := NormalSymmetricThree.exists_product_equiv C eC
    have hKN : K ≤ N := le_centralizer_iff.mp le_rfl
    let B := K.subgroupOf N
    let eB : B ≃* alternatingGroup (Fin 5) := (subgroupOfEquivOfLe hKN).trans eK
    have hCB : centralizer (B : Set N) = ⊥ := by
      apply bot_unique
      intro n hn
      have hnC : (n : G) ∈ C := by
        intro k hk
        exact congrArg (fun a : N => (a : G)) (hn ⟨k,hKN hk⟩ hk)
      have h1 : (n : G) = 1 := Subgroup.disjoint_def.mp
        (NormalSymmetricThree.centralizer_disjoint C eC) hnC n.property
      exact mem_bot.mpr (Subtype.ext h1)
    have hnot : ¬ N ≤ K := by
      intro hNK
      let q := QuotientGroup.mk' (K ⊔ X)
      let f := q.comp C.subtype
      have hf : Function.Surjective f := by
        intro y
        obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (K ⊔ X) y
        obtain ⟨⟨c,n⟩,rfl⟩ := e.surjective g
        refine ⟨c,?_⟩
        rw [he,map_mul]
        have hnq : q n = 1 := (QuotientGroup.eq_one_iff _).mpr
          ((show K ≤ K ⊔ X from le_sup_left) (hNK n.property))
        rw [hnq,mul_one]
        rfl
      have hd : Nat.card (G ⧸ (K ⊔ X)) ∣ 6 := by
        have hh := card_dvd_of_surjective f hf
        have hcard : Nat.card C = 6 := by
          rw [Nat.card_congr eC.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
          decide
        rwa [hcard] at hh
      obtain ⟨m,hm⟩ := hquot.exists_card_eq
      have hcop : Nat.Coprime (Nat.card (G ⧸ (K ⊔ X))) 3 := by
        rw [hm]
        exact (by decide : Nat.Coprime 2 3).pow_left m
      exact hncyc (isCyclic_of_card_dvd_prime (p := 2)
        (hcop.dvd_mul_right.mp (show Nat.card (G ⧸ (K ⊔ X)) ∣ 2 * 3 from hd)))
    obtain ⟨n,hnN,hnK⟩ := SetLike.not_le_iff_exists.mp hnot
    let t : N := ⟨n,hnN⟩
    have ht : (MulAut.conjNormal t : MulAut B) ∉ MulAut.innerSubgroup B := by
      intro ht
      have hm : t ∈ (MulAut.innerSubgroup B).comap (MulAut.conjNormal : N →* MulAut B) := ht
      rw [MulAut.conjNormal_comap_innerSubgroup,hCB,sup_bot_eq] at hm
      exact hnK hm
    obtain ⟨eN,_⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.exists_equiv B eB hCB t ht
    exact ⟨e.symm.trans ((MulEquiv.prodCongr eC eN).trans MulEquiv.prodComm)⟩
end Theory.GroupTheory
