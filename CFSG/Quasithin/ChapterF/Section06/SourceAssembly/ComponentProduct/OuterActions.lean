module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.LocalModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.Source
/-!
# The two outer actions in the component-product branch

The opposite vertex identifies G/K with S₃. Faithfulness on the actual
common Sylow subgroup, of order eight, forces an element inducing an outer
automorphism on K, whose Sylow two-subgroups have order four. Its image
in S₃ then acts nontrivially on the literal normal cubic complement.
Both witnesses are conjugation by this same original element of G.

Source: Aschbacher–Smith F.6.17(2) and F.6.18(3), printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem SingleResidualComponent.quotient_symmetric_three (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hQK : (pCore 2 G₂).map G₂.subtype ≤ d.component) :
    letI : d.component.Normal := d.normal
    Nonempty ((G ⧸ d.component) ≃* Equiv.Perm (Fin 3)) := by
  let K := d.component
  let : K.Normal := d.normal
  let f := (QuotientGroup.mk' K).comp G₂.subtype
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective K z
    have hg : g ∈ K ⊔ G₂ := d.generates.symm ▸ mem_top g
    obtain ⟨k,hk,a,ha,rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨⟨a,ha⟩,?_⟩
    change QuotientGroup.mk' K a = QuotientGroup.mk' K (k*a)
    have hkq : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [map_mul,hkq,one_mul]
  have hbound := (h.right_subnormal_core_iff_not_residual_le K d.isComponent.1).mpr d.right_escapes
  have hker : f.ker = pCore 2 G₂ := by
    ext a
    change QuotientGroup.mk' K (a : G) = 1 ↔ a ∈ pCore 2 G₂
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      obtain ⟨b,hb,he⟩ := hbound ⟨a.property,ha⟩
      have he' : b=a := Subtype.ext he
      exact he' ▸ hb
    · intro ha
      exact hQK ⟨a,ha,rfl⟩
  let j := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨j.symm.trans h.quotient_right.some⟩

private theorem symmetric_three_cubic_centralizer (A : Subgroup (Equiv.Perm (Fin 3)))
    (hA : Nat.card A = 3) : centralizer (A : Set (Equiv.Perm (Fin 3))) = A := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hle : A ≤ centralizer (A : Set (Equiv.Perm (Fin 3))) := le_centralizer A
  let C := centralizer (A : Set (Equiv.Perm (Fin 3)))
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hdiv : Nat.card C ∣ 6 := hcard ▸ C.card_subgroup_dvd_card
  have hlo : 3 ≤ Nat.card C := by
    have hh := card_le_of_le hle
    rw [hA] at hh
    exact hh
  have hhi : Nat.card C ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  have hc : Nat.card C = 3 ∨ Nat.card C = 6 := by
    interval_cases hh : Nat.card C <;> norm_num [hh] at *
  rcases hc with hc | hc
  · exact (eq_of_le_of_card_ge hle (show Nat.card C ≤ Nat.card A by rw [hc,hA])).symm
  · have htop : C = ⊤ := eq_top_of_card_eq C (hc.trans hcard.symm)
    have hcent : A ≤ center (Equiv.Perm (Fin 3)) := centralizer_eq_top_iff_subset.mp htop
    have htriv : ∀ x : Equiv.Perm (Fin 3), (∀ y, y*x=x*y) → x=1 := by decide +kernel
    have hb : A = ⊥ := eq_bot_iff.mpr (fun x hx => htriv x (mem_center_iff.mp (hcent hx)))
    simp [hb] at hA


/-- Every element of the actual overlap outside the component is outer. -/
theorem SingleResidualComponent.outer_component_action_of_mem_overlap
    (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hz : center d.component = ⊥)
    (hQK : (pCore 2 G₂).map G₂.subtype ≤ d.component)
    (hgood : generalizedFitting G₂ = pCore 2 G₂)
    (hthree : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3)
    (hQcard : Nat.card ((pCore 2 G₂).map G₂.subtype) = 4)
    {t : G} (ht : t ∈ G₁ ⊓ G₂) (htK : t ∉ d.component) :
    letI : d.component.Normal := d.normal
    (MulAut.conjNormal t : MulAut d.component) ∉ MulAut.innerSubgroup d.component := by
  let K := d.component
  let T := G₁ ⊓ G₂
  let Q := (pCore 2 G₂).map G₂.subtype
  let : K.Normal := d.normal
  obtain ⟨_,hd₂⟩ := d.local_disjoint_centralizer h hcore hz hQK hgood hthree
  let a : T →* MulAut K := (MulAut.conjNormal : G →* MulAut K).comp T.subtype
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxC : (x : G) ∈ centralizer (K : Set G) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer K]
      exact hx
    exact Subtype.ext (hd₂.le_bot ⟨x.property.2,hxC⟩)
  obtain ⟨S,hS⟩ := sylow_in_normal_eq_right_core_intersection h K d.right_escapes
  rw [inf_eq_left.mpr hQK] at hS
  have hScard : Nat.card S = 4 := by
    rw [← card_map_of_injective (K := (S : Subgroup K)) K.subtype_injective,hS]
    exact hQcard
  have hTp : IsPGroup 2 T := by
    obtain ⟨R,hR⟩ := h.intersection_sylow
    change IsPGroup 2 (G₁ ⊓ G₂ : Subgroup G)
    rw [hR]
    exact R.isPGroup'
  let I := (MulAut.innerSubgroup K).comap a
  let b : I →* MulAut.innerSubgroup K := (a.comp I.subtype).codRestrict _ (fun x => x.property)
  let j : K ≃* MulAut.innerSubgroup K :=
    MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)
  let f := j.symm.toMonoidHom.comp b
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply ha
    have hh := j.symm.injective he
    exact congrArg Subtype.val hh
  have hp : IsPGroup 2 f.range :=
    (hTp.to_subgroup I).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  have hRcard : Nat.card R = 4 := (Nat.card_congr (R.equiv S).toEquiv).trans hScard
  have hbound : Nat.card f.range ≤ 4 := (card_le_of_le hR).trans hRcard.le
  have hIcard : Nat.card I ≤ 4 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact hbound
  let J := I.map T.subtype
  have hJcard : Nat.card J ≤ 4 := by
    rw [card_map_of_injective T.subtype_injective]
    exact hIcard
  have hQT : Q ≤ T := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
  have hQJ : Q ≤ J := by
    intro x hx
    refine ⟨⟨x,hQT hx⟩,?_,rfl⟩
    change (MulAut.conjNormal x : MulAut K) ∈ MulAut.innerSubgroup K
    refine ⟨⟨x,hQK hx⟩,?_⟩
    ext y
    rfl
  have he : Q = J := eq_of_le_of_card_ge hQJ (by rw [hQcard]; exact hJcard)
  intro hi
  have htJ : t ∈ J := ⟨⟨t,ht⟩,hi,rfl⟩
  have htQ : t ∈ Q := by rw [he]; exact htJ
  exact htK (hQK htQ)


theorem SingleResidualComponent.exists_outer_component_actor (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hz : center d.component = ⊥)
    (hQK : (pCore 2 G₂).map G₂.subtype ≤ d.component)
    (hgood : generalizedFitting G₂ = pCore 2 G₂)
    (hthree : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3)
    (hQcard : Nat.card ((pCore 2 G₂).map G₂.subtype) = 4)
    (hTcard : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    letI : d.component.Normal := d.normal
    ∃ t : G, t ∈ G₁ ⊓ G₂ ∧ (MulAut.conjNormal t : MulAut d.component) ∉ MulAut.innerSubgroup d.component := by
  let K := d.component
  let T := G₁ ⊓ G₂
  let Q := (pCore 2 G₂).map G₂.subtype
  let : K.Normal := d.normal
  have hbound := (h.right_subnormal_core_iff_not_residual_le K d.isComponent.1).mpr d.right_escapes
  have hnot : ¬ T ≤ K := by
    intro hTK
    have hTQ : T ≤ Q := fun _ ht => hbound ⟨ht.2,hTK ht⟩
    have hh := card_le_of_le hTQ
    change Nat.card (G₁ ⊓ G₂ : Subgroup G) ≤ Nat.card Q at hh
    rw [hTcard,hQcard] at hh
    omega
  have hex : ∃ t : G, t ∈ T ∧ t ∉ K := by
    by_contra hnone
    push Not at hnone
    exact hnot hnone
  obtain ⟨t,ht,htK⟩ := hex
  exact ⟨t,ht,d.outer_component_action_of_mem_overlap h hcore hz hQK hgood hthree hQcard ht htK⟩


omit [Finite G] in
private theorem outer_cubic_actor {K D T : Subgroup G} [K.Normal] [D.Normal]
    (q : (G ⧸ K) ≃* Equiv.Perm (Fin 3)) (hd : Disjoint K D)
    (hD : Nat.card D = 3) (hT : IsPGroup 2 T)
    {t : G} (ht : t ∈ T) (htK : t ∉ K) :
    (MulAut.conjNormal t : MulAut D) ∉ MulAut.innerSubgroup D := by
  let : IsCyclic D := isCyclic_of_prime_card hD
  let f : G →* Equiv.Perm (Fin 3) := q.toMonoidHom.comp (QuotientGroup.mk' K)
  let g := f.comp D.subtype
  have hg : Function.Injective g := by
    apply g.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxK : (x : G) ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply q.injective
      simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, map_one] using (show f x = 1 from hx)
    exact Subtype.ext (hd.le_bot ⟨hxK,x.property⟩)
  let A := g.range
  have hA : Nat.card A = 3 := (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm.trans hD
  intro hinner
  obtain ⟨d,hd⟩ := hinner
  have hin : MulAut.conj d = 1 := by
    apply MulEquiv.ext
    intro x
    change d*x*d⁻¹=x
    rw [IsMulCommutative.is_comm.comm d x]
    group
  have htC : t ∈ centralizer (D : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer D]
    exact hd.symm.trans hin
  have htf : f t ∈ centralizer (A : Set (Equiv.Perm (Fin 3))) := by
    rintro y ⟨x,rfl⟩
    change f x * f t = f t * f x
    simpa only [map_mul] using congrArg f (htC x x.property)
  have hmem : f t ∈ A := symmetric_three_cubic_centralizer A hA ▸ htf
  have hdis : Disjoint (T.map f) A := IsPGroup.disjoint_of_ne 2 3 (by decide) _ _
    (hT.map f) (IsPGroup.of_card (n := 1) (by simpa using hA))
  have hf1 : f t = 1 := hdis.le_bot ⟨⟨t,ht,rfl⟩,hmem⟩
  apply htK
  apply (QuotientGroup.eq_one_iff _).mp
  apply q.injective
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, map_one] using hf1


/-- The same actual overlap element induces outer conjugation on both factors. -/
theorem SingleResidualComponent.source_prime_outer_actions
    {H : Type*} [Group H] [Finite H] (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    let D := pResidual 2 G ⊓ centralizer (d.component : Set G)
    ∃ t : G, t ∈ G₁ ⊓ G₂ ∧ t ∉ d.component ∧
      (∃ α : MulAut d.component,
        (∀ a : d.component, (α a : G) = t * (a : G) * t⁻¹) ∧
        α ∉ MulAut.innerSubgroup d.component) ∧
      (∃ β : MulAut D, (∀ a : D, (β a : G) = t * (a : G) * t⁻¹) ∧
        β ∉ MulAut.innerSubgroup D) := by
  let K := d.component
  let D := pResidual 2 G ⊓ centralizer (K : Set G)
  let : K.Normal := d.normal
  obtain ⟨hD,hDcard,_,hdis,_⟩ := d.prime_product e h hp hm
  let : D.Normal := hD
  obtain ⟨hz,_,_⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  obtain ⟨hQK,hQcard,hTcard,hgood,_,_⟩ := d.source_prime_local_models e h hp hm hc
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e))
  obtain ⟨t,ht,ho⟩ := d.exists_outer_component_actor h hcore hz hQK hgood hc hQcard hTcard
  have htK : t ∉ K := by
    intro htK
    apply ho
    refine ⟨⟨t,htK⟩,?_⟩
    ext a
    rfl
  obtain ⟨q⟩ := d.quotient_symmetric_three h hQK
  have hT : IsPGroup 2 (G₁ ⊓ G₂ : Subgroup G) := by
    obtain ⟨R,hR⟩ := h.intersection_sylow
    rw [hR]
    exact R.isPGroup'
  have hoD := outer_cubic_actor q hdis hDcard hT ht htK
  exact ⟨t,ht,htK,⟨MulAut.conjNormal t,fun _ => rfl,ho⟩,
    ⟨MulAut.conjNormal t,fun _ => rfl,hoD⟩⟩


/-- The source's universal assertion: every overlap element outside K
induces an outer automorphism on each of the two original factors. -/
theorem SingleResidualComponent.source_prime_outer_actions_all
    {H : Type*} [Group H] [Finite H] (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    let D := pResidual 2 G ⊓ centralizer (d.component : Set G)
    ∀ t : G, t ∈ G₁ ⊓ G₂ → t ∉ d.component →
      (∃ α : MulAut d.component,
        (∀ a : d.component, (α a : G) = t * (a : G) * t⁻¹) ∧
        α ∉ MulAut.innerSubgroup d.component) ∧
      (∃ β : MulAut D, (∀ a : D, (β a : G) = t * (a : G) * t⁻¹) ∧
        β ∉ MulAut.innerSubgroup D) := by
  let K := d.component
  let D := pResidual 2 G ⊓ centralizer (K : Set G)
  let : K.Normal := d.normal
  obtain ⟨hD,hDcard,_,hdis,_⟩ := d.prime_product e h hp hm
  let : D.Normal := hD
  obtain ⟨hz,_,_⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  obtain ⟨hQK,hQcard,_,hgood,_,_⟩ := d.source_prime_local_models e h hp hm hc
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e))
  obtain ⟨q⟩ := d.quotient_symmetric_three h hQK
  have hT : IsPGroup 2 (G₁ ⊓ G₂ : Subgroup G) := by
    obtain ⟨R,hR⟩ := h.intersection_sylow
    rw [hR]
    exact R.isPGroup'
  dsimp only
  intro t ht htK
  have ho := d.outer_component_action_of_mem_overlap h hcore hz hQK hgood hc hQcard ht htK
  have hoD := outer_cubic_actor q hdis hDcard hT ht htK
  exact ⟨⟨MulAut.conjNormal t,fun _ => rfl,ho⟩,
    ⟨MulAut.conjNormal t,fun _ => rfl,hoD⟩⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
