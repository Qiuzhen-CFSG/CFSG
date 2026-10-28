module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Projection
public import Theory.SpecificGroups.PSL3Three.ProperSubgroups
public import Theory.SpecificGroups.PSL3Three.SylowInvolutions
public import Theory.GroupTheory.SolvableSylowInvolutions
public import Theory.GroupTheory.SelfCentralizingCoreSubnormal
public import Theory.Mathieu.M11.Properties.InvolutionCentralizer
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer

/-!
# Actual small-model intersections from the original marked source

The original 1.1.5 hypotheses construct a nontrivial inner involution on each
PSL3(3) or M11 component. Its fixed group lies in M. In M11 that centralizer
is maximal. For PSL3(3), the proper intersection is solvable and its odd
prime cores vanish by subnormality in the characteristic-two intersection.
The semidihedral Sylow involution argument forces it to centralize the
projected involution. Thus the actual intersection is GL2(3) in both cases.

This extracts the small-model argument without the unused block-generation
input of the wider component-refinement setup. Source: Aschbacher--Smith
2.3.9(7)(d) and 2.5.2(3), printed pp.525--526 and p.551.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Chapter1.QuasisimpleInvolutions ComponentRefinement

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb : e a ∈ center B := ((centerCongr e) ⟨a, ha⟩).property
  have hb1 : e a = 1 := by simpa only [h, mem_bot] using hb
  exact mem_bot.mpr (e.injective (hb1.trans (map_one e).symm))

private theorem centralizer_map_eq {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (t : A) :
    (centralizer ({t} : Set A)).map e.toMonoidHom = centralizer ({e t} : Set B) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (by simpa using congrArg e (mem_centralizer_singleton_iff.mp hx))
  · intro hy
    refine ⟨e.symm y, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply y⟩
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

private theorem small_marked_center_inner {A : Type*} [Group A] [Finite A]
    [IsQuasisimple A] {α : MulAut A} {P : Sylow 2 A} (d : MarkedInvolution α P)
    (hm : Nonempty (A ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (A ≃* Sporadic.Mathieu.M11)) :
    center A = ⊥ ∧ α ∈ (MulAut.conj (G := A)).range := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hc := center_bot_transport (e.trans Matrix.PSL3Three.equiv.symm)
      Matrix.PSL3Three.center_eq_bot
    let q : A ⧸ center A ≃* A :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact ⟨hc, (d.linear_three_three_inner_and_center
      ⟨ZMod 3, inferInstance, inferInstance, by norm_num, ⟨q.trans e⟩⟩).1⟩
  · obtain ⟨e⟩ := hm
    obtain ⟨t, ht⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 e α
    exact ⟨center_bot_transport e Sporadic.Mathieu.m11_center_eq_bot, t, ht.symm⟩

variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

/-- The actual small-model intersection is the fixed group of the original
marked involution. No block-generation or full component-refinement input. -/
theorem small_intersection_fixed_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) :
    ∃ (α : MulAut D) (P : Sylow 2 D),
      (∀ x : D, ((α x : H) : G) = z * (x : G) * z⁻¹) ∧
      MarkedInvolution α P ∧ ((M.subgroupOf H).subgroupOf D) = α.fixedSubgroup := by
  let : IsQuasisimple D := hD.2
  obtain ⟨hout, α, P, ha, d, _hc⟩ := h.component_inputs D hD
  obtain ⟨hcenter, hi⟩ := small_marked_center_inner d hm
  have ha2 : α ^ 2 = 1 := d.order_two ▸ pow_orderOf_eq_one α
  have hane : α ≠ 1 := by intro he; have hh := d.order_two; simp [he] at hh
  obtain ⟨t, ht, _⟩ := exists_unique_inner_involution hcenter α ha2 hane hi
  let I := (M.subgroupOf H).subgroupOf D
  have hproper : I ≠ ⊤ := by
    intro he
    apply hout
    rintro x ⟨a, ha, rfl⟩
    have hh : (⟨a, ha⟩ : D) ∈ I := he ▸ mem_top _
    exact hh
  have hfix : α.fixedSubgroup ≤ I := by
    intro x hx
    apply h.centralizer_le
    have he := ha x
    have hh : α x = x := (MulAut.mem_fixedSubgroup α x).mp hx
    rw [hh] at he
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hPI : (P : Subgroup D) ≤ I := fun x hx => hfix ((MulAut.mem_fixedSubgroup α x).mpr (d.fixes x hx))
  have hfixed : α.fixedSubgroup = centralizer ({t} : Set D) := by
    rw [← ht.1, MulAut.fixedSubgroup_conj]
  have hCtI : centralizer ({t} : Set D) ≤ I := hfixed ▸ hfix
  have hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → pCore p I = ⊥ := by
    intro p hp hp2
    let : Fact p.Prime := ⟨hp⟩
    let J := D.subgroupOf (M.subgroupOf H)
    have hJ : J.IsSubnormal := hD.1.comap (M.subgroupOf H).subtype
    have hb := subnormal_pCore_eq_bot_of_other_selfCentralizingCore 2 p hp2
      h.intersection_characteristicTwo J hJ
    let eIJ : I ≃* J := {
      toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
    have hh := pCore_map_iso p eIJ
    rw [hb] at hh
    exact (map_eq_bot_iff_of_injective _ eIJ.injective).mp hh
  have hICt : I ≤ centralizer ({t} : Set D) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      have hproperImage : I.map e.toMonoidHom ≠ ⊤ := by
        intro he
        apply hproper
        apply e.mapSubgroup.injective
        simpa using he
      let : Group.IsSolvable (I.map e.toMonoidHom) :=
        Matrix.PSL3Three.isSolvable_of_ne_top _ hproperImage
      let eI : I ≃* (I.map e.toMonoidHom) := e.subgroupMap I
      let : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective
        (f := eI.toMonoidHom) eI.injective
      have htC : t ∈ centralizer (P : Set D) := by
        intro x hx
        have hf := d.fixes x hx
        rw [← ht.1] at hf
        change t * x * t⁻¹ = x at hf
        exact (mul_inv_eq_iff_eq_mul.mp hf).symm
      have htp : t ∈ (P : Subgroup D) := by
        have hp : IsPGroup 2 (zpowers t) :=
          (IsPGroup.iff_card).mpr ⟨1, by simpa using ht.2⟩
        have hh : t ∈ zpowers t ⊓ normalizer (P : Set D) :=
          ⟨mem_zpowers t, Subgroup.centralizer_le_normalizer _ htC⟩
        rw [hp.inf_normalizer_sylow P] at hh
        exact hh.2
      let PI := P.subtype hPI
      let q : PI ≃* P := subgroupOfEquivOfLe hPI
      have hunique : ∀ x y : PI, orderOf x = 2 → orderOf y = 2 →
          (∀ s : PI, Commute x (s * x * s⁻¹)) →
          (∀ s : PI, Commute y (s * y * s⁻¹)) → x = y := by
        intro x y hx hy hxc hyc
        apply q.injective
        apply Matrix.PSL3Three.sylow_involution_eq_of_commuting_conjugates e P
        · simpa using hx
        · simpa using hy
        · intro s; simpa using (hxc (q.symm s)).map q.toMonoidHom
        · intro s; simpa using (hyc (q.symm s)).map q.toMonoidHom
      let ti : I := ⟨t, hPI htp⟩
      let tp : PI := ⟨ti, htp⟩
      have htp2 : orderOf tp = 2 :=
        (Subgroup.orderOf_coe tp).symm.trans ((Subgroup.orderOf_coe ti).symm.trans ht.2)
      have htpc : tp ∈ center PI := by
        apply mem_center_iff.mpr
        intro s
        apply Subtype.ext
        apply Subtype.ext
        exact htC _ s.property
      have hcentral := central_of_sylow_involution_uniqueness PI hunique hodd tp htp2 htpc
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg (fun y : I => (y : D)) (mem_center_iff.mp hcentral ⟨x, hx⟩))
    · obtain ⟨e⟩ := hm
      obtain ⟨g, hg⟩ := isConj_iff.mp
        (Sporadic.Mathieu.m11_involution_isConj_generatorA (e t)
          ((e.orderOf_eq t).trans ht.2))
      let f := e.trans (MulAut.conj g)
      have hf : f t = Sporadic.Mathieu.m11GeneratorAInM11 := hg
      have hmax : IsCoatom (centralizer ({t} : Set D)) := by
        apply (OrderIso.isCoatom_iff f.mapSubgroup (centralizer ({t} : Set D))).mp
        change IsCoatom ((centralizer ({t} : Set D)).map f.toMonoidHom)
        rw [centralizer_map_eq, hf]
        exact Sporadic.Mathieu.m11_involutionCentralizer_isCoatom
      exact ((hmax.le_iff_eq hproper).mp hCtI).le
  exact ⟨α, P, ha, d, (le_antisymm hICt hCtI).trans hfixed.symm⟩

/-- The genuine marked source constructs the exact GL2(3) intersection carrier. -/
theorem small_intersection_equiv_gl2_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) :
    Nonempty (((M.subgroupOf H).subgroupOf D) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  let : IsQuasisimple D := hD.2
  obtain ⟨α, P, _ha, d, he⟩ := small_intersection_fixed_of_source_marking h D hD hm
  obtain ⟨_hz, hi⟩ := small_marked_center_inner d hm
  let q := MulEquiv.subgroupCongr he
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    let α' := MulAut.congr e α
    have hα' : orderOf α' = 2 := ((MulAut.congr e).orderOf_eq α).trans d.order_two
    obtain ⟨t, ht⟩ := hi
    have hi' : ∃ g, α' = MulAut.conj g :=
      (MulAut.congr_inner_iff e α).mpr ⟨t, ht.symm⟩
    exact ⟨q.trans ((MulAut.fixedSubgroupCongr e α).trans
      (Matrix.PSL3Three.innerInvolutoryAutFixedEquiv α' hα' hi'))⟩
  · obtain ⟨e⟩ := hm
    exact ⟨q.trans (Sporadic.Mathieu.involutoryAutFixedEquivOfM11 e α d.order_two)⟩

/-- The literal projection and centralizer equality of source 2.5.2(3). -/
theorem small_intersection_projection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) :
    ∃ t : D, orderOf t = 2 ∧
      (∀ x : D, z * (x : G) * z⁻¹ = (((t * x * t⁻¹ : D) : H) : G)) ∧
      ((M.subgroupOf H).subgroupOf D) = centralizer ({t} : Set D) := by
  let : IsQuasisimple D := hD.2
  obtain ⟨α, P, ha, d, he⟩ := small_intersection_fixed_of_source_marking h D hD hm
  obtain ⟨hc, hi⟩ := small_marked_center_inner d hm
  have hn : α ≠ 1 := by intro hh; have htwo := d.order_two; simp [hh] at htwo
  obtain ⟨t, ht, _⟩ := exists_unique_inner_involution hc α
    (d.order_two ▸ pow_orderOf_eq_one α) hn hi
  refine ⟨t, ht.2, ?_, ?_⟩
  · intro x
    rw [← ha x, ← ht.1]
    rfl
  · rw [he, ← ht.1, MulAut.fixedSubgroup_conj]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
