module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitarySeparation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallProjectiveUnitary

/-!
# The small projective-unitary octagon against larger linear fields

A root-generated solvable actor of order 72 has a regular order-eight
Borel. A crossed root makes its action on each relevant section faithful;
the regular ternary plane then forces binary degree at least eight.
An element of order five or seven in the opposite linear Cartan fixes
every unitary root, since their Frattini quotients have order at most four.
The fixed radical has order 512, but its two moving Frattini layers require
order at least 65536. This excludes the linear fields of orders 16 and 64.

This supplies the small projective-unitary instances of the separating
Cartan argument in Fong--Seitz I (6F), printed p.46. The quadratic field
ratio and the special-unitary scalar cover require separate arguments.
The companion source and Chapter 12 modules use the original quotient,
full Borel, both endpoint squares and either orientation.
-/

public noncomputable section
open Subgroup MulAction
open scoped IsMulCommutative MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
open RootCoordinates UnitarySource GTwoSource HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)

private theorem nine_actor_borel
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    Q.tits.B.subgroupOf (rankOne Q split j) =
      (simpleRoot Q split j).subgroupOf (rankOne Q split j) := by
  have hp := singleton_parabolic_root_index Q split j
  change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hp
  have hB := (Q.tits.B.subgroupOf (rankOne Q split j)).index_mul_card
  rw [rankOne_borel_index Q split j,hp,hroot,hR] at hB
  have hA : Nat.card ((simpleRoot Q split j).subgroupOf (rankOne Q split j)) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).toEquiv).trans hroot
  exact (eq_of_le_of_card_ge
    (subgroupOf_mono _ ((simpleRoot_le Q split j).trans split.U_le)) (by omega)).symm

private theorem nine_actor_projection_injective
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    Function.Injective (rootImageProjection Q split j) := by
  apply (rootImageProjection Q split j).ker_eq_bot_iff.mp
  apply (eq_bot_iff_forall _).mpr
  intro r hr
  have hk : (r : X ⧸ Q.D) ∈ localKernel Q j := by
    change r ∈ ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker at hr
    rw [MonoidHom.ker_rangeRestrict,panelAction_ker] at hr
    exact hr
  have hb : r ∈ Q.tits.B.subgroupOf (rankOne Q split j) := localKernel_le_borel Q j hk
  rw [nine_actor_borel Q split j hR hroot] at hb
  apply Subtype.ext
  have he : (⟨r,hb⟩ : simpleRoot Q split j) = 1 := by
    apply simpleRoot_panelAction_injective Q split j
    rw [map_one]
    exact congrArg Subtype.val hr
  exact congrArg (fun a : simpleRoot Q split j => (a : X ⧸ Q.D)) he

private theorem nine_actor_structure
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    Group.IsSolvable (rootPanelImage Q split j) ∧
      Nat.card (rootPanelImage Q split j) = 72 ∧
      (∀ g : stabilizer (rootPanelImage Q split j) (panelBase Q j),
        ∀ x : Panel Q j, x ≠ panelBase Q j → (g : rootPanelImage Q split j) • x = x → g = 1) := by
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f := (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hi := nine_actor_projection_injective Q split j hR hroot
  refine ⟨Group.isSolvable_of_surjective hf, (Nat.card_congr (Equiv.ofBijective f ⟨hi,hf⟩)).symm.trans hR,?_⟩
  intro g x hx hfix
  obtain ⟨r,hr⟩ := hf g
  have hb : (r : X ⧸ Q.D) ∈ Q.tits.B := by
    have hh := g.property
    change (g : rootPanelImage Q split j) • panelBase Q j = panelBase Q j at hh
    rw [←hr,ReeSource.panelBase_eq_mk_one Q split j] at hh
    change QuotientGroup.mk (⟨r,rankOne_le_parabolic Q split j r.property⟩*1) =
      (QuotientGroup.mk 1 : Panel Q j) at hh
    have hh' := QuotientGroup.eq.mp hh
    simp only [mul_one,inv_mem_iff] at hh'
    exact hh'
  have hu : (r : X ⧸ Q.D) ∈ simpleRoot Q split j := by
    change r ∈ (simpleRoot Q split j).subgroupOf (rankOne Q split j)
    rw [←nine_actor_borel Q split j hR hroot]
    exact hb
  have hz : (⟨r,hu⟩ : simpleRoot Q split j) = 1 := by
    apply (exists_unique_root_transport Q split j x x hx hx).unique
    · change f r • x = x
      rwa [hr]
    · change (1 : panelActor Q split j) • x = x
      exact one_smul _ _
  apply Subtype.ext
  rw [←hr,show r = 1 from Subtype.ext (congrArg (fun a : simpleRoot Q split j => (a : X ⧸ Q.D)) hz),map_one]
  rfl

private theorem cross_section_reflection_ne_root
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j)
    (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator)
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split j) :
    d.action ⟨s.val,s.mem_rankOne⟩ ≠ d.action u := by
  let x : d.numerator := ⟨a,hax⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : d.action r⁻¹ = d.action u⁻¹ := by rw [map_inv,map_inv,he]
  have hx : d.numeratorAction r⁻¹ x = d.numeratorAction u⁻¹ x := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) hei
    rw [d.action_mk,d.action_mk] at hh
    have hh' := QuotientGroup.eq_iff_div_mem.mp hh
    rw [hden,mem_bot] at hh'
    exact div_eq_one.mp hh'
  have heq := congrArg Subtype.val hx
  rw [d.numeratorAction_apply,d.numeratorAction_apply] at heq
  simp only [coe_inv,inv_inv] at heq
  change (s.val : X ⧸ Q.D)⁻¹*a*s.val = (u : X ⧸ Q.D)⁻¹*a*u at heq
  have haD : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [←rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using a.property
  obtain ⟨hU,hD,hd⟩ := cross_root_separation Q split hm i j hij
  let C := unipotentConjugate split (Q.simple j*Q.simple i)
  have hc := C.mul_mem (C.mul_mem (hU hu) (heq ▸ hD haD)) (C.inv_mem (hU hu))
  have hc' : (a : X ⧸ Q.D) ∈ C := by
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hc
  exact ha (Subtype.ext (disjoint_def.mp hd a.property hc'))

private theorem nine_section_action_not_two
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j)
    (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) : ¬ IsPGroup 2 d.action.range := by
  let f := d.action.rangeRestrict
  let B := Q.tits.B.subgroupOf (rankOne Q split j)
  have hp : Nat.card (Panel Q j) = 9 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  intro ht
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd d.action.rangeRestrict_surjective
    rwa [rankOne_borel_index Q split j,hp] at hh
  obtain ⟨n,hn⟩ := ht.exists_card_eq
  have hidx : (B.map f).index = 1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  have hb : f ⟨s.val,s.mem_rankOne⟩ ∈ B.map f := index_eq_one.mp hidx ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hb
  have hu' : (u : X ⧸ Q.D) ∈ simpleRoot Q split j := by
    change u ∈ (simpleRoot Q split j).subgroupOf (rankOne Q split j)
    rw [←nine_actor_borel Q split j hR hroot]
    exact hu
  exact cross_section_reflection_ne_root Q split j hm i hij s d hden a ha hax u hu'
    (congrArg Subtype.val he).symm

/-- A moved section of the small projective-unitary octagon actor has
at least eight binary dimensions in its effective Frattini quotient. -/
theorem nine_actor_section_bound
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j)
    (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) : 256 ≤ Nat.card d.EffectiveCarrier := by
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f := (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  let e := MulEquiv.ofBijective f ⟨nine_actor_projection_injective Q split j hR hroot,hf⟩
  obtain ⟨hsol,hcard,hfree⟩ := nine_actor_structure Q split j hR hroot
  let := hsol
  have hp : Nat.card (Panel Q j) = 9 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  let α := d.action.comp e.symm.toMonoidHom
  have hra : α.range = d.action.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,←MonoidHom.range_eq_map]
  have hα : Function.Injective α := BinaryPanel.injective_of_non_two_image
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) α
    (hra ▸ nine_section_action_not_two Q split j hR hroot hm i hij s d hden a ha hax)
  have hd : Function.Injective d.action := by
    intro x y he
    have hh : α (e x) = α (e y) := by simpa only [α,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using he
    exact e.injective (hα hh)
  let β := d.effectiveAction.comp e.symm.toMonoidHom
  have hβ : Function.Injective β := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) β
    ((d.effectiveKernel_isTwo_of_faithful hd).comap_of_injective e.symm.toMonoidHom e.symm.injective)
  let ρ := d.effectiveRepresentation.comp e.symm.toMonoidHom
  have hρ : Function.Injective ρ := by
    intro r t he
    apply hβ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => a (Additive.ofMul x)) he)
  have hdim := BinaryPanel.frobenius_nine_degree
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) hfree ρ hρ
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  simp only [Nat.card_zmod] at he
  rw [←he] at hh
  exact hh

private theorem nine_root_frattini_bound
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8) (w : Weyl Q) :
    Nat.card (rootAt Q split j w ⧸ frattini (rootAt Q split j w)) ≤ 4 := by
  rw [Nat.card_congr (rootAtFrattiniEquiv Q split j w).toEquiv]
  let A := simpleRoot Q split j
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split j)⟩
  obtain ⟨a,ha⟩ := HexagonStructure.nine_actor_root_square Q split j hR hroot
  have hnon : frattini A ≠ ⊥ := by
    intro hz
    have hh := pth_power_mem_frattini_of_isPGroup (p := 2) a
    rw [hz,mem_bot] at hh
    exact ha hh
  have hPhi := (frattini A).one_lt_card_iff_ne_bot.mpr hnon
  have he := (frattini A).index_mul_card
  rw [show Nat.card A=8 from hroot] at he
  change (frattini A).index ≤ 4
  nlinarith

/-- A Cartan actor of order coprime to 24 fixes every small unitary root:
its action on the Frattini quotient embeds in permutations of at most four points. -/
theorem nine_roots_centralized_of_coprime_order
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (ho : (orderOf t).Coprime 24) (w : Weyl Q) :
    t ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) := by
  let V := rootAt Q split j w ⧸ frattini (rootAt Q split j w)
  let α := rootAtCartanFrattiniAction Q split j w
  let z : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨t,ht⟩
  have hd : orderOf (α z) ∣ 24 := by
    apply (orderOf_dvd_natCard (α z)).trans
    apply (card_dvd_of_injective (MulAut.toPerm V) MulEquiv.toEquiv_injective).trans
    rw [Nat.card_perm]
    exact Nat.factorial_dvd_factorial (nine_root_frattini_bound Q split j hR hroot w)
  have hα : α z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ho
      ((orderOf_map_dvd α z).trans (Subgroup.orderOf_coe z).symm.dvd) hd)
  have hk : z ∈ (rootAtCartanFrattiniRepresentation Q split j w).ker := by
    change rootAtCartanFrattiniRepresentation Q split j w z = 1
    ext a
    change Additive.ofMul (α z a.toMul) = a
    rw [hα]
    rfl
  rw [rootAtCartanFrattiniRepresentation_kernel] at hk
  intro a ha
  have he := congrArg (fun f : MulAut (rootAt Q split j w) => (f ⟨a,ha⟩ : X ⧸ Q.D)) hk
  change t*a*t⁻¹=a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The separated order-eight root family cannot give an octagon: the
fixed radical has order 512, but its two Frattini layers require order 65536. -/
theorem separated_nine_radical_false
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) ∧
      rootAt Q split i w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) : False := by
  let d : RootSection Q split j := {
    numerator := simpleRemainder Q split j ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _)
    le_radical := inf_le_left
    normalized := separated_radical_centralizer_normalized Q split j hKj c (fun w => (hc w).1)
    denominator := ⊥
    invariant _ := map_bot _ }
  let f := frattiniSection Q split j d
  let A := rootAt Q split j (Q.simple i)
  have hAd : A ≤ d.numerator := by
    change A ≤ simpleRemainder Q split j ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _)
    rw [←separated_radical_centralizer_sup Q split hm j i hij.symm c hc]
    exact le_sup_left.trans le_sup_left
  obtain ⟨a,ha⟩ : ∃ a : A, a^2 ≠ 1 := by
    obtain ⟨u,hu⟩ := HexagonStructure.nine_actor_root_square Q split j hR hroot
    let e : A ≃* simpleRoot Q split j :=
      ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i))
    refine ⟨e.symm u,?_⟩
    intro he
    apply hu
    simpa only [map_pow,map_one,e.apply_symm_apply] using congrArg e he
  have hane : a ≠ 1 := fun he => ha (by rw [he,one_pow])
  let s := actorReflection Q split j
  have h1 := nine_actor_section_bound Q split j hR hroot hm i hij s d rfl a hane (hAd a.property)
  let v : d.numerator := inclusion hAd a
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have h2 := nine_actor_section_bound Q split j hR hroot hm i hij s f rfl (a^2) ha
    (show ((a^2 : A) : X ⧸ Q.D) ∈ f.numerator from
      ⟨v^2,pth_power_mem_frattini_of_isPGroup (p:=2) v,rfl⟩)
  have hden : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  have h1' : 256 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
    change 256 ≤ d.effectiveDenominator.index at h1
    rwa [hden] at h1
  have h2' : 256 ≤ Nat.card (frattini d.numerator) := by
    have hh := h2.trans (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk'_surjective f.effectiveDenominator))
    exact hh.trans_eq (Nat.card_congr
      ((frattini d.numerator).equivMapOfInjective d.numerator.subtype
        d.numerator.subtype_injective).symm.toEquiv)
  have hlo : 65536 ≤ Nat.card d.numerator := by
    calc
      _ = 256*256 := rfl
      _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator)*Nat.card (frattini d.numerator) :=
        Nat.mul_le_mul h1' h2'
      _ = _ := (frattini d.numerator).index_mul_card
  have hsize : Nat.card d.numerator = 512 := by
    have hh := (octagon_separated_root_centralizer_orders Q split hm j i hij.symm c hc).1
    simpa only [hroot,Nat.reducePow] using hh
  omega

/-- Linear fields of orders 16 and 64 are excluded opposite the regular
small projective-unitary actor, in either orientation. -/
theorem nine_actor_large_linear_false
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (hE : Nat.card E = 16 ∨ Nat.card E = 64) : False := by
  obtain ⟨r,hr,hd,hcop⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card E-1 ∧ r.Coprime 24 := by
    rcases hE with hE | hE
    · exact ⟨5,by decide,by rw [hE]; decide,by decide⟩
    · exact ⟨7,by decide,by rw [hE]; decide,by decide⟩
  let : Fact r.Prime := ⟨hr⟩
  let si := actorReflection Q split i
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)) r
    (by rwa [rankOne_cartan_card Q split i hKi μi si])
  have ho : orderOf (t : X ⧸ Q.D) = r := (Subgroup.orderOf_coe t).trans ht
  have hfix := nine_roots_centralized_of_coprime_order Q split j hR hroot t.property.1
    (ho ▸ hcop)
  have hne : (t : X ⧸ Q.D) ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ho
    exact hr.ne_one ho.symm
  have hfree := linear_cartan_separated_roots Q split i j hij hKi μi
    t.property.1 t.property.2 hne hfix
  exact separated_nine_radical_false Q split j hR hroot hm i hij hKj
    ⟨t,t.property.1⟩ (fun w => ⟨hfix w,hfree w⟩)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
