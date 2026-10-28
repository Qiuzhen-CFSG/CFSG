module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineFrattiniExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzukiLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLinear

/-!
# The small projective-unitary hexagon contradiction

An actual root actor of order 72 has its order-eight canonical root as
its whole Borel. Its panel action is faithful and sharply transitive on
ordered pairs of the nine points. Solvability gives the regular ternary
plane. The root has a unique involution and hence a nontrivial square.

For a section containing a crossed root, geometric root separation keeps
the reflection distinct from every root element. An action with two-group
image would identify them by the odd Borel index. Primitivity thus makes
the section action faithful, and coprime Frattini faithfulness does the
same on its effective quotient. The regular ternary plane forces binary
degree at least eight. Applying this to the radical and its Frattini
subgroup gives |U_sj| ≥ 2^16, excluding opposite root orders at most eight.

For a linear opposite, its own two-layer bound and the original square
profile force that small order bound. The companion CFSG module constructs
every premise from the original PSU3(2) marking, including the (2B)
containment, and excludes it against the entire original F.1.1 catalogue.
The special SU3(2) actor has order 216 and is not covered by this argument.

Source: Fong--Seitz I (4D), (5D), and the first case of (6D), printed
pp.21--22,26--27,41. All sections and actions belong to the same marked
finite quotient; no perfectness assumption is imposed.
-/

public noncomputable section
open Subgroup MulAction
open scoped IsMulCommutative MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource GTwoSource
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

/-- A root of a solvable nine-point actor has a nontrivial square. -/
theorem nine_actor_root_square
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    ∃ a : simpleRoot Q split j, a^2 ≠ 1 := by
  classical
  obtain ⟨hsol,hcard,hfree⟩ := nine_actor_structure Q split j hR hroot
  let := hsol
  have hp : Nat.card (Panel Q j) = 9 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  let f : simpleRoot Q split j →* stabilizer (rootPanelImage Q split j) (panelBase Q j) :=
    ((rootImageProjection Q split j).comp
      (inclusion (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left))).codRestrict _
        (fun r => panelRoot_fixes_base Q split j r)
  have hf : Function.Injective f := by
    intro a b he
    apply simpleRoot_panelAction_injective Q split j
    exact congrArg (fun a => a.val.val) he
  by_contra! hn
  have hu (a b : simpleRoot Q split j) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
    apply hf
    apply BinaryPanel.stabilizer_involution_unique
      (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) hfree
    · exact fun he => ha (hf (he.trans f.map_one.symm))
    · exact fun he => hb (hf (he.trans f.map_one.symm))
    · rw [←map_pow,hn,map_one]
    · rw [←map_pow,hn,map_one]
  have hi : Function.Injective (fun a : simpleRoot Q split j => decide (a = 1)) := by
    intro a b he
    by_cases ha : a = 1
    · have hb : b = 1 := by simpa [ha] using he.symm
      exact ha.trans hb.symm
    · have hb : b ≠ 1 := by simpa [ha] using he.symm
      exact hu a b ha hb
  have hc := Nat.card_le_card_of_injective _ hi
  norm_num [hroot] at hc

private theorem nine_section_action_not_two
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
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
  apply ownRoot_oddProduct_moves_section Q split hm i j hij s u⁻¹
    ((simpleRoot Q split j).inv_mem hu') d hden a ha hax
  have he' : d.action u = d.action ⟨s.val,s.mem_rankOne⟩ := congrArg Subtype.val he
  rw [map_mul,map_inv,←he',mul_inv_cancel]

/-- The actual effective section of a solvable order-72 root actor has
at least eight binary dimensions whenever a crossed root moves it. -/
theorem nine_actor_section_bound
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
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

/-- Both successive Frattini quotients of the actual radical have order
at least 256 for the solvable order-72 root actor. -/
theorem nine_actor_radical_two_layers
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    256 ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
      256 ≤ Nat.card (frattini (simpleRemainder Q split j) ⧸
        frattini (frattini (simpleRemainder Q split j))) ∧
      65536 ≤ Nat.card (simpleRemainder Q split j) := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  obtain ⟨x,hx⟩ := nine_actor_root_square Q split j hR hroot
  let e := ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j)
    (representative (Q.simple i))
  let a : rootAt Q split j (Q.simple i) := e.symm x
  have ha2 : a^2 ≠ 1 := by
    intro he
    apply hx
    have he' : (e.symm x)^2 = 1 := he
    have hh := congrArg e he'
    simpa only [map_pow,map_one,MulEquiv.apply_symm_apply] using hh
  have ha : a ≠ 1 := fun he => ha2 (by rw [he,one_pow])
  have hA : rootAt Q split j (Q.simple i) ≤ d.numerator :=
    (le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)
  have h1 := nine_actor_section_bound Q split j hR hroot hm i hij s d rfl a ha (hA a.property)
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have h2 := nine_actor_section_bound Q split j hR hroot hm i hij s f rfl (a^2) ha2
    (show ((a^2 : rootAt Q split j (Q.simple i)) : X ⧸ Q.D) ∈ f.numerator from
      ⟨(inclusion hA a)^2,pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩)
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]; exact sup_bot_eq _
  have hf : f.effectiveDenominator = frattini f.numerator := by
    rw [f.effectiveDenominator_eq]; exact sup_bot_eq _
  change 256 ≤ d.effectiveDenominator.index at h1
  change 256 ≤ f.effectiveDenominator.index at h2
  rw [hd] at h1
  rw [hf] at h2
  let eF : frattini d.numerator ≃* f.numerator :=
    (frattini d.numerator).equivMapOfInjective d.numerator.subtype d.numerator.subtype_injective
  have hc := Nat.card_congr (QuotientGroup.congr _ _ eF (frattini_map_equiv eF)).toEquiv
  change Nat.card (frattini d.numerator ⧸ frattini (frattini d.numerator)) =
    Nat.card (f.numerator ⧸ frattini f.numerator) at hc
  have h2' : 256 ≤ Nat.card (frattini d.numerator ⧸ frattini (frattini d.numerator)) := hc ▸ h2
  refine ⟨h1,h2',?_⟩
  have hle := Nat.card_le_card_of_surjective _
    (QuotientGroup.mk'_surjective (frattini (frattini d.numerator)))
  have hmul := (frattini d.numerator).card_mul_index
  rw [index_eq_card] at hmul
  change 256 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) at h1
  change 65536 ≤ Nat.card d.numerator
  nlinarith

/-- A small projective-unitary root actor cannot occur opposite a root of
order at most eight in the same split hexagon. -/
theorem nine_actor_small_opposite_excluded
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hi : Nat.card (simpleRoot Q split i) ≤ 8) : False := by
  have hlarge := (nine_actor_radical_two_layers Q split j hR hroot hm i hij s hKj).2.2
  have hU := unipotent_card_even Q split 3 hm
  have hprod : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) =
      Nat.card (simpleRoot Q split i)*8 := by
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (hij rfl).elim
    · rw [hroot]
    · rw [hroot,Nat.mul_comm]
    · exact (hij rfl).elim
  rw [hprod] at hU
  have hbound : Nat.card split.U ≤ 262144 := by
    rw [hU]
    exact Nat.pow_le_pow_left (Nat.mul_le_mul_right 8 hi) 3
  have hrem := unipotent_card_simple Q split j
  rw [hroot] at hrem
  omega

/-- The linear opposite is excluded in every field: the linear two-layer
bound and source square profile first force its root order to be at most eight. -/
theorem nine_actor_linear_opposite_excluded
    [Group.IsSolvable (rankOne Q split j)]
    (hR : Nat.card (rankOne Q split j) = 72)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  apply nine_actor_small_opposite_excluded Q split j hR hroot hm i hij sj hKj
  by_contra! hbig
  obtain ⟨a,ha⟩ := (split.isTwo.to_le (simpleRoot_le Q split i)).exists_card_eq
  have ha4 : 4 ≤ a := by
    have hh : 2^3 < 2^a := by simpa only [ha,Nat.reducePow] using hbig
    have ht := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh
    omega
  have hF : Nat.card F = 2^a := (simpleRoot_card Q split i hKi μi).symm.trans ha
  have hb := linear_two_layer_bound_of_opposite_square Q split hm j i hij.symm
    hKj hKi μi si (by omega) hF (nine_actor_root_square Q split j hR hroot)
  have hU := unipotent_card_even Q split 3 hm
  have hprod : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) = 2^a*8 := by
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (hij rfl).elim
    · rw [ha,hroot]
    · rw [ha,hroot,Nat.mul_comm]
    · exact (hij rfl).elim
  rw [hprod] at hU
  have hrem := unipotent_card_simple Q split i
  rw [ha,hU] at hrem
  have hpow : 2^(5*a) ≤ 2^(3*a+9) := by
    calc
      2^(5*a) = 2^a*2^(4*a) := by rw [←pow_add]; congr 1; omega
      _ ≤ 2^a*Nat.card (simpleRemainder Q split i) := Nat.mul_le_mul_left _ hb
      _ = (2^a*8)^3 := hrem.symm
      _ = 2^(3*a+9) := by
        rw [show (8 : ℕ) = 2^3 from rfl,←pow_add,←pow_mul]
        congr 1
        omega
  have hle := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hp : a%2 = 1%2 := mixed_unitary_square_profile_parity (n := 1) (by
    simpa only [ha,hroot,Nat.reducePow] using hsquare)
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
