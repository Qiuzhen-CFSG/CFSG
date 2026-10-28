module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryCentralizers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.DerivedRadical
public import Theory.Frattini.BinarySquares
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# Order-five movement on the derived octagonal radical

The seven-root product bounds the image of Φ(V) in V/[V,V] by the product
of the seven root Frattini orders. In the binary Suzuki row, four roots are
elementary and three are cyclic of order four; consequently
|Φ(V)| ≤ 8 |[V,V]|. This uses the actual root factorization, without
assuming Φ(V)=[V,V] or the later nonzero mixed commutator.

The corrected reflection times the central root involution already moves
Φ(V) and has order five. Its fixed subgroup there has index at least 16.
It therefore cannot fix [V,V] pointwise. Coprime Frattini faithfulness and
the normal-subgroup structure of Sz(2) give a faithful action on the actual
derived Frattini section. The other root field remains unrestricted.

Source: Fong--Seitz I (1973), the effective derived section preceding (6.1),
printed p.52, and (5D)(b), pp.26--27. This supplies the binary movement
premise left explicit in the earlier derived-radical interface. The source
application discharges the elementary-root and (6.3) premises from the
natural panel markings and transports the result to the original endpoint.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

private theorem frattini_image_eq_square_range {G C : Type*} [Group G] [Finite G]
    [CommGroup C] (hG : IsPGroup 2 G) (f : G →* C) :
    (frattini G).map f = ((powMonoidHom 2).comp f).range := by
  rw [hG.frattini_eq_closure_squares, MonoidHom.map_closure]
  have he : f '' Set.range (fun x : G => x^2) =
      (((powMonoidHom 2).comp f).range : Set C) := by
    ext y
    simp only [Set.mem_image,Set.mem_range]
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨x,(map_pow f x 2).symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x^2,⟨x,rfl⟩,map_pow f x 2⟩
  rw [he,closure_eq]

private theorem product_set_card_le {C : Type*} [Group C]
    (l : List (Set C)) : Nat.card l.prod ≤ (l.map (fun A : Set C => Nat.card A)).prod := by
  induction l with
  | nil => simp
  | cons A l ih =>
    simpa only [List.prod_cons,List.map_cons] using
      (Set.natCard_mul_le (s := A) (t := l.prod)).trans (Nat.mul_le_mul_left _ ih)

private theorem frattini_image_card_le_of_product {G C : Type*} [Group G] [Finite G]
    [CommGroup C] [Finite C] (hG : IsPGroup 2 G) (f : G →* C)
    (l : List (Subgroup G))
    (hl : (l.map (fun A : Subgroup G => (A : Set G))).prod = Set.univ) :
    Nat.card ((frattini G).map f) ≤ (l.map (fun A : Subgroup G => Nat.card (frattini A))).prod := by
  let s : G →* C := (powMonoidHom 2).comp f
  have he : (s.range : Set C) = (l.map (fun A : Subgroup G => s '' (A : Set G))).prod := by
    have hh := Set.image_list_prod s (l.map (fun A : Subgroup G => (A : Set G)))
    simpa only [hl,Set.image_univ,List.map_map,MonoidHom.coe_range,Function.comp_def] using hh
  rw [frattini_image_eq_square_range hG f]
  change Nat.card (s.range : Set C) ≤ _
  rw [he]
  apply (product_set_card_le _).trans
  rw [List.map_map]
  apply List.prod_le_prod'
  intro A hA
  have hs : s '' (A : Set G) = (((powMonoidHom 2).comp (f.comp A.subtype)).range : Set C) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩; exact ⟨x,x.property,rfl⟩
  change Nat.card (s '' (A : Set G)) ≤ _
  rw [hs,←frattini_image_eq_square_range (hG.to_subgroup A)]
  exact Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)

private theorem frattini_card_le_of_product {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (l : List (Subgroup G))
    (hl : (l.map (fun A : Subgroup G => (A : Set G))).prod = Set.univ) :
    Nat.card (frattini G) ≤ (l.map (fun A : Subgroup G => Nat.card (frattini A))).prod *
      Nat.card (commutator G) := by
  let f : G →* Abelianization G := Abelianization.of
  let g := f.comp (frattini G).subtype
  have hker : g.ker = (commutator G).subgroupOf (frattini G) := by
    change ((Abelianization.of : G →* Abelianization G).comp (frattini G).subtype).ker = _
    rw [←MonoidHom.comap_ker,Abelianization.ker_of]
    rfl
  have hr : g.range = (frattini G).map f := by
    rw [MonoidHom.range_comp,range_subtype]
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  have hcard := g.ker.index_mul_card
  rw [index_ker,hr,hker,Nat.card_congr
    (subgroupOfEquivOfLe (commutator_le_frattini_of_isPGroup (p := 2))).toEquiv] at hcard
  rw [←hcard]
  exact Nat.mul_le_mul_right _ (frattini_image_card_le_of_product hG f l hl)

private theorem frattini_card_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (frattini A) = Nat.card (frattini B) := by
  rw [←frattini_map_equiv e,card_map_of_injective e.injective]

private theorem frattini_card_le_ambient_product {Y : Type*} [Group Y] [Finite Y]
    (V : Subgroup Y) (hV : IsPGroup 2 V) (l : List (Subgroup Y))
    (hAV : ∀ A ∈ l, A ≤ V)
    (hprod : (l.map (fun A : Subgroup Y => (A : Set Y))).prod = V) :
    Nat.card (frattini V) ≤ (l.map (fun A : Subgroup Y => Nat.card (frattini A))).prod *
      Nat.card (commutator V) := by
  let k := l.map (fun A => A.subgroupOf V)
  have he : V.subtype '' (k.map (fun A : Subgroup V => (A : Set V))).prod = V := by
    rw [Set.image_list_prod]
    dsimp only [k]
    simp only [List.map_map,Function.comp_def]
    have hh : l.map (fun A : Subgroup Y => V.subtype '' (A.subgroupOf V : Set V)) =
        l.map (fun A : Subgroup Y => (A : Set Y)) := by
      apply List.map_congr_left
      intro A hA
      change ((A.subgroupOf V).map V.subtype : Set Y) = A
      rw [map_subgroupOf_eq_of_le (hAV A hA)]
    change (l.map (fun A : Subgroup Y => V.subtype '' (A.subgroupOf V : Set V))).prod = V
    rw [hh,hprod]
  have hk : (k.map (fun A : Subgroup V => (A : Set V))).prod = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : (x : Y) ∈ V.subtype '' (k.map (fun A : Subgroup V => (A : Set V))).prod := by
      rw [he]; exact x.property
    obtain ⟨y,hy,hyx⟩ := hx
    exact (V.subtype_injective hyx) ▸ hy
  apply (frattini_card_le_of_product hV k hk).trans
  apply Nat.mul_le_mul_right
  dsimp only [k]
  rw [List.map_map]
  apply List.prod_le_prod'
  intro A hA
  exact le_of_eq (frattini_card_equiv (subgroupOfEquivOfLe (hAV A hA)))

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem remainder_seven (hm : rotationOrder Q = 8) (b : Bool) :
    rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
      simpleRemainder Q split (if b then 0 else 1) := by
  have hw : longest Q = Q.simple (if b then 0 else 1)*alternatingWord Q b 7 := by
    have hh := (alternatingWord_longest Q (!b)).symm
    rw [hm] at hh
    cases b <;> exact hh
  change split.U ⊓ unipotentConjugate split (longest Q*(alternatingWord Q b 7)⁻¹) = _
  rw [hw,mul_inv_cancel_right]
  rfl

private theorem frattini_card_conjugate (A : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    Nat.card (frattini (rightConjugate A n)) = Nat.card (frattini A) :=
  frattini_card_equiv (RootAction.conjugateEquiv A n)

/-- The seven actual positive factors bound the Frattini image in the abelianization. -/
theorem octagon_frattini_card_le_derived
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (frattini (simpleRemainder Q split i)) ≤
      Nat.card (frattini (simpleRoot Q split j))^4 *
        Nat.card (frattini (simpleRoot Q split i))^3 *
          Nat.card (commutator (simpleRemainder Q split i)) := by
  have hh (b : Bool) := frattini_card_le_ambient_product
    (simpleRemainder Q split (if b then 0 else 1))
    (split.isTwo.to_le inf_le_left) (orderedRoots Q split b 7)
    (fun A hA => by
      rw [←remainder_seven Q split hm b]
      exact orderedRoots_le Q split b 7 (by omega) A hA)
    (by
      have hp := orderedRoots_product Q split b 7 (by omega)
      rw [remainder_seven Q split hm b] at hp
      simpa only [bind_pure_comp,Functor.map,List.map_map,Function.comp_def] using hp)
  have hcount (b : Bool) :
      ((orderedRoots Q split b 7).map
        (fun A : Subgroup (X ⧸ Q.D) => Nat.card (frattini A))).prod =
      Nat.card (frattini (simpleRoot Q split (if b then 1 else 0)))^4 *
        Nat.card (frattini (simpleRoot Q split (if b then 0 else 1)))^3 := by
    cases b
    all_goals
      try rw [show (if true then (1 : Fin 2) else 0) = 1 by decide]
      try rw [show (if true then (0 : Fin 2) else 1) = 0 by decide]
      try rw [show (if false then (1 : Fin 2) else 0) = 0 by decide]
      try rw [show (if false then (0 : Fin 2) else 1) = 1 by decide]
      simp only [orderedRoots,List.map_cons,List.map_nil,List.prod_cons,
        List.prod_nil,frattini_card_conjugate,Bool.not_false,
        Bool.not_true,Bool.false_eq_true,↓reduceIte]
      ring
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := hh true
    rw [hcount] at ht
    rw [show (if true then (1 : Fin 2) else 0) = 1 by decide,
      show (if true then (0 : Fin 2) else 1) = 0 by decide] at ht
    exact ht
  · have ht := hh false
    rw [hcount] at ht
    rw [show (if false then (1 : Fin 2) else 0) = 0 by decide,
      show (if false then (0 : Fin 2) else 1) = 1 by decide] at ht
    exact ht
  · exact (hij rfl).elim

open BenderSuzuki.MatrixGroups
variable (i j : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include μ hB in
/-- Three binary Suzuki factors contribute at most three squares modulo the derived radical. -/
theorem binary_frattini_card_le_eight_derived
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hlin : IsElementaryAbelian 2 (simpleRoot Q split j)) :
    Nat.card (frattini (simpleRemainder Q split i)) ≤
      8 * Nat.card (commutator (simpleRemainder Q split i)) := by
  have hs : Nat.card (frattini (simpleRoot Q split i)) = 2 := by
    have hh := (frattini (simpleRoot Q split i)).card_mul_index
    change Nat.card (frattini (simpleRoot Q split i)) *
      Nat.card (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) = _ at hh
    rw [suzuki_frattini_quotient_card Q split i 0 μ hB,
      Nat.card_congr (suzukiRootEquiv Q split i 0 μ hB).toEquiv,matrixRoot_card] at hh
    norm_num at hh
    omega
  let := hlin
  let : Fact (IsPGroup 2 (simpleRoot Q split j)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  have hl : Nat.card (frattini (simpleRoot Q split j)) = 1 := by
    rw [frattini_eq_bot_of_isElementaryAbelian (p := 2),card_bot]
  have hh := octagon_frattini_card_le_derived Q split hm i j hij
  simpa only [hl,hs,one_pow,Nat.reducePow,one_mul] using hh

variable (hV : simpleRemainder Q split i ≤ localKernel Q i)

include hB in
/-- The actual order-five product moves the DERIVED source section. No movement premise remains. -/
theorem binary_frattiniMover_moves_derived
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hlin : IsElementaryAbelian 2 (simpleRoot Q split j))
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    (derivedRadicalSection Q split i hV).action (frattiniMover Q split i 0 μ hB) ≠ 1 := by
  let V := simpleRemainder Q split i
  let c := frattiniMover Q split i 0 μ hB
  let ρ : rankOne Q split i →* MulAut V := (radicalSection Q split i hV).numeratorAction
  let r := ρ c
  let a := MulAut.characteristic (frattini V) r
  have htwo : IsPGroup 2 V := split.isTwo.to_le inf_le_left
  let : Fact (IsPGroup 2 V) := ⟨htwo⟩
  have hD : commutator V ≤ frattini V := commutator_le_frattini_of_isPGroup (p := 2)
  have hc : c^5 = 1 := by
    rw [←binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm,pow_orderOf_eq_one]
  have ha : a^5 = 1 := by
    change (MulAut.characteristic (frattini V) r)^5 = 1
    have hr : r^5 = 1 := by
      change (ρ c)^5 = 1
      rw [←map_pow,hc,map_one]
    rw [←map_pow,hr,map_one]
  have hne : a ≠ 1 := binary_mover_frattini_restriction_ne_one Q split i hV μ hB hm j hij hcomm
  have hidx := quintic_fixed_index_ge (htwo.to_subgroup (frattini V)) a ha hne
  intro hfix
  let d := derivedRadicalSection Q split i hV
  have hinc : (commutator V).subgroupOf (frattini V) ≤ a.fixedSubgroup := by
    intro v hv
    apply (MulAut.mem_fixedSubgroup a v).mpr
    have hx : (v.val : X ⧸ Q.D) ∈ d.numerator := by
      change (v.val : X ⧸ Q.D) ∈ ⁅V,V⁆
      rw [←map_subtype_commutator]
      exact mem_map_of_mem V.subtype hv
    let x : d.numerator := ⟨v.val,hx⟩
    have he : d.numeratorAction c x = x := by
      have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) hfix
      rw [d.action_mk] at hh
      exact congrArg QuotientGroup.quotientBot hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : d.numerator => (z : X ⧸ Q.D)) he
  have hcard := card_le_of_le hinc
  rw [Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv] at hcard
  have hlo : 16 * Nat.card (commutator V) ≤ Nat.card (frattini V) := by
    calc
      _ ≤ a.fixedSubgroup.index * Nat.card a.fixedSubgroup := Nat.mul_le_mul hidx hcard
      _ = _ := a.fixedSubgroup.index_mul_card
  have hhi := binary_frattini_card_le_eight_derived Q split i j μ hB hm hij hlin
  have hp := Nat.card_pos (α := commutator V)
  change Nat.card (frattini V) ≤ 8 * Nat.card (commutator V) at hhi
  omega

include hB in
/-- Faithful effectivity of the binary derived section with its movement witness discharged. -/
theorem binary_derivedRadical_effectiveAction_injective_of_octagon
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hlin : IsElementaryAbelian 2 (simpleRoot Q split j))
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    Function.Injective (derivedRadicalSection Q split i hV).effectiveAction :=
  binary_suzuki_section_effectiveAction_injective Q split i μ hB _
    (frattiniMover Q split i 0 μ hB)
    (binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm)
    (binary_frattiniMover_moves_derived Q split i j μ hB hV hm hij hlin hcomm)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
