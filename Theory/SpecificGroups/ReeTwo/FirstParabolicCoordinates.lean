module

public import Theory.SpecificGroups.ReeTwo.MaximalCharacters
public import Theory.SpecificGroups.ReeTwo.FirstParabolic
public import Theory.SpecificGroups.ReeTwo.SylowCenter

/-!
# Coordinates for the first Ree two parabolic core

The second center consists of products of roots 11 and 12. To bound it,
three commutation tests modulo the known center suffice; a finite check in
the verified coordinate group proves the bound. Polynomial multiplication
shows that root 11 lies in the second center and that an element commutes
with it exactly when its root-3 coordinate is zero. Root 12 is central.
Consequently `C_S(Z₂(S))` is the root-3 character kernel, of order 2048.

Its three binary quotient coordinates are cyclic-four parity, the root-4
coordinate, and the sum of the root-5 and root-6 coordinates. The cyclic
factor preserves the latter two on this subgroup. An explicit section
proves surjectivity. Eight products of squares generate the kernel by the
root normal form, so the kernel is characteristic. The fiber over `(0,0,1)`
consists entirely of elements of order four: a kernel-checked calculation
uses its eight independent binary parameters. The identity and six elements
whose fourth powers are nonidentity exclude the other seven fibers.

Source: Shinoda (1975), (2.3), pp. 81–83, via the verified `Core`, `RootAction`
and `Sylow` coordinates. The parabolic terminology follows van Beek (2024),
Proposition 3.1, p. 10. No external subgroup or automorphism census is used.
-/

open scoped commutatorElement
namespace ReeTwo.SylowModel

private def commuteModLast (x y : SylowModel) : Prop :=
  x * y = y * x ∨ x * y = root 9 * (y * x)
private instance (x y : SylowModel) : Decidable (commuteModLast x y) := by
  unfold commuteModLast
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem second_center_test : ∀ g : SylowModel,
    commuteModLast g (root 0) → commuteModLast g (root 2) →
    commuteModLast g rootOne →
    g = 1 ∨ g = root 8 ∨ g = root 9 ∨ g = root 8 * root 9 := by
  decide +kernel

private theorem commuteModLast_of_mem_second_center (g : SylowModel)
    (hg : g ∈ Subgroup.upperCentralSeries SylowModel 2) (y : SylowModel) :
    commuteModLast g y := by
  have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hg y
  rw [Subgroup.upperCentralSeries_one] at h
  rcases eq_one_or_root_twelve_of_mem_center _ h with h | h
  · left
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he
  · right
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he

/-- Elements of the second center are products of roots 11 and 12. -/
public theorem second_center_cases (g : SylowModel)
    (hg : g ∈ Subgroup.upperCentralSeries SylowModel 2) :
    g = 1 ∨ g = root 8 ∨ g = root 9 ∨ g = root 8 * root 9 :=
  second_center_test g (commuteModLast_of_mem_second_center g hg _)
    (commuteModLast_of_mem_second_center g hg _)
    (commuteModLast_of_mem_second_center g hg _)

private theorem action_last (t : FiveFour.Cyclic 4) (i : CoreRoot)
    (hi : i = 8 ∨ i = 9) :
    Core.complementAction (SemidirectProduct.inr t) (Core.root i) = Core.root i := by
  exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, ∀ i : CoreRoot,
    i = 8 ∨ i = 9 → Core.complementAction (SemidirectProduct.inr t) (Core.root i) =
      Core.root i) t i hi

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

private theorem root_nine_commute (g : SylowModel) : root 9 * g = g * root 9 := by
  apply SemidirectProduct.ext
  · change Core.root 9 * Core.complementAction (SemidirectProduct.inr 1) g.left =
      g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 9)
    rw [map_one, map_one, MulAut.one_apply, action_last _ _ (Or.inr rfl)]
    apply Core.ext <;> simp [core_mul_eq, Core.mul, Core.root, Core.ofCoords]
    ring
  · simp [root]

private theorem root_nine_mem_center : root 9 ∈ Subgroup.center SylowModel := by
  exact Subgroup.mem_center_iff.mpr (fun g => (root_nine_commute g).symm)

private theorem root_eight_commute_iff (g : SylowModel) :
    g * root 8 = root 8 * g ↔ g.left.b0 = 0 := by
  have hl : (g * root 8).left = g.left * Core.root 8 := by
    change g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 8) = _
    rw [action_last _ _ (Or.inl rfl)]
  have hr : (root 8 * g).left = Core.root 8 * g.left := by
    change Core.root 8 * Core.complementAction (SemidirectProduct.inr 1) g.left = _
    rw [map_one, map_one, MulAut.one_apply]
  constructor
  · intro h
    have he := congrArg (fun x : SylowModel => x.left.b9) h
    change (g * root 8).left.b9 = (root 8 * g).left.b9 at he
    rw [hl, hr] at he
    simpa [core_mul_eq, Core.mul, Core.root, Core.ofCoords, eq_comm] using he
  · intro h
    apply SemidirectProduct.ext
    · rw [hl, hr]
      apply Core.ext <;> simp [core_mul_eq, Core.mul, Core.root, Core.ofCoords, h]
      ring
    · simp [root]

private theorem root_eight_commuteModLast (g : SylowModel) : commuteModLast (root 8) g := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) g.left.b0 with h | h
  · exact Or.inl ((root_eight_commute_iff g).mpr h).symm
  · right
    apply SemidirectProduct.ext
    · change Core.root 8 * Core.complementAction (SemidirectProduct.inr 1) g.left =
        Core.root 9 * Core.complementAction (SemidirectProduct.inr 1)
          (g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 8))
      rw [map_one, map_one, MulAut.one_apply, MulAut.one_apply,
        action_last _ _ (Or.inl rfl)]
      apply Core.ext <;> simp [core_mul_eq, Core.mul, Core.root, Core.ofCoords, h]
      ring
    · simp [root]

private theorem root_eight_mem_second_center :
    root 8 ∈ Subgroup.upperCentralSeries SylowModel 2 := by
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro g
  rw [Subgroup.upperCentralSeries_one]
  rcases root_eight_commuteModLast g with h | h
  · have he : ⁅root 8, g⁆ = 1 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact (Subgroup.center SylowModel).one_mem
  · have he : ⁅root 8, g⁆ = root 9 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact root_nine_mem_center

/-- The first parabolic core is precisely the kernel of the root-3 character. -/
public theorem firstParabolicCore_eq_rootThreeCharacter_ker :
    firstParabolicCore = rootThreeCharacter.ker := by
  ext g
  change g ∈ Subgroup.centralizer
    (Subgroup.upperCentralSeries SylowModel 2 : Set SylowModel) ↔ g.left.b0 = 0
  constructor
  · intro h
    apply (root_eight_commute_iff g).mp
    exact (Subgroup.mem_centralizer_iff.mp h _ root_eight_mem_second_center).symm
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    rcases second_center_cases x hx with rfl | rfl | rfl | rfl
    · simp
    · exact ((root_eight_commute_iff g).mpr h).symm
    · exact root_nine_commute g
    · rw [mul_assoc, root_nine_commute, ← mul_assoc,
        ((root_eight_commute_iff g).mpr h).symm, mul_assoc]

/-- The first parabolic core is the parameter triple `(0, 1, 0)`. -/
public theorem firstParabolicCore_eq_maximalCharacter_ker :
    firstParabolicCore = (maximalCharacter 0 1 0).ker := by
  rw [firstParabolicCore_eq_rootThreeCharacter_ker]
  simp [maximalCharacter, show (1 : ZMod 2).val = 1 from rfl]

/-- The first parabolic core has order 2048. -/
public theorem firstParabolicCore_card : Nat.card firstParabolicCore = 2048 := by
  rw [firstParabolicCore_eq_maximalCharacter_ker]
  exact maximalCharacter_ker_card 0 1 0 (Or.inr (Or.inl (by decide)))

/-- Membership in the first parabolic core is vanishing of the root-3 coordinate. -/
@[simp] public theorem mem_firstParabolicCore_iff (x : SylowModel) :
    x ∈ firstParabolicCore ↔ x.left.b0 = 0 := by
  rw [firstParabolicCore_eq_rootThreeCharacter_ker]
  rfl
/-- The three binary coordinates of the first parabolic quotient. -/
@[expose] public def firstParabolicCoordinates (x : SylowModel) : Fin 3 → ZMod 2 :=
  ![(parity x.right).toAdd, x.left.b1, x.left.b2 + x.left.b3]
private def middleCoordinates : Core →* Multiplicative (Fin 2 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b1, x.b2 + x.b3]
  map_one' := by decide +kernel
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · rfl
    · change (x.b2 + y.b2) + (x.b3 + y.b3) = (x.b2 + x.b3) + (y.b2 + y.b3)
      ring
private def transformedCoordinates : Core →* Multiplicative (Fin 2 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b1 + x.b0, x.b2 + x.b3 + x.b0]
  map_one' := by decide +kernel
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · change (x.b1 + y.b1) + (x.b0 + y.b0) = (x.b1 + x.b0) + (y.b1 + y.b0)
      ring
    · change (x.b2 + y.b2) + (x.b3 + y.b3) + (x.b0 + y.b0) =
        (x.b2 + x.b3 + x.b0) + (y.b2 + y.b3 + y.b0)
      ring
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem middleCoordinates_a : middleCoordinates.comp Core.a.toMonoidHom =
    transformedCoordinates := by
  apply Core.hom_ext
  exact (by decide +kernel : ∀ i : CoreRoot,
    middleCoordinates (Core.a (Core.root i)) = transformedCoordinates (Core.root i))
private theorem quotient_action_check (t : FiveFour.Cyclic 4) (x : Core)
    (hx : x.b0 = 0) :
    (Core.complementAction (SemidirectProduct.inr t) x).b1 = x.b1 ∧
    (Core.complementAction (SemidirectProduct.inr t) x).b2 +
      (Core.complementAction (SemidirectProduct.inr t) x).b3 = x.b2 + x.b3 := by
  have ha (y : Core) (hy : y.b0 = 0) : middleCoordinates (Core.a y) = middleCoordinates y := by
    have h := DFunLike.congr_fun middleCoordinates_a y
    change middleCoordinates (Core.a y) = Multiplicative.ofAdd ![y.b1 + y.b0, y.b2 + y.b3 + y.b0] at h
    change middleCoordinates (Core.a y) = Multiplicative.ofAdd ![y.b1, y.b2 + y.b3]
    simpa only [hy, add_zero] using h
  have hb (y : Core) : (Core.a y).b0 = y.b0 := by
    exact congrArg Multiplicative.toAdd
      (Core.rootThreeCharacter_action (FiveFour.generator 4) y)
  have hp (n : ℕ) : middleCoordinates ((Core.a ^ n) x) = middleCoordinates x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ha, ih]
      have hzero : ∀ k : ℕ, ((Core.a ^ k) x).b0 = 0 := by
        intro k
        induction k with
        | zero => exact hx
        | succ k hk => rw [pow_succ', MulAut.mul_apply, hb, hk]
      exact hzero n
  have h : middleCoordinates (Core.complementAction (SemidirectProduct.inr t) x) =
      middleCoordinates x := by
    rw [← FiveFour.generator_pow_val t, map_pow, map_pow]
    exact hp _
  exact ⟨congrFun (congrArg Multiplicative.toAdd h) 0,
    congrFun (congrArg Multiplicative.toAdd h) 1⟩
/-- The characteristic binary quotient of the first parabolic core. -/
@[expose] public def firstParabolicQuotient : firstParabolicCore →* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (firstParabolicCoordinates x)
  map_one' := by decide +kernel
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · change (parity ((x : SylowModel).right * (y : SylowModel).right)).toAdd = _
      rw [map_mul]; rfl
    · have h := (quotient_action_check (x : SylowModel).right (y : SylowModel).left
        ((mem_firstParabolicCore_iff _).mp y.property)).1
      change (x : SylowModel).left.b1 +
        (Core.complementAction (SemidirectProduct.inr (x : SylowModel).right) (y : SylowModel).left).b1 = _
      rw [h]; rfl
    · have h := (quotient_action_check (x : SylowModel).right (y : SylowModel).left
        ((mem_firstParabolicCore_iff _).mp y.property)).2
      change ((x : SylowModel).left.b2 +
        (Core.complementAction (SemidirectProduct.inr (x : SylowModel).right) (y : SylowModel).left).b2) +
        ((x : SylowModel).left.b3 +
        (Core.complementAction (SemidirectProduct.inr (x : SylowModel).right) (y : SylowModel).left).b3) = _
      calc
        _ = (x : SylowModel).left.b2 + (x : SylowModel).left.b3 +
          ((Core.complementAction (SemidirectProduct.inr (x : SylowModel).right) (y : SylowModel).left).b2 +
          (Core.complementAction (SemidirectProduct.inr (x : SylowModel).right) (y : SylowModel).left).b3) := by ring
        _ = _ := by rw [h]; rfl

/-- Binary digits encode the core, with the next two digits encoding the cyclic factor. -/
private def element (n : ℕ) : SylowModel :=
  ⟨Core.ofCoords (fun i => ((n / 2 ^ i.val : ℕ) : ZMod 2)),
    Multiplicative.ofAdd ((n / 1024 : ℕ) : ZMod 4)⟩
private def sectionElement (v : Fin 3 → ZMod 2) : SylowModel :=
  ⟨⟨0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩,
    Multiplicative.ofAdd ((v 0).val : ZMod 4)⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem section_check : ∀ v : Fin 3 → ZMod 2,
    firstParabolicCoordinates (sectionElement v) = v := by decide +kernel
/-- Every binary triple occurs in the quotient. -/
public theorem firstParabolicQuotient_surjective : Function.Surjective firstParabolicQuotient := by
  intro v
  refine ⟨⟨sectionElement v.toAdd, (mem_firstParabolicCore_iff _).mpr rfl⟩, ?_⟩
  exact congrArg Multiplicative.ofAdd (section_check v.toAdd)
private def seed (i : Fin 8) : SylowModel :=
  element (![2, 4, 6, 8, 12, 1024, 1026, 1032] i)
private theorem seed_mem (i : Fin 8) : seed i ∈ firstParabolicCore := by
  rw [mem_firstParabolicCore_iff]
  exact (by decide +kernel : ∀ i, (seed i).left.b0 = 0) i
private def squareSeed (i : Fin 8) : firstParabolicCore := ⟨seed i, seed_mem i⟩
/-- Roots 5·6, 7, …, 12, and the square of the cyclic generator. -/
private def kernelGenerator (i : Fin 8) : SylowModel :=
  element (![12, 16, 32, 64, 128, 256, 512, 2048] i)
/-- Explicit square expressions for the eight kernel generators. -/
private def squareWord (i : Fin 8) : List (Fin 8) :=
  ![[6, 7, 2], [3, 5, 7], [0], [0, 1, 2], [1, 3, 4], [3], [1], [5]] i
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem squareWord_check : ∀ i : Fin 8,
    kernelGenerator i = ((squareWord i).map (fun j => seed j ^ 2)).prod := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem kernelGenerator_eq (i : Fin 8) : kernelGenerator i =
    ![root 2 * root 3, root 4, root 5, root 6, root 7, root 8, root 9,
      (SemidirectProduct.inr (FiveFour.generator 4) : SylowModel) ^ 2] i := by
  exact (by decide +kernel : ∀ i : Fin 8, kernelGenerator i =
    ![root 2 * root 3, root 4, root 5, root 6, root 7, root 8, root 9,
      (SemidirectProduct.inr (FiveFour.generator 4) : SylowModel) ^ 2] i) i
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem kernel_mem_of_generators (H : Subgroup SylowModel)
    (hH : ∀ i, kernelGenerator i ∈ H) (x : SylowModel)
    (hx : x.left.b0 = 0) (hc : firstParabolicCoordinates x = 0) : x ∈ H := by
  have hb : x.left.b1 = 0 := congrFun hc 1
  have hp : x.left.b2 + x.left.b3 = 0 := congrFun hc 2
  have h23 : x.left.b3 = x.left.b2 :=
    (by decide : ∀ u v : ZMod 2, u + v = 0 → v = u) _ _ hp
  have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form x.left)
  simp only [map_mul, map_pow, hx, hb, ZMod.val_zero, pow_zero, one_mul, h23] at hn
  have hp23 : (root 2 * root 3) ^ x.left.b2.val =
      root 2 ^ x.left.b2.val * root 3 ^ x.left.b2.val :=
    (by decide +kernel : ∀ z : ZMod 2,
      (root 2 * root 3) ^ z.val = root 2 ^ z.val * root 3 ^ z.val) _
  have hright : ((SemidirectProduct.inr (FiveFour.generator 4) : SylowModel) ^ 2) ^
      (x.right.toAdd.val / 2) = SemidirectProduct.inr x.right := by
    have hparity : parity x.right = 1 := congrArg Multiplicative.ofAdd (congrFun hc 0)
    exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
      ((SemidirectProduct.inr (FiveFour.generator 4) : SylowModel) ^ 2) ^ (t.toAdd.val / 2) =
        SemidirectProduct.inr t) x.right hparity
  have hroots : root 2 * root 3 ∈ H ∧ root 4 ∈ H ∧ root 5 ∈ H ∧ root 6 ∈ H ∧
      root 7 ∈ H ∧ root 8 ∈ H ∧ root 9 ∈ H ∧
      (SemidirectProduct.inr (FiveFour.generator 4) : SylowModel) ^ 2 ∈ H := by
    have hg (i : Fin 8) := hH i
    simp only [kernelGenerator_eq] at hg
    exact ⟨hg 0, hg 1, hg 2, hg 3, hg 4, hg 5, hg 6, hg 7⟩
  rcases hroots with ⟨h0, h4, h5, h6, h7, h8, h9, ht⟩
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply H.mul_mem
  · rw [← hn]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (hp23 ▸ H.pow_mem h0 _) (H.pow_mem h4 _)) (H.pow_mem h5 _))
        (H.pow_mem h6 _)) (H.pow_mem h7 _)) (H.pow_mem h8 _)) (H.pow_mem h9 _)
  · rw [← hright]
    exact H.pow_mem ht _
/-- The kernel is exactly the subgroup generated by all squares in the first parabolic core. -/
public theorem firstParabolicQuotient_ker_eq_squares : firstParabolicQuotient.ker =
    Subgroup.closure (Set.range (fun x : firstParabolicCore => x ^ 2)) := by
  let K := Subgroup.closure (Set.range (fun x : firstParabolicCore => x ^ 2))
  have hs (x : firstParabolicCore) : x ^ 2 ∈ K := Subgroup.subset_closure ⟨x, rfl⟩
  apply le_antisymm
  · intro x hx
    have hcoords : firstParabolicCoordinates (x : SylowModel) = 0 :=
      congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hx)
    let g (i : Fin 8) : firstParabolicCore :=
      ((squareWord i).map (fun j => squareSeed j ^ 2)).prod
    have hg (i : Fin 8) : g i ∈ K := by
      apply K.list_prod_mem
      intro y hy
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
      exact hs _
    have hval (i : Fin 8) : (g i : SylowModel) = kernelGenerator i := by
      simpa only [g, Subgroup.val_list_prod, List.map_map, Function.comp_def,
        Subgroup.coe_pow, squareSeed] using (squareWord_check i).symm
    have hm : (x : SylowModel) ∈ K.map firstParabolicCore.subtype := by
      apply kernel_mem_of_generators (K.map firstParabolicCore.subtype) (fun i => ⟨g i, hg i, hval i⟩) _
        ((mem_firstParabolicCore_iff _).mp x.property) hcoords
    obtain ⟨y, hy, he⟩ := hm
    exact (show y = x from Subtype.ext he) ▸ hy
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨x, rfl⟩
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, pow_two]
    apply Multiplicative.toAdd.injective
    change (firstParabolicQuotient x).toAdd + (firstParabolicQuotient x).toAdd = 0
    funext i
    exact (by decide : ∀ z : ZMod 2, z + z = 0) _
/-- Every automorphism of the first parabolic core preserves the quotient kernel. -/
public theorem firstParabolicQuotient_ker_characteristic : firstParabolicQuotient.ker.Characteristic := by
  rw [firstParabolicQuotient_ker_eq_squares]
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro f
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨x, rfl⟩
  change f (x ^ 2) ∈ Subgroup.closure (Set.range (fun x : firstParabolicCore => x ^ 2))
  rw [map_pow]
  exact Subgroup.subset_closure ⟨f x, rfl⟩

/-- The distinguished nonzero vector, corresponding to roots 5 and 6. -/
@[expose] public def firstParabolicDistinguished : Fin 3 → ZMod 2 := ![0, 0, 1]
/-- The eight free binary parameters in the distinguished fiber. -/
private def distinguishedElement (c e f g h i j : ZMod 2) (t : Fin 2) : SylowModel :=
  ⟨⟨0, 0, c, 1 + c, e, f, g, h, i, j⟩, Multiplicative.ofAdd ((2 * t.val : ℕ) : ZMod 4)⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem distinguished_check_reduced : ∀ (c e f g h i j : ZMod 2) (t : Fin 2),
    (distinguishedElement c e f g h i j t) ^ 2 ≠ 1 ∧
    (distinguishedElement c e f g h i j t) ^ 4 = 1 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem distinguished_check (x : SylowModel)
    (hx : x.left.b0 = 0) (hc : firstParabolicCoordinates x = firstParabolicDistinguished) :
    x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
  have h1 : x.left.b1 = 0 := congrFun hc 1
  have h23 : x.left.b2 + x.left.b3 = 1 := congrFun hc 2
  have h3 : x.left.b3 = 1 + x.left.b2 :=
    (by decide : ∀ u v : ZMod 2, u + v = 1 → v = 1 + u) _ _ h23
  have ht : parity x.right = 1 := congrArg Multiplicative.ofAdd (congrFun hc 0)
  obtain ⟨t, ht⟩ := (by decide +kernel : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
    ∃ j : Fin 2, t = Multiplicative.ofAdd ((2 * j.val : ℕ) : ZMod 4)) x.right ht
  have he : x = distinguishedElement x.left.b2 x.left.b4 x.left.b5 x.left.b6
      x.left.b7 x.left.b8 x.left.b9 t := by
    apply SemidirectProduct.ext
    · exact Core.ext hx h1 rfl h3 rfl rfl rfl rfl rfl rfl
    · exact ht
  rw [he]
  exact distinguished_check_reduced _ _ _ _ _ _ _ _
private def counterexample (i : Fin 7) : SylowModel :=
  element (![0, 2050, 2054, 1056, 1060, 1058, 1030] i)
private theorem counterexample_mem (i : Fin 7) : counterexample i ∈ firstParabolicCore := by
  rw [mem_firstParabolicCore_iff]
  exact (by decide +kernel : ∀ i, (counterexample i).left.b0 = 0) i
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem other_fibers_check : ∀ v : Fin 3 → ZMod 2,
    v ≠ firstParabolicDistinguished → ∃ i : Fin 7,
      firstParabolicCoordinates (counterexample i) = v ∧
      (counterexample i = 1 ∨ counterexample i ^ 4 ≠ 1) := by decide +kernel
/-- Exactly one quotient fiber consists entirely of elements of order four. -/
public theorem firstParabolicQuotient_fiber_order_four_iff (v : Fin 3 → ZMod 2) :
    (∀ x : firstParabolicCore, firstParabolicQuotient x = Multiplicative.ofAdd v →
      orderOf x = 4) ↔ v = firstParabolicDistinguished := by
  constructor
  · intro h
    by_contra hv
    obtain ⟨i, hi, hbad⟩ := other_fibers_check v hv
    let x : firstParabolicCore := ⟨counterexample i, counterexample_mem i⟩
    have ho := h x (congrArg Multiplicative.ofAdd hi)
    have ho' : orderOf (counterexample i) = 4 := by
      simpa only [x, Subgroup.orderOf_mk] using ho
    rcases hbad with hbad | hbad
    · simp [hbad] at ho'
    · apply hbad
      have hp := pow_orderOf_eq_one (counterexample i)
      rwa [ho'] at hp
  · rintro rfl x hx
    have hc := distinguished_check x ((mem_firstParabolicCore_iff _).mp x.property)
      (congrArg Multiplicative.toAdd hx)
    rw [← Subgroup.orderOf_coe]
    exact @orderOf_eq_prime_pow _ _ (x : SylowModel) 1 2 ⟨Nat.prime_two⟩ hc.1 hc.2
end ReeTwo.SylowModel
