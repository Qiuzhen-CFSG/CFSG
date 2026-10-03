module

public import Theory.SpecificGroups.ReeTwo.Action
public import Theory.SpecificGroups.ReeTwo.SourceComparison
public import Mathlib.GroupTheory.Sylow

/-!
# The Ree two central-involution centralizer model

The model is the semidirect product of the ten-root core by its specified
faithful `C₅ : C₄` action. Its order is 20480 and its Sylow two-subgroups
have order 4096. The maps into arbitrary groups retain the core roots,
root 1 and the Weyl involution, giving a presentation/recognition interface.

Source: K. Shinoda, *A characterization of odd order extensions of the Ree
groups ²F₄(q)* (1975), pp. 81–83, (2.3) and (3.2). This construction uses
the remaining relations to resolve the inconsistent extra root-11 factor
in the printed root-2/root-3 relation at q = 2. The comparison below is
an equality of specified root words, not an identification by group order.
Identification with a centralizer in an independently constructed ambient
Ree group requires supplying the generators and relations to `lift`.
-/

@[expose] public section
namespace ReeTwo

abbrev Centralizer := Core ⋊[Core.complement.subtype] Core.complement

namespace Centralizer

/-- Explicit multiplication, using the verified polynomial core multiplication. -/
theorem mul_coordinates (g h : Centralizer) :
    g * h = ⟨g.left * (g.right : MulAut Core) h.left, g.right * h.right⟩ := rfl

instance : Finite Centralizer :=
  Finite.of_equiv (Core × Core.complement) SemidirectProduct.equivProd.symm

theorem card : Nat.card Centralizer = 20480 := by
  rw [SemidirectProduct.card, Core.card, Core.complement_card]

theorem sylow_card (P : Sylow 2 Centralizer) : Nat.card P = 4096 := by
  rw [Sylow.card_eq_multiplicity, card]
  rw [show 20480 = 2 ^ 12 * 5 from rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_pow]
  norm_num [Nat.Prime.factorization (by decide : Nat.Prime 2),
    Nat.Prime.factorization (by decide : Nat.Prime 5)]

/-- The embedded ten-root core. -/
def core : Subgroup Centralizer := SemidirectProduct.inl.range

theorem core_card : Nat.card core = 1024 := by
  exact (Nat.card_congr
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective
      (φ := Core.complement.subtype))).toEquiv.symm).trans Core.card

instance : core.Normal := by
  unfold core
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

def root (i : CoreRoot) : Centralizer := SemidirectProduct.inl (Core.root i)

@[simp] theorem inl_rootWord (w : List CoreRoot) :
    (SemidirectProduct.inl (rootWord Core.root w) : Centralizer) = rootWord root w :=
  map_rootWord _ _ _

/-- Root 1 projects to the inverse automorphism: the source uses right conjugation. -/
def rootOne : Centralizer := SemidirectProduct.inr Core.complementA⁻¹

def rootTwo : Centralizer := rootOne ^ 2

def weyl : Centralizer := SemidirectProduct.inr Core.complementR

theorem root_injective : Function.Injective root := by
  intro i j h
  have he := SemidirectProduct.inl_injective h
  have hi : Function.Injective Core.root := by decide +kernel
  exact hi he

theorem root_ne_one (i : CoreRoot) : root i ≠ 1 := by
  intro h
  have he : Core.root i = 1 := SemidirectProduct.inl_injective (by simpa [root] using h)
  exact (by decide +kernel : ∀ i : CoreRoot, Core.root i ≠ 1) i he

theorem core_relations : CoreRelations root where
  square i := by
    change SemidirectProduct.inl (Core.root i) * SemidirectProduct.inl (Core.root i) = _
    simpa only [map_mul, inl_rootWord] using
      congrArg (SemidirectProduct.inl (φ := Core.complement.subtype))
        (Core.relations.square i)
  commutator i j hij := by
    change rightComm (SemidirectProduct.inl (Core.root i))
      (SemidirectProduct.inl (Core.root j)) = _
    simpa only [map_rightComm, inl_rootWord] using
      congrArg (SemidirectProduct.inl (φ := Core.complement.subtype))
        (Core.relations.commutator i j hij)

theorem root_one_relations : RootOneRelations rootOne root := by
  intro i
  have h := Core.rightConj_root_one (Core.root i)
  rw [Core.a_root] at h
  change MulAut.conj rootOne⁻¹ (root i) = _ at h
  rw [map_mul (SemidirectProduct.inl (φ := Core.complement.subtype)),
    map_inv (SemidirectProduct.inl (φ := Core.complement.subtype)), inl_rootWord] at h
  change MulAut.conj rootOne⁻¹ (root i) = root i *
    (rootWord root (actionCorrection i))⁻¹ at h
  have hi := congrArg Inv.inv h
  simpa [rightComm, MulAut.conj_apply, mul_assoc] using
    congrArg (fun t => t * root i) hi

theorem weyl_root (i : CoreRoot) :
    weyl * root i * weyl⁻¹ = root (weylRoot i) := by
  simpa [weyl, root, Core.complementR] using
    (SemidirectProduct.inl_aut (φ := Core.complement.subtype)
      Core.complementR (Core.root i)).symm

theorem root_one_four : rootOne ^ 4 = 1 := by
  have h : Core.complementA ^ 4 = 1 := Subtype.ext Core.a_four
  simp only [rootOne, ← map_pow, inv_pow, h, inv_one, map_one]

theorem root_two_square : rootTwo * rootTwo = 1 := by
  calc
    rootTwo * rootTwo = rootOne ^ 4 := by unfold rootTwo; group
    _ = 1 := root_one_four

theorem weyl_square : weyl ^ 2 = 1 := by
  have h : Core.complementR ^ 2 = 1 := Subtype.ext Core.r_two
  simp only [weyl, ← map_pow, h, map_one]

theorem root_one_order : orderOf rootOne = 4 := by
  rw [rootOne, orderOf_injective _ SemidirectProduct.inr_injective, orderOf_inv,
    ← Subgroup.orderOf_coe]
  exact Core.orderOf_a

theorem weyl_order : orderOf weyl = 2 := by
  rw [weyl, orderOf_injective _ SemidirectProduct.inr_injective,
    ← Subgroup.orderOf_coe]
  exact Core.orderOf_r

theorem root_one_two_commutator : rightComm rootOne rootTwo = 1 := by
  simp [rootTwo, rightComm, pow_two, mul_assoc]

/-- Ordered binary core coordinates and the specified five-by-four complement word. -/
theorem normal_form (g : Centralizer) :
    ∃ v : CoreRoot → ZMod 2, ∃ i : Fin 5, ∃ j : Fin 4,
      g = SemidirectProduct.inl (Core.ofCoords v) *
        ((rootOne⁻¹) ^ 2 * weyl) ^ i.val * (rootOne⁻¹) ^ j.val := by
  obtain ⟨i, j, h⟩ := Core.complement_normal_form g.right
  refine ⟨Core.coords g.left, i, j, ?_⟩
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g, h]
  simp only [Core.ofCoords_coords, map_mul, map_pow, rootOne, weyl,
    ← map_inv, inv_inv, mul_assoc]

/-- The chosen complement generators satisfy the relations used by `lift`. -/
theorem complement_relations :
    ((rootOne⁻¹) ^ 2 * weyl) ^ 5 = 1 ∧
    (rootOne⁻¹) ^ 4 = 1 ∧
    rootOne⁻¹ * ((rootOne⁻¹) ^ 2 * weyl) * (rootOne⁻¹)⁻¹ =
      ((rootOne⁻¹) ^ 2 * weyl) ^ 2 := by
  let f : FiveFour.Group →* Centralizer :=
    SemidirectProduct.inr.comp Core.complementEquiv.toMonoidHom
  have ha : f FiveFour.a = rootOne⁻¹ := by simp [f, rootOne]
  have hr : f FiveFour.r = weyl := by simp [f, weyl]
  have hc : f FiveFour.c = (rootOne⁻¹) ^ 2 * weyl := by
    rw [FiveFour.c_eq, map_mul, map_pow, ha, hr]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_pow, map_one, hc] using congrArg f FiveFour.c_five
  · simpa only [map_pow, map_one, ha] using congrArg f FiveFour.a_four
  · simpa only [map_mul, map_inv, map_pow, ha, hc] using congrArg f FiveFour.a_conj_c

/-- The q = 2 root-2 corrections; the first entry is forced by the other relations. -/
def rootTwoCorrection (i : CoreRoot) : List CoreRoot :=
  match i.val with
  | 0 => [2, 3, 4, 5, 6]
  | 1 => [4, 8, 9]
  | 5 => [7, 8, 9]
  | 6 => [8]
  | _ => []

theorem root_two_relations (i : CoreRoot) :
    rightComm rootTwo (root i) = rootWord root (rootTwoCorrection i) := by
  rw [rootTwo, rightComm_square, root_one_relations]
  have h := Core.rightConj_root_one (rootWord Core.root (actionCorrection i))
  rw [inl_rootWord] at h
  change MulAut.conj rootOne⁻¹ (rootWord root (actionCorrection i)) = _ at h
  rw [h]
  rw [← inl_rootWord, ← inl_rootWord, ← map_mul]
  congr 1
  exact (by decide +kernel : ∀ i : CoreRoot,
    Core.a (rootWord Core.root (actionCorrection i)) *
      rootWord Core.root (actionCorrection i) = rootWord Core.root (rootTwoCorrection i)) i

theorem forced_root_two_three :
    rightComm rootTwo (root 0) = rootWord root [2, 3, 4, 5, 6] :=
  forced_rootTwoThree rootOne root core_relations root_one_relations

/-- The literal extra factor in the source fails in this noncollapsed model. -/
theorem printed_root_two_three_false :
    rightComm rootTwo (root 0) ≠ rootWord root [2, 3, 4, 5, 6, 8] := by
  intro h
  exact root_ne_one 8
    (printed_rootTwoThree_forces_last_roots_trivial rootOne root
      core_relations root_one_relations h).1

/-- The universal map, stated directly for actual root and Weyl generators.
The complement presentation is imposed on `s⁻¹`, because `s` is root 1. -/
noncomputable def lift {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2) :
    Centralizer →* G :=
  Core.semidirectLift hx hs hw (Core.complementLift s⁻¹ w hc ha h)
    (Core.complementLift_a ..) (Core.complementLift_r ..)

@[simp] theorem lift_root {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2)
    (i : CoreRoot) : lift hx hs hw hc ha h (root i) = x i := by
  simp [lift, root]

@[simp] theorem lift_rootOne {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2) :
    lift hx hs hw hc ha h rootOne = s := by
  exact Core.semidirectLift_root_one ..

@[simp] theorem lift_weyl {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2) :
    lift hx hs hw hc ha h weyl = w := by
  simp [lift, weyl]

theorem hom_ext {G : Type*} [Group G] {f g : Centralizer →* G}
    (hx : ∀ i, f (root i) = g (root i))
    (hs : f rootOne = g rootOne) (hw : f weyl = g weyl) : f = g := by
  apply SemidirectProduct.hom_ext
  · exact Core.hom_ext hx
  · apply Core.complement_hom_ext
    · have hi := congrArg Inv.inv hs
      simpa only [rootOne, map_inv, inv_inv, MonoidHom.comp_apply] using hi
    · exact hw

/-- The last root is the distinguished central involution. -/
theorem root_twelve_order : orderOf (root 9) = 2 := by
  apply orderOf_eq_prime
  · simpa [pow_two, coreSquare] using core_relations.square 9
  · exact root_ne_one 9

theorem root_twelve_central : root 9 ∈ Subgroup.center Centralizer := by
  have he : (MulAut.conj (root 9)).toMonoidHom = MonoidHom.id Centralizer := by
    apply hom_ext
    · intro i
      have h : Commute (Core.root 9) (Core.root i) :=
        (by decide +kernel : ∀ i : CoreRoot,
          Core.root 9 * Core.root i = Core.root i * Core.root 9) i
      have hm : Commute (root 9) (root i) := h.map SemidirectProduct.inl
      exact hm.mul_inv_cancel
    · have h : rightComm rootOne (root 9) = 1 := root_one_relations 9
      have hc : Commute (root 9) rootOne := by
        show root 9 * rootOne = rootOne * root 9
        calc
          root 9 * rootOne = root 9 * rootOne * rightComm rootOne (root 9) := by rw [h, mul_one]
          _ = rootOne * root 9 := by simp [rightComm, mul_assoc]
      exact hc.mul_inv_cancel
    · have h : weyl * root 9 * weyl⁻¹ = root 9 := weyl_root 9
      have hc : Commute (root 9) weyl := (mul_inv_eq_iff_eq_mul.mp h).symm
      exact hc.mul_inv_cancel
  apply Subgroup.mem_center_iff.mpr
  intro g
  have h : root 9 * g * (root 9)⁻¹ = g := DFunLike.congr_fun he g
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- No extra relations are needed to specify a map on the chosen generators. -/
theorem lift_unique {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2)
    (f : Centralizer →* G) (fx : ∀ i, f (root i) = x i)
    (fs : f rootOne = s) (fw : f weyl = w) : f = lift hx hs hw hc ha h := by
  apply hom_ext <;> simp [fx, fs, fw]

end Centralizer
end ReeTwo
