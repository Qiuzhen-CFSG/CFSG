module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram.Geometry
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
/-!
# The geometric diagram kernel of PSL₃ over a binary field

The nodes of A₂ are the two distinct inner-conjugacy classes of point and
line parabolics. Standard automorphism coverage and the geometric calculations
in `Diagram.Geometry` construct the action of every actual automorphism on
these nodes. Linear-field actors preserve both classes, while the graph coset
exchanges them. The kernel is thus exactly the faithful semilinear image
`ExtensionBorel.linearField`.

Independently of that calculation, `diagramTrivial` is defined by preservation
of both geometric classes. We identify it with the action kernel and with the
linear-field subgroup. In the field of order two, the model's linear-field
collapse then proves that every diagram-trivial actor is inner, and every
intermediate diagram-trivial extension containing Inn equals Inn.

This supplies the linear-three binary clause in Aschbacher–Smith F.1.12,
printed pp.263–264 (PDF pp.274–275 of `refs/quasithin.pdf`). The remaining
local core and quotient-action clauses belong to the source assembly owner.
-/

public section
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions
/-- The nontrivial permutation of the two A₂ nodes. -/
@[expose] def diagramSwap : Equiv.Perm Bool where
  toFun b := !b
  invFun b := !b
  left_inv := Bool.not_not
  right_inv := Bool.not_not

variable (F : Type*) [Field F] [Finite F]

private theorem map_aut_mul {G : Type*} [Group G] (P : Subgroup G) (a b : MulAut G) :
    P.map (a*b).toMonoidHom = (P.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]; rfl

private theorem map_conj_conj {G : Type*} [Group G] (P : Subgroup G) (g h : G) :
    (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      P.map (MulAut.conj (h*g)).toMonoidHom := by
  rw [map_mul, map_aut_mul]

private theorem map_conj_aut {G : Type*} [Group G] (P : Subgroup G)
    (g : G) (a : MulAut G) :
    (P.map (MulAut.conj g).toMonoidHom).map a.toMonoidHom =
      (P.map a.toMonoidHom).map (MulAut.conj (a g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- The image of one standard parabolic lies in the other's actual inner-conjugacy class. -/
@[expose] def MapsParabolicType (a : MulAut PSL(3,F)) (b c : Bool) : Prop :=
  ∃ g : PSL(3,F), (parabolic F b).map a.toMonoidHom =
    (parabolic F c).map (MulAut.conj g).toMonoidHom

/-- Preservation of the line-parabolic conjugacy class. -/
@[expose] def PreservesLineType (a : MulAut PSL(3,F)) : Prop :=
  ∃ g : PSL(3,F), (lineParabolic F).map a.toMonoidHom =
    (lineParabolic F).map (MulAut.conj g).toMonoidHom

omit [Finite F] in
private theorem mapsType_one (b : Bool) : MapsParabolicType F 1 b b := by
  refine ⟨1, ?_⟩
  rw [map_one]

omit [Finite F] in
private theorem mapsType_mul (a b : MulAut PSL(3,F)) (i j k : Bool)
    (ha : MapsParabolicType F a j k) (hb : MapsParabolicType F b i j) :
    MapsParabolicType F (a*b) i k := by
  obtain ⟨g,hg⟩ := hb
  obtain ⟨h,hh⟩ := ha
  refine ⟨a g*h, ?_⟩
  rw [map_aut_mul, hg, map_conj_aut, hh, map_conj_conj]

omit [Finite F] in
private theorem mapsType_inv (a : MulAut PSL(3,F)) (i j : Bool)
    (ha : MapsParabolicType F a i j) : MapsParabolicType F a⁻¹ j i := by
  obtain ⟨g,hg⟩ := ha
  refine ⟨a⁻¹ (g⁻¹), ?_⟩
  apply Subgroup.map_injective (f:=a.toMonoidHom) a.injective
  rw [← map_aut_mul, mul_inv_cancel, map_conj_aut, hg, map_conj_conj]
  simp

/-- Acting trivially on the geometric A₂ types means preserving each actual
inner-conjugacy class of maximal parabolics. -/
def diagramTrivial : Subgroup (MulAut PSL(3,F)) where
  carrier := {a | ∀ b, MapsParabolicType F a b b}
  one_mem' := mapsType_one F
  mul_mem' ha hb b := mapsType_mul F _ _ b b b (ha b) (hb b)
  inv_mem' ha b := mapsType_inv F _ b b (ha b)

omit [Finite F] in
theorem mem_diagramTrivial (a : MulAut PSL(3,F)) :
    a ∈ diagramTrivial F ↔ ∀ b, MapsParabolicType F a b b := Iff.rfl

omit [Finite F] in
theorem mem_diagramTrivial_iff (a : MulAut PSL(3,F)) :
    a ∈ diagramTrivial F ↔ PreservesPointType F a ∧ PreservesLineType F a := by
  constructor
  · intro ha; exact ⟨ha true, ha false⟩
  · rintro ⟨hp,hl⟩ b
    cases b
    · exact hl
    · exact hp

/-- Linear-field actors preserve each geometric diagram type. -/
theorem linearField_mapsParabolicType (a : MulAut PSL(3,F))
    (ha : a ∈ linearField F) (b : Bool) : MapsParabolicType F a b b := by
  obtain ⟨g,σ,rfl⟩ := linearField_factorization F a ha
  unfold MapsParabolicType
  rw [map_aut_mul, field_map_parabolic]
  exact linear_map_parabolic F g b

/-- The standard Borel-preserving graph actor exchanges the types. -/
theorem oppositionGraph_mapsParabolicType (b : Bool) :
    MapsParabolicType F (oppositionGraph F) b (!b) := by
  refine ⟨1, ?_⟩
  rw [oppositionGraph_map_parabolic, map_one]
  exact (Subgroup.map_id _).symm

/-- Pure inverse transpose also exchanges the types, up to inner conjugation. -/
theorem graph_mapsParabolicType (b : Bool) :
    MapsParabolicType F (graph F) b (!b) := by
  have hl : MapsParabolicType F (linearConj F (reversalGL F)⁻¹) (!b) (!b) :=
    linear_map_parabolic F (reversalGL F)⁻¹ (!b)
  have h := mapsType_mul F _ _ b (!b) (!b) hl (oppositionGraph_mapsParabolicType F b)
  simpa only [oppositionGraph, map_inv, inv_mul_cancel_left] using h

/-- Every linear-field translate of inverse transpose exchanges the two types. -/
theorem linearField_graph_mapsParabolicType (a : MulAut PSL(3,F))
    (ha : a ∈ linearField F) (b : Bool) :
    MapsParabolicType F (a * graph F) b (!b) :=
  mapsType_mul F _ _ b (!b) (!b) (linearField_mapsParabolicType F a ha (!b))
    (graph_mapsParabolicType F b)

variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
include hn hF

/-- The two entire conjugacy classes are disjoint, without excluding q = 2. -/
theorem point_line_conjugates_ne (g h : PSL(3,F)) :
    (pointParabolic F).map (MulAut.conj g).toMonoidHom ≠
      (lineParabolic F).map (MulAut.conj h).toMonoidHom := by
  intro he
  have hh := congrArg (fun P : Subgroup PSL(3,F) =>
    P.map (MulAut.conj h⁻¹).toMonoidHom) he
  rw [map_conj_conj, map_conj_conj, inv_mul_cancel, map_one] at hh
  change (pointParabolic F).map (MulAut.conj (h⁻¹*g)).toMonoidHom =
    (lineParabolic F).map (MonoidHom.id _) at hh
  rw [Subgroup.map_id] at hh
  exact pointParabolic_not_conjugate_line F hn hF (h⁻¹*g) hh

private theorem mapsType_unique (a : MulAut PSL(3,F)) (i j k : Bool)
    (hj : MapsParabolicType F a i j) (hk : MapsParabolicType F a i k) : j = k := by
  obtain ⟨g,hg⟩ := hj
  obtain ⟨h,hh⟩ := hk
  have he := hg.symm.trans hh
  cases j <;> cases k
  · rfl
  · exact (point_line_conjugates_ne F hn hF h g he.symm).elim
  · exact (point_line_conjugates_ne F hn hF g h he).elim
  · rfl

private theorem exists_diagramPerm (a : MulAut PSL(3,F)) :
    ∃ π : Equiv.Perm Bool, ∀ b, MapsParabolicType F a b (π b) := by
  have ha : a ∈ standard F := by rw [standard_eq_top_of_two_power_card F hn hF]; trivial
  obtain ⟨g,σ,he | he⟩ := CartanActions.ResidualLinear.standard_opposition_factorization a ha
  · refine ⟨1, fun b => ?_⟩
    rw [he]
    exact linearField_mapsParabolicType F _ ((linearField F).mul_mem
      (Subgroup.mem_sup_left ⟨g,rfl⟩) (Subgroup.mem_sup_right ⟨σ,rfl⟩)) b
  · refine ⟨diagramSwap, fun b => ?_⟩
    rw [he]
    exact mapsType_mul F _ _ b (!b) (!b)
      (linearField_mapsParabolicType F _ ((linearField F).mul_mem
        (Subgroup.mem_sup_left ⟨g,rfl⟩) (Subgroup.mem_sup_right ⟨σ,rfl⟩)) (!b))
      (oppositionGraph_mapsParabolicType F b)

private theorem diagramPerm_unique (a : MulAut PSL(3,F))
    (π ρ : Equiv.Perm Bool) (hπ : ∀ b, MapsParabolicType F a b (π b))
    (hρ : ∀ b, MapsParabolicType F a b (ρ b)) : π = ρ := by
  ext b
  exact mapsType_unique F hn hF a b _ _ (hπ b) (hρ b)

/-- The actual action on the two parabolic conjugacy classes of the A₂ diagram. -/
noncomputable def diagramAction : MulAut PSL(3,F) →* Equiv.Perm Bool where
  toFun a := Classical.choose (exists_diagramPerm F hn hF a)
  map_one' := diagramPerm_unique F hn hF 1 _ 1
    (Classical.choose_spec (exists_diagramPerm F hn hF 1)) (mapsType_one F)
  map_mul' a b := diagramPerm_unique F hn hF (a*b) _ _
    (Classical.choose_spec (exists_diagramPerm F hn hF (a*b))) (fun i =>
      mapsType_mul F a b i _ _
        (Classical.choose_spec (exists_diagramPerm F hn hF a) _)
        (Classical.choose_spec (exists_diagramPerm F hn hF b) i))

/-- The node permutation is realized by the literal image of each parabolic. -/
theorem diagramAction_spec (a : MulAut PSL(3,F)) (b : Bool) :
    MapsParabolicType F a b (diagramAction F hn hF a b) :=
  Classical.choose_spec (exists_diagramPerm F hn hF a) b

/-- The action is characterized exactly by geometric conjugacy, not by a family tag. -/
theorem diagramAction_apply_iff (a : MulAut PSL(3,F)) (b c : Bool) :
    diagramAction F hn hF a b = c ↔ MapsParabolicType F a b c := by
  constructor
  · intro h; rw [← h]; exact diagramAction_spec F hn hF a b
  · intro h; exact mapsType_unique F hn hF a b _ c (diagramAction_spec F hn hF a b) h

/-- The geometric subgroup is the kernel of the actual diagram action. -/
theorem diagramAction_ker : (diagramAction F hn hF).ker = diagramTrivial F := by
  ext a
  change diagramAction F hn hF a = 1 ↔ ∀ b, MapsParabolicType F a b b
  constructor
  · intro ha b
    simpa only [ha, Equiv.Perm.one_apply] using diagramAction_spec F hn hF a b
  · intro ha
    exact diagramPerm_unique F hn hF a _ 1 (diagramAction_spec F hn hF a) ha

theorem diagramAction_linearField (a : MulAut PSL(3,F)) (ha : a ∈ linearField F) :
    diagramAction F hn hF a = 1 :=
  diagramPerm_unique F hn hF a _ 1 (diagramAction_spec F hn hF a)
    (linearField_mapsParabolicType F a ha)

theorem diagramAction_graph : diagramAction F hn hF (graph F) = diagramSwap :=
  diagramPerm_unique F hn hF _ _ _ (diagramAction_spec F hn hF _)
    (graph_mapsParabolicType F)

/-- Preserving either one of the two types excludes the entire graph coset. -/
theorem mapsParabolicType_self_iff_mem_linearField (a : MulAut PSL(3,F)) (b : Bool) :
    MapsParabolicType F a b b ↔ a ∈ linearField F := by
  constructor
  · intro hp
    have ha : a ∈ standard F := by rw [standard_eq_top_of_two_power_card F hn hF]; trivial
    obtain ⟨g,σ,he | he⟩ := CartanActions.ResidualLinear.standard_opposition_factorization a ha
    · rw [he]
      exact (linearField F).mul_mem (Subgroup.mem_sup_left ⟨g,rfl⟩)
        (Subgroup.mem_sup_right ⟨σ,rfl⟩)
    · have hx : MapsParabolicType F a b (!b) := by
        rw [he]
        exact mapsType_mul F _ _ b (!b) (!b)
          (linearField_mapsParabolicType F _ ((linearField F).mul_mem
            (Subgroup.mem_sup_left ⟨g,rfl⟩) (Subgroup.mem_sup_right ⟨σ,rfl⟩)) (!b))
          (oppositionGraph_mapsParabolicType F b)
      have hb := mapsType_unique F hn hF a b b (!b) hp hx
      cases b <;> cases hb
  · intro ha
    exact linearField_mapsParabolicType F a ha b

/-- The intrinsic condition published in Locals is exactly the linear-field condition. -/
theorem preservesPointType_iff_mem_linearField (a : MulAut PSL(3,F)) :
    PreservesPointType F a ↔ a ∈ linearField F :=
  mapsParabolicType_self_iff_mem_linearField F hn hF a true

theorem preservesLineType_iff_mem_linearField (a : MulAut PSL(3,F)) :
    PreservesLineType F a ↔ a ∈ linearField F :=
  mapsParabolicType_self_iff_mem_linearField F hn hF a false

theorem preservesPointType_iff_preservesLineType (a : MulAut PSL(3,F)) :
    PreservesPointType F a ↔ PreservesLineType F a :=
  (preservesPointType_iff_mem_linearField F hn hF a).trans
    (preservesLineType_iff_mem_linearField F hn hF a).symm

/-- Identification of the intrinsically defined diagram kernel with the semilinear image. -/
theorem diagramTrivial_eq_linearField : diagramTrivial F = linearField F := by
  apply le_antisymm
  · intro a ha
    exact (preservesPointType_iff_mem_linearField F hn hF a).mp (ha true)
  · intro a ha
    exact linearField_mapsParabolicType F a ha

theorem diagramAction_ker_eq_linearField :
    (diagramAction F hn hF).ker = linearField F := by
  rw [diagramAction_ker, diagramTrivial_eq_linearField F hn hF]

section Binary
omit hn hF

/-- For q = 2 the geometrically defined diagram kernel consists exactly of inner actors. -/
theorem diagramTrivial_eq_inner_of_card_two (hcard : Nat.card F = 2) :
    diagramTrivial F = MulAut.innerSubgroup PSL(3,F) := by
  rw [diagramTrivial_eq_linearField F (n:=1) (by decide) (by simpa using hcard),
    linearField_eq_inner_of_card_two F hcard]

theorem preservesPointType_iff_inner_of_card_two (hcard : Nat.card F = 2)
    (a : MulAut PSL(3,F)) :
    PreservesPointType F a ↔ a ∈ MulAut.innerSubgroup PSL(3,F) := by
  rw [preservesPointType_iff_mem_linearField F (n:=1) (by decide) (by simpa using hcard),
    linearField_eq_inner_of_card_two F hcard]

/-- An actual diagram-trivial automorphism of the binary group has an inner implementer. -/
theorem diagramTrivial_is_inner_of_card_two (hcard : Nat.card F = 2)
    (a : MulAut PSL(3,F)) (ha : a ∈ diagramTrivial F) :
    ∃ g : PSL(3,F), a = MulAut.conj g := by
  rw [diagramTrivial_eq_inner_of_card_two F hcard] at ha
  obtain ⟨g,hg⟩ := ha
  exact ⟨g,hg.symm⟩

/-- F.1.12's binary extension application, with the geometric diagram hypothesis. -/
theorem diagramTrivial_extension_eq_inner_of_card_two (hcard : Nat.card F = 2)
    (E : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)
    (hE : E ≤ diagramTrivial F) : E = MulAut.innerSubgroup PSL(3,F) :=
  le_antisymm (hE.trans_eq (diagramTrivial_eq_inner_of_card_two F hcard)) hinner

/-- The same binary application using the intrinsic condition published in Locals. -/
theorem pointType_extension_eq_inner_of_card_two (hcard : Nat.card F = 2)
    (E : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)
    (hE : ∀ a ∈ E, PreservesPointType F a) : E = MulAut.innerSubgroup PSL(3,F) := by
  apply le_antisymm _ hinner
  intro a ha
  exact (preservesPointType_iff_inner_of_card_two F hcard a).mp (hE a ha)

end Binary
end Matrix.PSL3.LinearThree.OuterExtensions
