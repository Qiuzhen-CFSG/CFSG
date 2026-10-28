module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Core
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CodeAction

/-!
# Natural modules from the actual Golay coordinate halfspaces

Axis indices `0`, `1`, `2` refer to the first, second, third Parker axes.
The signed label `(x, ε)` denotes the subset of the corresponding axis whose
Golay word takes value `ε` at `x`. Coordinate separation proves that these
48 subsets are distinct. Complementation within the axis changes the sign.

The module is the space of real anti-invariant functions on these labels.
Evaluation at bit one gives the fixed 24-coordinate model and the source's
orthonormal basis. A permutation carrying actual halfspaces to halfspaces
induces the signed action: finiteness supplies bijectivity and relative
complementation supplies compatibility with signs. Faithfulness on signed
points gives the exact halfspace-fixation criterion for its linear kernel.

Source: Aschbacher, *Sporadic Groups*, the construction preceding Lemma 27.4,
printed pp. 146–147 (PDF page 79), and Exercise 4.3. Structural identification
of the kernel in the triality group is a separate theorem.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin.SignedModules.Natural

abbrev Axis := Fin 3
abbrev Label := Omega × ParkerBit

def point : Axis → ParkerLoop → Triple
  | 0 => axis1
  | 1 => axis2
  | 2 => axis3

theorem point_injective (i : Axis) : Function.Injective (point i) := by
  fin_cases i <;> intro a b h
  · exact Option.some.inj (congrArg Prod.fst h)
  · exact Option.some.inj (congrArg (fun t : Triple => t.2.1) h)
  · exact Option.some.inj (congrArg (fun t : Triple => t.2.2) h)

/-- The actual coordinate halfspace on the indicated Parker axis. -/
def halfspace (i : Axis) (l : Label) : Set Triple :=
  point i '' {d : ParkerLoop | d.1.val l.1 = l.2}

@[simp] theorem point_mem_halfspace (i : Axis) (l : Label) (d : ParkerLoop) :
    point i d ∈ halfspace i l ↔ d.1.val l.1 = l.2 := by
  exact (point_injective i).mem_set_image

private theorem bit_cases (b : ParkerBit) : b = 0 ∨ b = 1 := by
  revert b; decide

theorem halfspace_nonempty (i : Axis) (l : Label) : (halfspace i l).Nonempty := by
  rcases bit_cases l.2 with h | h
  · exact ⟨point i loopOne, (point_mem_halfspace _ _ _).2 (by exact h.symm)⟩
  · exact ⟨point i parkerOmega, (point_mem_halfspace _ _ _).2 (by exact h.symm)⟩

/-- Distinct signed labels give distinct subsets of the genuine Parker triples. -/
theorem halfspace_injective (i : Axis) : Function.Injective (halfspace i) := by
  rintro ⟨x, ε⟩ ⟨y, η⟩ h
  have he (d : ParkerLoop) : d.1.val x = ε ↔ d.1.val y = η := by
    simpa only [point_mem_halfspace] using Set.ext_iff.mp h (point i d)
  have hε : ε = η := by
    have hz := he loopOne
    change (0 : ParkerBit) = ε ↔ 0 = η at hz
    rcases bit_cases ε with rfl | rfl <;> rcases bit_cases η with rfl | rfl <;> simp_all
  subst η
  have hxy : x = y := parkerGolay_coordinates_separate x y (by
    intro a
    have ha := he (a, 0)
    rcases bit_cases (a.val x) with hx | hx <;>
      rcases bit_cases (a.val y) with hy | hy <;>
      rcases bit_cases ε with hε | hε <;> simp_all)
  exact Prod.ext hxy rfl

/-- Labels are equivalent to the actual family of halfspaces. -/
def halfspaceEquiv (i : Axis) : Label ≃ Set.range (halfspace i) :=
  Equiv.ofInjective _ (halfspace_injective i)

def signs : SignedSet Label where
  flip :=
    { toFun l := (l.1, l.2 + 1)
      invFun l := (l.1, l.2 + 1)
      left_inv := by rintro ⟨x, ε⟩; simp [add_assoc]
      right_inv := by rintro ⟨x, ε⟩; simp [add_assoc] }
  involutive := by rintro ⟨x, ε⟩; simp [add_assoc]
  fixedPointFree := by rintro ⟨x, ε⟩ h; have := congrArg Prod.snd h; simp at this

@[simp] theorem flip_label (l : Label) : signs.flip l = (l.1, l.2 + 1) := rfl

theorem halfspace_flip (i : Axis) (l : Label) :
    halfspace i (signs.flip l) = Set.range (point i) \ halfspace i l := by
  ext a
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    rw [point_mem_halfspace]
    change d.1.val l.1 = l.2 + 1 at hd
    rw [hd]
    simp
  · rintro ⟨⟨d, rfl⟩, hd⟩
    rw [point_mem_halfspace] at hd ⊢
    change d.1.val l.1 = l.2 + 1
    rcases bit_cases (d.1.val l.1) with h | h <;>
      rcases bit_cases l.2 with hl | hl <;> simp_all

/-- Real anti-invariant functions; the index records the source Parker axis. -/
abbrev Space (_i : Axis) := signs.Space

def L (i : Axis) (ε : ParkerBit) (x : Omega) : Space i := signs.delta (x, ε)

@[simp] theorem L_add_one (i : Axis) (ε : ParkerBit) (x : Omega) :
    L i (ε + 1) x = -L i ε x := signs.delta_flip (x, ε)

/-- Evaluation on the source's positive labels, whose bit is one. -/
def coordinates (i : Axis) : Space i ≃ₗ[ℝ] (Omega → ℝ) where
  toFun v x := v.val (x, 1)
  invFun f := ⟨fun l => if l.2 = 1 then f l.1 else -f l.1, by
    rintro ⟨x, ε⟩
    change (if ε + 1 = 1 then f x else -f x) = -(if ε = 1 then f x else -f x)
    rcases bit_cases ε with rfl | rfl <;> simp⟩
  left_inv v := by
    apply Subtype.ext
    funext ⟨x, ε⟩
    change (if ε = 1 then v.val (x, 1) else -v.val (x, 1)) = v.val (x, ε)
    rcases bit_cases ε with rfl | rfl
    · have h := signs.negative_apply v (x, 1)
      change v.val (x, 1 + 1) = -v.val (x, 1) at h
      simpa using h.symm
    · simp
  right_inv f := by funext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinates_L_one (i : Axis) (x : Omega) :
    coordinates i (L i 1 x) = Pi.single x 1 := by
  funext y
  simp [coordinates, L, signs, Pi.single_apply]

def basis (i : Axis) : Module.Basis Omega ℝ (Space i) :=
  (Pi.basisFun ℝ Omega).map (coordinates i).symm

@[simp] theorem basis_eq_L (i : Axis) (x : Omega) : basis i x = L i 1 x := by
  apply (coordinates i).injective
  simp [basis]

theorem finrank_space (i : Axis) : Module.finrank ℝ (Space i) = 24 := by
  rw [(coordinates i).finrank_eq, Module.finrank_pi]
  decide

def form (i : Axis) : LinearMap.BilinForm ℝ (Space i) := signs.form

theorem form_pos (i : Axis) (v : Space i) (hv : v ≠ 0) : 0 < form i v v :=
  signs.form_pos v hv

theorem form_symmetric (i : Axis) (v w : Space i) : form i v w = form i w v :=
  signs.form_symmetric v w

theorem basis_orthonormal (i : Axis) (x y : Omega) :
    form i (basis i x) (basis i y) = if x = y then 1 else 0 := by
  rw [basis_eq_L, basis_eq_L]
  change signs.form (signs.delta (x, 1)) (signs.delta (y, 1)) = _
  rw [signs.form_delta]
  simp [signs]


/-- A permutation carries the actual source halfspace family into the target family.
Finiteness then gives equality of the families. -/
def Carries (i j : Axis) (g : Equiv.Perm Triple) : Prop :=
  ∀ l, ∃ m, g '' halfspace i l = halfspace j m

def labelMap {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g) (l : Label) : Label :=
  Classical.choose (hg l)

theorem image_halfspace {i j : Axis} (g : Equiv.Perm Triple)
    (hg : Carries i j g) (l : Label) :
    g '' halfspace i l = halfspace j (labelMap g hg l) := Classical.choose_spec (hg l)

theorem labelMap_injective {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g) :
    Function.Injective (labelMap g hg) := by
  intro l m h
  apply halfspace_injective i
  apply g.injective.image_injective
  simp only [image_halfspace g hg, h]

/-- The permutation of labels is recovered from its action on genuine halfspaces. -/
def labelEquiv {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g) : Label ≃ Label :=
  Equiv.ofBijective (labelMap g hg) ⟨labelMap_injective g hg,
    Finite.surjective_of_injective (labelMap_injective g hg)⟩

theorem labelEquiv_of_image {i j : Axis} (g : Equiv.Perm Triple)
    (hg : Carries i j g) (l m : Label) (h : g '' halfspace i l = halfspace j m) :
    labelEquiv g hg l = m :=
  halfspace_injective j ((image_halfspace g hg l).symm.trans h)

private theorem union_halfspace (i : Axis) :
    ⋃ l, halfspace i l = Set.range (point i) := by
  ext a
  constructor
  · intro ha
    obtain ⟨l, d, _, rfl⟩ := Set.mem_iUnion.mp ha
    exact ⟨d, rfl⟩
  · rintro ⟨d, rfl⟩
    apply Set.mem_iUnion.mpr
    exact ⟨(((0, 0), 0), d.1.val ((0, 0), 0)),
      (point_mem_halfspace _ _ _).mpr rfl⟩

theorem image_axis {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g) :
    g '' Set.range (point i) = Set.range (point j) := by
  rw [← union_halfspace i, Set.image_iUnion]
  simp only [image_halfspace g hg]
  change (⋃ l, halfspace j (labelEquiv g hg l)) = _
  rw [(labelEquiv g hg).surjective.iUnion_comp, union_halfspace]

theorem labelEquiv_flip {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g)
    (l : Label) : labelEquiv g hg (signs.flip l) = signs.flip (labelEquiv g hg l) := by
  apply halfspace_injective j
  change halfspace j (labelMap g hg (signs.flip l)) = _
  rw [← image_halfspace, halfspace_flip, Set.image_sdiff g.injective,
    image_axis g hg, image_halfspace, halfspace_flip]
  rfl

/-- Forward transport of signed functions, induced from an ambient triple permutation. -/
def transport {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g) :
    Space i ≃ₗ[ℝ] Space j := signs.transport signs (labelEquiv g hg) (labelEquiv_flip g hg)

@[simp] theorem transport_L {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g)
    (ε : ParkerBit) (x : Omega) :
    transport g hg (L i ε x) = L j (labelEquiv g hg (x, ε)).2
      (labelEquiv g hg (x, ε)).1 := signs.transport_delta signs _ _ (x, ε)

theorem transport_isometry {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g)
    (v w : Space i) : form j (transport g hg v) (transport g hg w) = form i v w :=
  signs.transport_isometry signs _ _ v w

/-- The linear kernel fixes every signed halfspace, including its sign. -/
theorem transport_kernel_iff {i : Axis} (g : Equiv.Perm Triple) (hg : Carries i i g) :
    transport g hg = LinearEquiv.refl ℝ (Space i) ↔
      ∀ l, g '' halfspace i l = halfspace i l := by
  rw [transport, signs.transport_eq_refl_iff]
  constructor
  · intro h l
    have hl := Equiv.congr_fun h l
    simpa only [labelEquiv, Equiv.ofBijective_apply, Equiv.refl_apply] using
      (image_halfspace g hg l).trans (congrArg (halfspace i) hl)
  · intro h
    apply Equiv.ext
    intro l
    exact labelEquiv_of_image g hg l l (h l)

/-- A group action on triples preserving the halfspace family induces its action on labels. -/
def labelRepresentation {G : Type*} [Group G] {i : Axis}
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries i i (ρ g)) :
    G →* Equiv.Perm Label where
  toFun g := labelEquiv (ρ g) (hρ g)
  map_one' := by
    apply Equiv.ext
    intro l
    apply labelEquiv_of_image
    simp
  map_mul' g h := by
    apply Equiv.ext
    intro l
    apply labelEquiv_of_image
    rw [map_mul]
    change (ρ g ∘ ρ h) '' halfspace i l = _
    rw [Set.image_comp, image_halfspace, image_halfspace]
    rfl

def representation {G : Type*} [Group G] {i : Axis}
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries i i (ρ g)) :
    Representation ℝ G (Space i) :=
  signs.representation (labelRepresentation ρ hρ) (fun g => labelEquiv_flip (ρ g) (hρ g))

@[simp] theorem representation_L {G : Type*} [Group G] {i : Axis}
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries i i (ρ g))
    (g : G) (ε : ParkerBit) (x : Omega) :
    representation ρ hρ g (L i ε x) =
      L i (labelEquiv (ρ g) (hρ g) (x, ε)).2 (labelEquiv (ρ g) (hρ g) (x, ε)).1 :=
  transport_L (ρ g) (hρ g) ε x

theorem representation_kernel_iff {G : Type*} [Group G] {i : Axis}
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries i i (ρ g)) (g : G) :
    representation ρ hρ g = 1 ↔ ∀ l, ρ g '' halfspace i l = halfspace i l := by
  exact (signs.representation_kernel_iff (labelRepresentation ρ hρ)
    (fun g => labelEquiv_flip (ρ g) (hρ g)) g).trans
      ((signs.transport_eq_refl_iff _ (labelEquiv_flip (ρ g) (hρ g))).symm.trans
        (transport_kernel_iff (ρ g) (hρ g)))

theorem representation_isometry {G : Type*} [Group G] {i : Axis}
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries i i (ρ g))
    (g : G) (v w : Space i) :
    form i (representation ρ hρ g v) (representation ρ hρ g w) = form i v w :=
  transport_isometry (ρ g) (hρ g) v w

/-- The first and third natural modules, used in the odd second-automorphism transport. -/
abbrev B1_24 := Space 0
abbrev B3_24 := Space 2

@[simp] theorem L_zero (i : Axis) (x : Omega) : L i 0 x = -basis i x := by
  simpa only [basis_eq_L, show (1 : ParkerBit) + 1 = 0 from rfl] using L_add_one i 1 x

theorem transport_monomial {i j : Axis} (g : Equiv.Perm Triple) (hg : Carries i j g)
    (x : Omega) : ∃ y, transport g hg (basis i x) = basis j y ∨
      transport g hg (basis i x) = -basis j y := by
  let l := labelEquiv g hg (x, 1)
  refine ⟨l.1, ?_⟩
  rw [basis_eq_L, transport_L]
  change L j l.2 l.1 = basis j l.1 ∨ L j l.2 l.1 = -basis j l.1
  rcases bit_cases l.2 with h | h
  · right; rw [h, L_zero]
  · left; rw [h, basis_eq_L]

theorem representation_monomial {G : Type*} [Group G] {i : Axis}
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries i i (ρ g)) (g : G) (x : Omega) :
    ∃ y, representation ρ hρ g (basis i x) = basis i y ∨
      representation ρ hρ g (basis i x) = -basis i y :=
  transport_monomial (ρ g) (hρ g) x

end Sporadic.Monster.Construction.TrialitySpin.SignedModules.Natural
