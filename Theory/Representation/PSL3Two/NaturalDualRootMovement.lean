module
public import Theory.Representation.PSL3Two.NaturalDualNormalizer
public import Theory.SpecificGroups.PSL3Two.BorelCenterNormalizer
public import Theory.Representation.BinaryConjugationSection.AutomizerGrowth
public import Theory.Representation.CyclicFixedRank

/-!
# Outer movement on the binary natural–dual root image

On the natural-plus-dual module for SL₃(2), the highest-root involution
I + E₀₂ moves the last natural basis vector to the first. Thus its
commutator image contains a nonzero pure natural vector. Every operator
implementing an outer automorphism exchanges the natural and dual factors,
so it moves this vector.

The literal-section consumer applies this fact to B = P ∩ V in P/Z. When P
centralizes this section image and induces an automizer of order four on V,
the marked outer actor forces the T-automizer to have order at least eight.
The coordinate equivalence and implementing outer operator are explicit:
this result does not infer a natural–dual module from an abstract quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
the nonsolvable endpoint in E.2.17.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace BinaryLinearThree.NaturalDual.RootMovement

/-- The central root involution of the upper triangular Sylow subgroup. -/
def root : Group := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩

/-- The pure natural root vector. -/
def point : Space := (Pi.single 0 1,0)

/-- The displacement of the central transvection on the natural–dual pair. -/
noncomputable def moved : Submodule (ZMod 2) Space := LinearMap.range (action root - LinearMap.id)

theorem root_eq_highestRoot : root = Matrix.PSL3Two.PairedGraphInputs.highestRoot := by
  apply Subtype.ext
  rfl

theorem root_sq : root ^ 2 = 1 := by decide

theorem root_mem_borel : root ∈ Matrix.PSL3Two.borelSL :=
  root_eq_highestRoot ▸ Matrix.PSL3Two.PairedGraphInputs.highestRoot_mem_borel

theorem root_mem_borel_center :
    (⟨root,root_mem_borel⟩ : Matrix.PSL3Two.borelSL) ∈ center Matrix.PSL3Two.borelSL := by
  simpa only [root_eq_highestRoot] using Matrix.PSL3Two.BorelCenterNormalizer.highestRoot_mem_center

/-- The named displacement image is the literal cyclic commutator space. -/
theorem moved_eq_commutator : moved = subspaceCommutator action ⊤ (zpowers root) :=
  (Representation.CyclicFixedRank.commutator_eq_range action root).symm

theorem point_mem_moved : point ∈ moved := by
  refine ⟨(Pi.single 2 1,0),?_⟩
  apply Prod.ext
  · change root.val.mulVec (Pi.single 2 1) - Pi.single 2 1 = Pi.single 0 1
    decide
  · change W.dual root 0 - 0 = 0
    simp only [map_zero,sub_self]

theorem point_ne_zero : point ≠ 0 := by
  intro h
  have he := congrArg (fun v : Space => v.1 0) h
  simp [point] at he

/-- Every outer implementation moves a vector in the marked central-root image. -/
theorem outer_moves_point (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ a v, f (action a v) = action (α a) (f v))
    (hα : α ∉ MulAut.innerSubgroup Group) : f point ≠ point := by
  intro he
  have hz := (outer_swaps α f hf hα).1 (Pi.single 0 1)
  change (f point).1 = 0 at hz
  rw [he] at hz
  have hh := congrFun hz 0
  simp [point] at hh


/-- An outer operator moves the image of the literal marked subgroup. -/
theorem outer_moves_section_image
    {H M : Type*} [_root_.Group H] [AddCommGroup M] [Module (ZMod 2) M]
    {T P Z : Subgroup H} {ρ : Representation (ZMod 2) T M}
    (c : BinaryConjugationSection T P Z ρ) (B : Subgroup H)
    (e : M ≃ₗ[ZMod 2] Space) (hB : (c.imageSpace B).map e.toLinearMap = moved)
    (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ a v, f (action a v) = action (α a) (f v))
    (hα : α ∉ MulAut.innerSubgroup Group) (g : T)
    (hg : ∀ v, e (ρ g v) = f (e v)) :
    ∃ b : P, (b : H) ∈ B ∧ ρ g (c.coordinates b).toAdd ≠ (c.coordinates b).toAdd := by
  have hpoint : point ∈ (c.imageSpace B).map e.toLinearMap := hB.symm ▸ point_mem_moved
  obtain ⟨v,hv,hev⟩ := hpoint
  obtain ⟨b,hb,hbv⟩ := (c.mem_imageSpace_iff B v).mp hv
  refine ⟨b,hb,?_⟩
  intro hfix
  apply outer_moves_point α f hf hα
  have he := congrArg e hfix
  rw [hg,hbv] at he
  exact hev ▸ he

end BinaryLinearThree.NaturalDual.RootMovement




namespace BinaryLinearThree.NaturalDual.RootMovement
variable {H M : Type*} [_root_.Group H] [Finite H] [AddCommGroup M] [Module (ZMod 2) M]
  {T P Z : Subgroup H} {ρ : Representation (ZMod 2) T M}

/-- Literal nonsolvable endpoint: the marked outer actor enlarges the induced
four-group of the core on V to an automizer of order at least eight. -/
theorem eight_le_automizer_of_marked_outer
    (c : BinaryConjugationSection T P Z ρ) (V : Subgroup H)
    (hTV : T ≤ normalizer (V : Set H)) (hc : ⁅P,P⁆ ≤ Z)
    (hfour : Nat.card ((P.subgroupOf T).map
      (V.normalizerMonoidHom.comp (inclusion hTV))) = 4)
    (e : M ≃ₗ[ZMod 2] Space)
    (hB : (c.imageSpace (P ⊓ V)).map e.toLinearMap = moved)
    (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ a v, f (action a v) = action (α a) (f v))
    (hα : α ∉ MulAut.innerSubgroup Group) (g : T)
    (hg : ∀ v, e (ρ g v) = f (e v)) :
    8 ≤ Nat.card (V.normalizerMonoidHom.comp (inclusion hTV)).range := by
  exact c.eight_le_automizer_of_moving_section V (P ⊓ V) hTV inf_le_right
    ((commutator_mono le_rfl inf_le_left).trans hc) hfour g
    (outer_moves_section_image c (P ⊓ V) e hB α f hf hα g hg)

/-- The same actual automizer bound expressed by the literal centralizer indices. -/
theorem eight_le_centralizer_index_of_marked_outer
    (c : BinaryConjugationSection T P Z ρ) (V : Subgroup H)
    (hTV : T ≤ normalizer (V : Set H)) (hc : ⁅P,P⁆ ≤ Z)
    (hfour : (centralizer (V : Set H)).relIndex P = 4)
    (e : M ≃ₗ[ZMod 2] Space)
    (hB : (c.imageSpace (P ⊓ V)).map e.toLinearMap = moved)
    (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ a v, f (action a v) = action (α a) (f v))
    (hα : α ∉ MulAut.innerSubgroup Group) (g : T)
    (hg : ∀ v, e (ρ g v) = f (e v)) :
    8 ≤ (centralizer (V : Set H)).relIndex T := by
  let φ := V.normalizerMonoidHom.comp (inclusion hTV)
  have hker : φ.ker = (centralizer (V : Set H)).subgroupOf T := by
    ext t
    change V.normalizerMonoidHom (inclusion hTV t) = 1 ↔ _
    rw [← MonoidHom.mem_ker,normalizerMonoidHom_ker]
    rfl
  have hcardP : Nat.card ((P.subgroupOf T).map φ) = 4 := by
    rw [←relIndex_ker,hker,subgroupOf,relIndex_comap,
      map_subgroupOf_eq_of_le c.section_le]
    exact hfour
  have hcardT : Nat.card φ.range = (centralizer (V : Set H)).relIndex T := by
    rw [←index_ker,hker]
    rfl
  rw [←hcardT]
  exact eight_le_automizer_of_marked_outer c V hTV hc hcardP e hB α f hf hα g hg

end BinaryLinearThree.NaturalDual.RootMovement
