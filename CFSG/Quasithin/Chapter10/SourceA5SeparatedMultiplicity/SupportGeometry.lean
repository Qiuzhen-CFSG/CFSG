module

public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.ActorRank
public import Theory.Representation.NormalPairHomogeneous
public import Theory.Representation.NormalPairSupport.Exchange

/-!
# Canonical supports for the marked separated actor

The literal conjugation map of an actor on the normal A₅ square determines
whether its canonical support spaces are preserved or exchanged. In the first
case they are actual subrepresentations, their complementary-sum coordinates
are equivariant, and the factor actions have exactly the two S₅ twists used
by the projected-rank estimate. In the second case one support is carried
into the other and is therefore disjoint from its image.

Source: the separated-support multiplicity step in Aschbacher--Smith D.3.21.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Representation.NormalPairSupport Representation.NormalPairHomogeneous
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
open Theory.GroupTheory.WreathTwoElementaryRank
open Theory.SpecificGroups.Alternating
namespace CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity

variable {A Q V : Type*} [Group A] [Group Q]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Q V) (i : Alt × Alt →* Q) (j : A →* Q)
  (c : A →* MulAut (Alt × Alt))

/-- The wreath coordinates of the actual marked conjugation action. -/
def markedWreath : A →* W Sym :=
  FiveSquareAutomorphisms.wreathEquiv.symm.toMonoidHom.comp c

variable (hc : ∀ a z, j a * i z * (j a)⁻¹ = i (c a z))
include hc

omit ρ in
/-- The base-preserving coordinates retain the literal two factor twists. -/
theorem marked_preserving_covariance (a : A) (ha : (markedWreath c a).right = 1) :
    ∀ x y, j a * i (x,y) * (j a)⁻¹ =
      i (MulAut.conjNormal ((markedWreath c a).left 1) x,
        MulAut.conjNormal ((markedWreath c a).left turn) y) := by
  intro x y
  rw [hc]
  have he := FiveSquareAutomorphisms.wreathEquiv.apply_symm_apply (c a)
  have hh := congrArg (fun f : MulAut (Alt × Alt) => f (x,y)) he
  rw [FiveSquareAutomorphisms.wreathEquiv_apply] at hh
  change FiveSquareAutomorphisms.wreathMap (markedWreath c a) (x,y) = c a (x,y) at hh
  rw [←hh, FiveSquareAutomorphisms.wreathMap_apply, if_pos ha]
  rfl

omit ρ in
/-- A nontrivial top coordinate gives the actual support exchange. -/
theorem marked_exchanging_covariance (a : A) (ha : (markedWreath c a).right ≠ 1) :
    ∀ x y, j a * i (x,y) * (j a)⁻¹ =
      i (MulAut.conjNormal ((markedWreath c a).left 1) y,
        MulAut.conjNormal ((markedWreath c a).left turn) x) := by
  intro x y
  rw [hc]
  have he := FiveSquareAutomorphisms.wreathEquiv.apply_symm_apply (c a)
  have hh := congrArg (fun f : MulAut (Alt × Alt) => f (x,y)) he
  rw [FiveSquareAutomorphisms.wreathEquiv_apply] at hh
  change FiveSquareAutomorphisms.wreathMap (markedWreath c a) (x,y) = c a (x,y) at hh
  rw [←hh, FiveSquareAutomorphisms.wreathMap_apply, if_neg ha]
  rfl

omit hc in
private theorem fixed_image {u v : Alt →* Q} (a : Q) (f : MulAut Alt)
    (h : ∀ s, a * u s * a⁻¹ = v (f s))
    {w : V} (hw : w ∈ invariants (ρ.comp u)) :
    ρ a w ∈ invariants (ρ.comp v) := by
  intro s
  obtain ⟨s,rfl⟩ := f.surjective s
  change ρ (v (f s)) (ρ a w) = ρ a w
  rw [←h]
  have he : ρ (a * u s * a⁻¹) (ρ a w) = ρ a (ρ (u s) w) := by
    simp only [←Module.End.mul_apply, ←map_mul, mul_assoc, inv_mul_cancel, mul_one]
  exact he.trans (congrArg (ρ a) (hw s))

variable (hb : ∀ a, (markedWreath c a).right = 1)
include hb

/-- The canonical first support as a subrepresentation of the actual actor. -/
def firstBlock : Subrepresentation (ρ.comp j) where
  toSubmodule := left ρ i
  apply_mem_toSubmodule a v hv := by
    apply fixed_image ρ (j a) (MulAut.conjNormal ((markedWreath c a).left turn))
      (fun s => ?_) hv
    simpa only [map_one, MonoidHom.comp_apply, MonoidHom.inr_apply] using
      marked_preserving_covariance i j c hc a (hb a) 1 s

/-- The canonical second support as a subrepresentation of the actual actor. -/
def secondBlock : Subrepresentation (ρ.comp j) where
  toSubmodule := right ρ i
  apply_mem_toSubmodule a v hv := by
    apply fixed_image ρ (j a) (MulAut.conjNormal ((markedWreath c a).left 1))
      (fun s => ?_) hv
    simpa only [map_one, MonoidHom.comp_apply, MonoidHom.inl_apply] using
      marked_preserving_covariance i j c hc a (hb a) s 1

/-- The complementary-sum map is equivariant for the original actor. -/
theorem support_coordinates_intertwine (hcomp : IsCompl (left ρ i) (right ρ i))
    (a : A) (v : V) :
    (Submodule.prodEquivOfIsCompl _ _ hcomp).symm ((ρ.comp j) a v) =
      ((firstBlock ρ i j c hc hb).toRepresentation a
        ((Submodule.prodEquivOfIsCompl _ _ hcomp).symm v).1,
       (secondBlock ρ i j c hc hb).toRepresentation a
        ((Submodule.prodEquivOfIsCompl _ _ hcomp).symm v).2) := by
  apply (Submodule.prodEquivOfIsCompl _ _ hcomp).injective
  rw [LinearEquiv.apply_symm_apply]
  change ρ (j a) v = ρ (j a) _ + ρ (j a) _
  rw [←map_add]
  congr 1
  exact ((Submodule.prodEquivOfIsCompl _ _ hcomp).apply_symm_apply v).symm

/-- The first canonical block normalizes its actual A₅ action by the first
permutation coordinate of the original marked conjugation map. -/
theorem firstBlock_covariance (a : A) (g : Alt) (v : left ρ i) :
    (firstBlock ρ i j c hc hb).toRepresentation a (leftAction ρ i g v) =
      leftAction ρ i (MulAut.conjNormal ((markedWreath c a).left 1) g)
        ((firstBlock ρ i j c hc hb).toRepresentation a v) := by
  apply Subtype.ext
  change ρ (j a) (ρ (i (g,1)) v) =
    ρ (i (MulAut.conjNormal ((markedWreath c a).left 1) g,1)) (ρ (j a) v)
  have hh := marked_preserving_covariance i j c hc a (hb a) g 1
  rw [map_one] at hh
  rw [←hh]
  simp only [←Module.End.mul_apply, ←map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- The second support has the second literal permutation twist. -/
theorem secondBlock_covariance (a : A) (g : Alt) (v : right ρ i) :
    (secondBlock ρ i j c hc hb).toRepresentation a (rightAction ρ i g v) =
      rightAction ρ i (MulAut.conjNormal ((markedWreath c a).left turn) g)
        ((secondBlock ρ i j c hc hb).toRepresentation a v) := by
  apply Subtype.ext
  change ρ (j a) (ρ (i (1,g)) v) =
    ρ (i (1,MulAut.conjNormal ((markedWreath c a).left turn) g)) (ρ (j a) v)
  have hh := marked_preserving_covariance i j c hc a (hb a) 1 g
  rw [map_one] at hh
  rw [←hh]
  simp only [←Module.End.mul_apply, ←map_mul, mul_assoc, inv_mul_cancel, mul_one]

omit hb in
/-- A swapping actor moves the canonical first support disjointly. -/
theorem swapping_support_disjoint (hd : Disjoint (left ρ i) (right ρ i))
    (a : A) (ha : (markedWreath c a).right ≠ 1) :
    Disjoint (left ρ i) ((left ρ i).map ((ρ.comp j) a)) := by
  apply hd.mono_right
  rintro _ ⟨v,hv,rfl⟩
  have hm := (exchangeEquiv ρ i (j a)
    (MulAut.conjNormal ((markedWreath c a).left 1))
    (MulAut.conjNormal ((markedWreath c a).left turn))
    (marked_exchanging_covariance i j c hc a ha) ⟨v,hv⟩).property
  rwa [exchangeEquiv_apply] at hm

end CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
