module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalActor
public import Theory.GroupAction.RankTwoCosetCover

/-!
# Actual local actors under a coset covering

Pull an actor back within its marked endpoint, where the covering map is
injective. Surjectivity onto the same endpoint gives an actual actor
isomorphism, with the original covering homomorphism on representatives.
Cartan normalization and the natural-kernel coordinates transport through
this restriction. The infinite completion is never identified with the
finite source group, nor is the actor replaced by the full endpoint.

Source application: DGS, *Groups and Graphs* (1985), the universal-tree
setup of Chapter 14, p.208, and reflection selection (14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry.RankTwo NaturalCubic
variable {X Y : Type*} [Group X] [Group Y]
variable {F : Bool → Subgroup X} {E : Bool → Subgroup Y} {f : X →* Y}

/-- Pull a local actor back within its marked endpoint, where the covering
map is injective. This is not its unrestricted preimage in the completion. -/
def coveredActor (A : Subgroup Y) (i : Bool) : Subgroup X := A.comap f ⊓ F i

variable (c : CoverData F E f) (A : Subgroup Y) (i : Bool) (hA : A≤E i)

/-- The pulled-back actor maps isomorphically to the same original actor. -/
def coveredActorEquiv : coveredActor (F := F) (f := f) A i ≃* A := by
  let m : coveredActor (F := F) (f := f) A i →* A :=
    { toFun x := ⟨f x,x.property.1⟩
      map_one' := Subtype.ext f.map_one
      map_mul' x y := Subtype.ext (f.map_mul x y) }
  apply MulEquiv.ofBijective m
  constructor
  · intro x y he
    have he' : f (x:X)=f (y:X) := congrArg Subtype.val he
    have hh := c.injective i (a₁ := ⟨x,x.property.2⟩) (a₂ := ⟨y,y.property.2⟩) he'
    exact Subtype.ext (congrArg (fun z : F i => (z:X)) hh)
  · intro y
    have hy := hA y.property
    rw [←c.map_eq i] at hy
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨⟨x,⟨show f x∈A from hxy ▸ y.property,hx⟩⟩,Subtype.ext hxy⟩

/-- The actor isomorphism is literally the original covering homomorphism. -/
theorem coveredActorEquiv_apply (x : coveredActor (F := F) (f := f) A i) :
    (coveredActorEquiv c A i hA x : Y)=f x := rfl

/-- The ambient Cartan normalizes the pulled-back actor when its image
normalizes the original actor. Only containment in the endpoint is used. -/
theorem coveredActor_normalized (K : Subgroup X) (hK : K≤F i)
    (hn : K.map f≤normalizer (A : Set Y)) :
    K≤normalizer (coveredActor (F := F) (f := f) A i : Set X) := by
  apply le_trans (le_inf ?_ (hK.trans (F i).le_normalizer)) inf_normalizer_le_normalizer_inf
  intro k hk
  exact A.le_normalizer_comap f (hn (mem_map_of_mem f hk))

/-- The same kernel coordinates transport through the restricted original
map; the full endpoint quotient need not have the actor's isomorphism type. -/
def coveredNaturalKernel {k : Type*} [Field k]
    (π : A →* SL(2,k)) (d : NaturalKernel π) :
    NaturalKernel (π.comp (coveredActorEquiv c A i hA).toMonoidHom) :=
  d.ofEquiv (coveredActorEquiv c A i hA)

end Theory.GroupTheory.WeakBNPair.RegularTree
