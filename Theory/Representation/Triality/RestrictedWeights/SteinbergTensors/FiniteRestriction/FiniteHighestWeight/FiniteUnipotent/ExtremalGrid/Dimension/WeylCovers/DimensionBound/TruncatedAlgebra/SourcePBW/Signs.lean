module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates

/-!
# The two root signs in the source PBW argument

The twelve standard coordinate roots exhaust the positive system. Simultaneous
negation gives the opposite system; both are nonopposite and closed under root
sums. Adding a raising simple root to a lowering root, when it is a root,
remains on the lowering side. These facts follow from the actual based D4
root pairing, with the source coordinate order unchanged.

Source: the based-root arithmetic in Steinberg (1963), section 2.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
@[expose] public noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
def turn (S:Geometry K) (negative:Bool) (r:S.roots.Root) : S.roots.Root :=
  if negative then S.roots.neg r else r
@[simp] lemma turn_twice (S:Geometry K) (negative:Bool) (r:S.roots.Root) :
    turn S negative (turn S negative r)=r := by
  cases negative <;> simp [turn,S.realized.neg_neg]
lemma turn_neg (S:Geometry K) (negative:Bool) (r:S.roots.Root) :
    turn S negative (S.roots.neg r)=S.roots.neg (turn S negative r) := by
  cases negative <;> rfl
lemma turn_root (S:Geometry K) (r:S.roots.Root) :
    (typeDRootPairing 2).root (S.rootIndex (S.roots.neg r)) =
      -(typeDRootPairing 2).root (S.rootIndex r) := by
  rw [S.based.2.2.1,RootPairing.root_reflectionPerm,RootPairing.reflection_apply_self]
lemma rootSum_turn (S:Geometry K) (negative:Bool) {a b c:S.roots.Root}
    (h:RootSum S a b c) : RootSum S (turn S negative a) (turn S negative b) (turn S negative c) := by
  cases negative
  · exact h
  · change (typeDRootPairing 2).root (S.rootIndex (S.roots.neg c)) =
      (typeDRootPairing 2).root (S.rootIndex (S.roots.neg a)) +
      (typeDRootPairing 2).root (S.rootIndex (S.roots.neg b))
    rw [turn_root,turn_root,turn_root]
    exact (congrArg Neg.neg h).trans (neg_add _ _)
def sideRoot (S:Geometry K) (negative:Bool) (i:Fin 12) : S.roots.Root :=
  turn S negative (positiveCoordinateRoot S i)
lemma positiveCoordinateRoot_positive (S:Geometry K) (i:Fin 12) :
    positiveCoordinateRoot S i∈S.roots.positive :=
  (S.positive _).mpr (by simpa only [positiveCoordinateRoot,Equiv.apply_symm_apply] using
    Standard.PositiveCoordinates.rootIndex_positive i)
lemma positiveCoordinateRoot_range (S:Geometry K) (r:S.roots.Root) :
    r∈S.roots.positive ↔ ∃i,positiveCoordinateRoot S i=r := by
  constructor
  · intro hr
    have hp : S.rootIndex r ∈ {r | (typeDRootPairing_base 2).IsPos r} := (S.positive r).mp hr
    rw [←Standard.PositiveCoordinates.range_rootIndex] at hp
    obtain ⟨i,hi⟩ := hp
    exact ⟨i,S.rootIndex.injective (by simpa only [positiveCoordinateRoot,Equiv.apply_symm_apply] using hi)⟩
  · rintro ⟨i,rfl⟩
    exact positiveCoordinateRoot_positive S i
lemma positive_ne_negative (S:Geometry K) {a b:S.roots.Root}
    (ha:a∈S.roots.positive) (hb:b∈S.roots.positive) : b≠S.roots.neg a := by
  intro he
  have hpa := (S.positive a).mp ha
  have hpb := (S.positive b).mp hb
  have hn := (typeDRootPairing_base 2).height_reflectionPerm_self (S.rootIndex a)
  have hh : (typeDRootPairing_base 2).height (S.rootIndex b)=
      -(typeDRootPairing_base 2).height (S.rootIndex a) := by
    rw [he,S.based.2.2.1]
    exact hn
  rw [RootPairing.Base.isPos_iff] at hpa hpb
  omega
lemma sideRoot_no_opposite (S:Geometry K) (negative:Bool) (i j:Fin 12) :
    sideRoot S negative j≠S.roots.neg (sideRoot S negative i) := by
  intro h
  have hh:=congrArg (turn S negative) h
  simp only [sideRoot,turn_neg,turn_twice] at hh
  exact positive_ne_negative S (positiveCoordinateRoot_positive S i)
    (positiveCoordinateRoot_positive S j) hh
lemma positive_sum_closed (S:Geometry K) {a b c:S.roots.Root}
    (ha:a∈S.roots.positive) (hb:b∈S.roots.positive) (hs:RootSum S a b c) :
    c∈S.roots.positive :=
  (S.positive c).mpr (((S.positive a).mp ha).add ((S.positive b).mp hb) hs)
lemma sideRoot_sum_closed (S:Geometry K) (negative:Bool) (i j:Fin 12) (c:S.roots.Root)
    (hs:RootSum S (sideRoot S negative i) (sideRoot S negative j) c) :
    ∃l,sideRoot S negative l=c := by
  have ht := rootSum_turn S negative hs
  simp only [sideRoot,turn_twice] at ht
  obtain ⟨l,hl⟩ := (positiveCoordinateRoot_range S _).mp
    (positive_sum_closed S (positiveCoordinateRoot_positive S i) (positiveCoordinateRoot_positive S j) ht)
  refine ⟨l,?_⟩
  have he:=congrArg (turn S negative) hl
  simpa only [sideRoot,turn_twice] using he
lemma simple_positive (S:Geometry K) (i:Fin 4) : (S.simpleRoot i).val∈S.roots.positive := by
  apply (S.positive _).mpr
  apply (typeDRootPairing_base 2).isPos_of_mem_support
  exact (S.based.2.2.2 _).mp (S.simpleRoot i).property
lemma positive_sub_simple (S:Geometry K) (i:Fin 4) {b c:S.roots.Root}
    (hb:b∈S.roots.positive) (hs:RootSum S (S.roots.neg (S.simpleRoot i).val) b c) :
    c∈S.roots.positive := by
  apply (S.positive _).mpr
  apply ((S.positive b).mp hb).sub ((S.based.2.2.2 _).mp (S.simpleRoot i).property)
  change (typeDRootPairing 2).root (S.rootIndex c) =
    (typeDRootPairing 2).root (S.rootIndex b) -
      (typeDRootPairing 2).root (S.rootIndex (S.simpleRoot i).val)
  change (typeDRootPairing 2).root (S.rootIndex c) =
    (typeDRootPairing 2).root (S.rootIndex (S.roots.neg (S.simpleRoot i).val)) +
      (typeDRootPairing 2).root (S.rootIndex b) at hs
  rw [turn_root] at hs
  exact hs.trans ((add_comm _ _).trans (sub_eq_add_neg _ _).symm)
lemma simple_side_mem (S:Geometry K) (negative:Bool) (i:Fin 4) :
    ∃l,sideRoot S negative l=turn S negative (S.simpleRoot i).val := by
  obtain ⟨l,hl⟩ := (positiveCoordinateRoot_range S _).mp (simple_positive S i)
  exact ⟨l,congrArg (turn S negative) hl⟩
lemma raising_sum_closed (S:Geometry K) (negative:Bool) (i:Fin 4) (j:Fin 12) (c:S.roots.Root)
    (hs:RootSum S (S.roots.neg (turn S negative (S.simpleRoot i).val))
      (sideRoot S negative j) c) : ∃l,sideRoot S negative l=c := by
  have ht := rootSum_turn S negative hs
  simp only [turn_neg,sideRoot,turn_twice] at ht
  obtain ⟨l,hl⟩ := (positiveCoordinateRoot_range S _).mp
    (positive_sub_simple S i (positiveCoordinateRoot_positive S j) ht)
  refine ⟨l,?_⟩
  have he:=congrArg (turn S negative) hl
  simpa only [sideRoot,turn_twice] using he
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
