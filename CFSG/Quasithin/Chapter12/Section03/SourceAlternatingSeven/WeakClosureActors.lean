module
public import Theory.Representation.BinarySevenCode.NormalizerGeometry
public import Theory.Representation.BinarySevenCode.WeakClosureActors
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Setup
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# Actual offender hyperplanes in the A₇ weak-closure argument

Restrict the marked permutation homomorphism to N_{Vᵍ}(V). Pulling back a
hyperplane of its image preserves the relative index, including the full
kernel. The exact core-coordinate equivariance identifies fixed vectors with
centralizing elements of V and displacements with a v a⁻¹ v⁻¹ in V.

The four-group image yields a hyperplane with a strictly larger centralizer
in V. The eight-group image yields a hyperplane-centralized vector whose
commutator has weight two. Together with the involution statement these
supply the finite inputs to the parent's weak-closure argument; no conclusion
about w(G,V), rank-four bound, or ambient simplex centralizer is assumed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 12.3.9--10, printed pp.810--811. The earlier
producer of the genuine LocalAnalysis remains with the source assembly.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open ChapterE BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (S : Setup T L V) (D : S.LocalAnalysis)

/-- The literal image of N_{Vᵍ}(V) in S₇. -/
def actorImage (g : G) : Subgroup (Equiv.Perm (Fin 7)) :=
  ((offenderNormalizer V g).subgroupOf (normalizer (V : Set G))).map D.model.permutation

/-- The preimage of an image subgroup, inside the original offender. -/
def actorLift (g : G) (J : Subgroup (Equiv.Perm (Fin 7))) : Subgroup G :=
  ((J.comap D.model.permutation) ⊓
    (offenderNormalizer V g).subgroupOf (normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype

theorem actorLift_le (g : G) (J : Subgroup (Equiv.Perm (Fin 7))) :
    actorLift S D g J ≤ offenderNormalizer V g := by
  rintro _ ⟨a,ha,rfl⟩
  exact ha.2

theorem actorLift_relIndex (g : G) (J : Subgroup (Equiv.Perm (Fin 7))) :
    (actorLift S D g J).relIndex (offenderNormalizer V g) =
      J.relIndex (actorImage S D g) := by
  have he : ((offenderNormalizer V g).subgroupOf (normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype = offenderNormalizer V g :=
    map_subgroupOf_eq_of_le (show offenderNormalizer V g ≤ normalizer (V : Set G)
      from inf_le_right)
  unfold actorLift
  conv_lhs => arg 2; rw [← he]
  rw [relIndex_map_map_of_injective _ _ Subtype.val_injective,
    inf_relIndex_right, relIndex_comap]
  rfl

theorem actorImage_elementary (g : G) : IsElementaryAbelian 2 (actorImage S D g) := by
  let _ := S.chosen.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 (offenderNormalizer V g) :=
    IsElementaryAbelian.of_le (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left)
  let _ := IsElementaryAbelian.subgroupOf (p := 2)
    (show offenderNormalizer V g ≤ normalizer (V : Set G) from inf_le_right)
  exact IsElementaryAbelian.map _

/-- The image fixed space is the literal centralizer of the offender in V. -/
theorem actorImage_fixed_iff (g : G) (v : V) :
    (D.model.coreCoordinates v).toAdd ∈ Representation.BinaryOffender.fixedSpace
      (BinaryPermutation.coreRepresentation (Fin 7)) (actorImage S D g) ↔
      v.val ∈ centralizer (offenderNormalizer V g : Set G) := by
  constructor
  · intro h a ha
    let n : normalizer (V : Set G) := ⟨a,ha.2⟩
    have hm : D.model.permutation n ∈ actorImage S D g := ⟨n,ha,rfl⟩
    have he := D.model.coreCoordinates_equivariant n v
    have hf0 : BinaryPermutation.SevenParabolic.action (D.model.permutation n)
        (D.model.coreCoordinates v).toAdd = (D.model.coreCoordinates v).toAdd := h ⟨_,hm⟩
    rw [hf0] at he
    have hf := D.model.coreCoordinates.injective (Multiplicative.toAdd.injective he)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hf)
  · intro h a
    obtain ⟨n,hn,heq⟩ := a.property
    change BinaryPermutation.coreRepresentation (Fin 7) a.val
      (D.model.coreCoordinates v).toAdd = _
    rw [← heq]
    have he : V.normalizerMonoidHom n v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (h n hn)
    have hh := D.model.coreCoordinates_equivariant n v
    rw [he] at hh
    exact hh.symm

private theorem lift_fixed (g : G) (J : Subgroup (Equiv.Perm (Fin 7)))
    (w : BinaryPermutation.core (Fin 7))
    (hw : w ∈ Representation.BinaryOffender.fixedSpace
      (BinaryPermutation.coreRepresentation (Fin 7)) J) :
    (D.model.coreCoordinates.symm (Multiplicative.ofAdd w)).val ∈
      centralizer (actorLift S D g J : Set G) := by
  rintro a ⟨n,hn,rfl⟩
  let v := D.model.coreCoordinates.symm (Multiplicative.ofAdd w)
  have he := D.model.coreCoordinates_equivariant n v
  have hv : (D.model.coreCoordinates v).toAdd = w := by simp [v]
  rw [hv] at he
  have hf0 : BinaryPermutation.SevenParabolic.action (D.model.permutation n) w = w :=
    hw ⟨_,hn.1⟩
  rw [hf0] at he
  rw [← hv] at he
  have hf := D.model.coreCoordinates.injective (Multiplicative.toAdd.injective he)
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hf)


/-- The commutator a v a⁻¹ v⁻¹ in the literal subgroup V. -/
def actorDisplacement (g : G) (a : offenderNormalizer V g) (v : V) : V :=
  V.normalizerMonoidHom ⟨a.val,a.property.2⟩ v * v⁻¹

omit [Finite G] in
@[simp] theorem actorDisplacement_val (g : G) (a : offenderNormalizer V g) (v : V) :
    (actorDisplacement g a v).val = a.val * v.val * a.val⁻¹ * v.val⁻¹ := rfl

private theorem displacement_coordinates (g : G) (a : offenderNormalizer V g) (v : V) :
    (D.model.coreCoordinates (actorDisplacement g a v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 7)
        (D.model.permutation ⟨a.val,a.property.2⟩) (D.model.coreCoordinates v).toAdd -
          (D.model.coreCoordinates v).toAdd := by
  simp only [actorDisplacement, map_mul, map_inv, toAdd_mul,
    toAdd_inv, sub_eq_add_neg]
  exact congrArg (fun w => w + -(D.model.coreCoordinates v).toAdd)
    (D.model.coreCoordinates_equivariant ⟨a.val,a.property.2⟩ v)


/-- Every nontrivial image involution has an actual weight-two commutator in V. -/
theorem actor_weight_two (g : G) (a : offenderNormalizer V g)
    (ha : D.model.permutation ⟨a.val,a.property.2⟩ ≠ 1) :
    ∃ v : V, weight (D.model.coordinates (actorDisplacement g a v)).toAdd.val = 2 := by
  let _ := S.chosen.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let n : normalizer (V : Set G) := ⟨a.val,a.property.2⟩
  have hn : n ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian a.val a.property.1)
  have hp : (D.model.permutation n) ^ 2 = 1 := by rw [← map_pow,hn,map_one]
  obtain ⟨w,hw⟩ := WeakClosureActors.involution_displacement (D.model.permutation n) hp ha
  let v := D.model.coreCoordinates.symm (Multiplicative.ofAdd w)
  refine ⟨v,?_⟩
  have he := displacement_coordinates S D g a v
  have hv : (D.model.coreCoordinates v).toAdd = w := by simp [v]
  rw [hv] at he
  change weight (D.model.coreCoordinates (actorDisplacement g a v)).toAdd.val = 2
  rw [he]
  exact hw

/-- A four-group image supplies a hyperplane of the actual offender with a
strictly larger centralizer in V. -/
theorem actor_four_hyperplane (g : G) (hc : Nat.card (actorImage S D g) = 4) :
    ∃ B ≤ offenderNormalizer V g, B.relIndex (offenderNormalizer V g) = 2 ∧
      ∃ v : V, v.val ∈ centralizer (B : Set G) ∧
        v.val ∉ centralizer (offenderNormalizer V g : Set G) := by
  obtain ⟨J,_hJ,hi,w,hw,hn⟩ := WeakClosureActors.four_hyperplane
    (actorImage S D g) (actorImage_elementary S D g) hc
  let v := D.model.coreCoordinates.symm (Multiplicative.ofAdd w)
  refine ⟨actorLift S D g J,actorLift_le S D g J,?_,v,
    lift_fixed S D g J w hw,?_⟩
  · rw [actorLift_relIndex,hi]
  · intro h
    have hh := (actorImage_fixed_iff S D g v).mpr h
    have hv : (D.model.coreCoordinates v).toAdd = w := by simp [v]
    rw [hv] at hh
    exact hn hh

/-- An eight-group image supplies a hyperplane and an actual weight-two
commutator of a vector centralized by that hyperplane. -/
theorem actor_eight_hyperplane (g : G) (hc : Nat.card (actorImage S D g) = 8) :
    ∃ B ≤ offenderNormalizer V g, B.relIndex (offenderNormalizer V g) = 2 ∧
      ∃ a : offenderNormalizer V g, ∃ v : V,
        v.val ∈ centralizer (B : Set G) ∧
        weight (D.model.coordinates (actorDisplacement g a v)).toAdd.val = 2 := by
  obtain ⟨J,_hJ,hi,p,hp,w,hw,hwt⟩ := WeakClosureActors.eight_hyperplane
    (actorImage S D g) (actorImage_elementary S D g) hc
  obtain ⟨n,hn,rfl⟩ := hp
  let a : offenderNormalizer V g := ⟨n.val,hn⟩
  let v := D.model.coreCoordinates.symm (Multiplicative.ofAdd w)
  refine ⟨actorLift S D g J,actorLift_le S D g J,?_,a,v,
    lift_fixed S D g J w hw,?_⟩
  · rw [actorLift_relIndex,hi]
  · have he := displacement_coordinates S D g a v
    have hv : (D.model.coreCoordinates v).toAdd = w := by simp [v]
    rw [hv] at he
    change weight (D.model.coreCoordinates (actorDisplacement g a v)).toAdd.val = 2
    rw [he]
    exact hwt

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
