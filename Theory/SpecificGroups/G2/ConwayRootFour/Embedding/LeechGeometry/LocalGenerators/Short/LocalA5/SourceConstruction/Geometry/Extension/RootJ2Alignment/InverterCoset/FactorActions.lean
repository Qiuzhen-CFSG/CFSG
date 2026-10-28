module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.ScalarLinearity
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.LinearCentralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalCoverage

/-!
# The two factor isomorphisms of the placed J₂ centralizer

The literal dihedral centralizer in the permutation J₂ is A₅. Transport its
action along any map into the tetrahedral centralizer satisfying the two
subgroup inclusions. Scalar linearity and the dihedral matrix calculation
factor this action into two two-dimensional blocks. Perfectness makes the
blocks special linear. The placed cubic makes both projections nontrivial;
simplicity and their equal orders make them isomorphisms.

Their comparison is a full diagonal automorphism inverting the marked torus.
No action of the inverter is assumed. `InverterCoset` uses these actual maps
with the ambient properness argument to identify that action.
Source: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284,
with the literal J₂ dihedral centralizer from 47.2 and 47.10.
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.InverterCoset
open Factorization
open Sporadic.LeechRelated.J2.RecognitionGeometry (K X B x X_sup_Y_le_K)

local instance : Group.IsPerfect K := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective
    (f := Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.localEquiv.symm.toMonoidHom)
    Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.localEquiv.symm.surjective

variable {L : LongFrame}
    {f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient}

def rootAction (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hf : ∀ a, f a ∈ centralizerI) : K →* Multiplicative (AddAut (Fin 6 → F)) :=
  (coordinateAction L).comp ((f.comp K.subtype).codRestrict centralizerI (fun a => hf a))

theorem rootAction_spec (hf : ∀ a, f a ∈ centralizerI) (a : K) (v : Fin 6 → F) :
    L.coordinates (rootAction L f hf a v) =
      quotientModTwoRepresentation (f a) (L.coordinates v) :=
  coordinateAction_spec L ⟨f a, hf a⟩ v

theorem rootAction_commutes (M : RootJ2SubgroupMarks L f)
    (hf : ∀ a, f a ∈ centralizerI) (a : K) (d : DihedralGroup 5) (v : Fin 6 → F) :
    rootAction L f hf a (blockAction (slEquiv (dihedralModel d)) v) =
      blockAction (slEquiv (dihedralModel d)) (rootAction L f hf a v) := by
  apply L.coordinates_injective
  rw [rootAction_spec, ← dihedralLift_action, ← dihedralLift_action, rootAction_spec]
  obtain ⟨b, hb, he⟩ := M.dihedral_le ⟨d,rfl⟩
  have hc : dihedralLift L d * f a = f a * dihedralLift L d := by
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg f (a.property b hb)
  have h := congrArg (fun g => quotientModTwoRepresentation g (L.coordinates v)) hc
  simpa only [map_mul, LinearEquiv.mul_apply] using h.symm

theorem rootAction_blockForm (M : RootJ2SubgroupMarks L f)
    (hf : ∀ a, f a ∈ centralizerI) (a : K) (v : Fin 6 → F) :
    rootAction L f hf a v = matrixAction (coefficients (rootAction L f hf a)) v := by
  let A : (Fin 6 → F) →ₗ[F] (Fin 6 → F) :=
    { toFun := rootAction L f hf a
      map_add' := (rootAction L f hf a).toAdd.map_add
      map_smul' := coordinateAction_smul L ⟨f a,hf a⟩ }
  apply linear_centralizer_blockForm A ?_ (rootAction_commutes M hf a) v
  intro w hw
  apply (dihedralLift_fixed_iff L _).mp
  intro d
  rw [dihedralLift_action]
  change L.coordinates (blockAction (slEquiv (dihedralModel d)) (rootAction L f hf a w)) = _
  rw [← rootAction_commutes M hf a]
  have hd := (dihedralLift_fixed_iff L w).mpr hw d
  rw [dihedralLift_action] at hd
  rw [L.coordinates_injective hd]
  rfl

def rootPair (M : RootJ2SubgroupMarks L f) (hf : ∀ a, f a ∈ centralizerI) :
    K →* (SL(2,F) × SL(2,F)) :=
  specialLinearPair (rootAction L f hf) (rootAction_blockForm M hf)

theorem rootPair_action (M : RootJ2SubgroupMarks L f)
    (hf : ∀ a, f a ∈ centralizerI) (a : K) (v : Fin 6 → F) :
    quotientModTwoRepresentation (f a) (L.coordinates v) =
      L.coordinates (pairRepresentation (rootPair M hf a) v) := by
  rw [rootPair, specialLinearPair_action, rootAction_spec]

def placedCubic (M : RootJ2SubgroupMarks L f) (t : Fˣ) : K :=
  ⟨(M.cubic_le ⟨t,rfl⟩).choose,
    X_sup_Y_le_K (Subgroup.mem_sup_left (M.cubic_le ⟨t,rfl⟩).choose_spec.1)⟩

theorem placedCubic_spec (M : RootJ2SubgroupMarks L f) (t : Fˣ) :
    f (placedCubic M t) = longCubic L t := (M.cubic_le ⟨t,rfl⟩).choose_spec.2

theorem placedCubic_mem_X (M : RootJ2SubgroupMarks L f) (t : Fˣ) :
    (placedCubic M t : Sporadic.LeechRelated.J2.Carrier) ∈ X :=
  (M.cubic_le ⟨t,rfl⟩).choose_spec.1

theorem rootPair_cubic (M : RootJ2SubgroupMarks L f)
    (hf : ∀ a, f a ∈ centralizerI) (t : Fˣ) :
    rootPair M hf (placedCubic M t) = (torus t, (torus t)⁻¹) := by
  apply pairRepresentation_injective
  apply LinearEquiv.ext
  intro v
  apply L.coordinates_injective
  rw [← rootPair_action, placedCubic_spec, longCubic_action]

private theorem exists_torus_ne_one : ∃ t : Fˣ, torus t ≠ 1 := by
  have hc : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]
    norm_num
  let : Fintype Fˣ := Fintype.ofFinite _
  let : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card, hc]
    decide)
  obtain ⟨t,ht⟩ := exists_ne (1 : Fˣ)
  refine ⟨t, fun h => ht ?_⟩
  apply Units.ext
  have he := congrArg (fun a : SL(2,F) => a.val 0 0) h
  simpa [torus] using he

private theorem projection_bijective (p : K →* SL(2,F))
    (hp : ∃ a, p a ≠ 1) : Function.Bijective p := by
  let : IsSimpleGroup K :=
    Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.localEquiv.isSimpleGroup
  have hi : Function.Injective p := by
    rcases p.normal_ker.eq_bot_or_eq_top with h | h
    · exact p.ker_eq_bot_iff.mp h
    · obtain ⟨a,ha⟩ := hp
      exact False.elim (ha (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top a)))
  apply (Nat.bijective_iff_injective_and_card p).mpr
  exact ⟨hi, (Nat.card_congr
    Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.localEquiv.toEquiv).trans
    (Nat.card_congr alternatingEquiv.toEquiv).symm⟩

def first (M : RootJ2SubgroupMarks L f) (hf : ∀ a, f a ∈ centralizerI) : K ≃* SL(2,F) :=
  MulEquiv.ofBijective ((MonoidHom.fst _ _).comp (rootPair M hf)) (by
    apply projection_bijective
    obtain ⟨t,ht⟩ := exists_torus_ne_one
    refine ⟨placedCubic M t, ?_⟩
    change (rootPair M hf (placedCubic M t)).1 ≠ 1
    rw [rootPair_cubic]
    exact ht)

def second (M : RootJ2SubgroupMarks L f) (hf : ∀ a, f a ∈ centralizerI) : K ≃* SL(2,F) :=
  MulEquiv.ofBijective ((MonoidHom.snd _ _).comp (rootPair M hf)) (by
    apply projection_bijective
    obtain ⟨t,ht⟩ := exists_torus_ne_one
    refine ⟨placedCubic M t, ?_⟩
    change (rootPair M hf (placedCubic M t)).2 ≠ 1
    rw [rootPair_cubic]
    exact inv_ne_one.mpr ht)

def twist (M : RootJ2SubgroupMarks L f) (hf : ∀ a, f a ∈ centralizerI) : MulAut (SL(2,F)) :=
  (first M hf).symm.trans (second M hf)

theorem twist_torus (M : RootJ2SubgroupMarks L f) (hf : ∀ a, f a ∈ centralizerI) (t : Fˣ) :
    twist M hf (torus t) = (torus t)⁻¹ := by
  have h1 : first M hf (placedCubic M t) = torus t := congrArg Prod.fst (rootPair_cubic M hf t)
  have h2 : second M hf (placedCubic M t) = (torus t)⁻¹ := congrArg Prod.snd (rootPair_cubic M hf t)
  change second M hf ((first M hf).symm (torus t)) = _
  rw [← h1, MulEquiv.symm_apply_apply, h2, h1]

theorem rootPair_eq (M : RootJ2SubgroupMarks L f) (hf : ∀ a, f a ∈ centralizerI) (a : K) :
    rootPair M hf a = (first M hf a, twist M hf (first M hf a)) := by
  apply Prod.ext
  · rfl
  · change second M hf a = second M hf ((first M hf).symm (first M hf a))
    rw [MulEquiv.symm_apply_apply]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.InverterCoset
