module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Model
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer
public import Theory.Alternating.Aut
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import Theory.Quasithin.Rank
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The faithful action on the actual orbit quotient

Conjugation descends through the specified two-core quotient. The critical
plane is not fixed by the component, so simplicity and the trivial A6
centralizer make the resulting S6 representation faithful. Whole component
movement and the original quotient coordinates are retained.

Source: MS93 (3.6), symplectic paragraph, printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
variable {M : Type*} [Group M] [Finite M] {K R : Subgroup M} {geo : Geometry R}
  (o : PairedOrbit K R geo)
namespace PermutationModel
variable {o} (s : PermutationModel o)

abbrev actor : Subgroup (Equiv.Perm (Fin 6)) :=
  (o.opposite.comap (embedM R)).map s.projection

abbrev topProjection : (⊤ : Subgroup M) →* Equiv.Perm (Fin 6) :=
  s.projection.comp (⊤ : Subgroup M).subtype

omit [Finite M] in
theorem topProjection_onto : Function.Surjective s.topProjection := by
  intro g
  obtain ⟨m,hm⟩ := s.onto g
  exact ⟨⟨m,mem_top _⟩,hm⟩

variable [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)]

omit [Finite M] in
theorem kernel_le : s.topProjection.ker ≤ (orbitRepresentation R o.c o.b).ker := by
  intro m hm
  have hmQ : (m : M) ∈ pCore 2 M := s.kernel ▸ hm
  apply ((orbitSection R o.c o.b o.layer_le).action_mem_ker_iff m).mpr
  intro a ha
  exact o.commutator_le_layer (commutator_mem_commutator hmQ ha)

omit [Finite M] in
theorem conjugation_kernel_le : s.topProjection.ker ≤ (orbitConjugation R o.c o.b).ker := by
  intro m hm
  have he : orbitRepresentation R o.c o.b m = 1 := s.kernel_le hm
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f => (f (Additive.ofMul x)).toMul) he

/-- Literal orbit conjugation descended along the specified two-core quotient. -/
def conjugation : Equiv.Perm (Fin 6) →* MulAut (OrbitQuotient R o.c o.b) :=
  s.topProjection.liftOfSurjective s.topProjection_onto
    ⟨orbitConjugation R o.c o.b,s.conjugation_kernel_le⟩

omit [Finite M] in
theorem conjugation_projection (m : (⊤ : Subgroup M)) :
    s.conjugation (s.projection m) = orbitConjugation R o.c o.b m :=
  MonoidHom.liftOfRightInverse_comp_apply s.topProjection
    (Function.surjInv s.topProjection_onto) (Function.rightInverse_surjInv s.topProjection_onto)
    ⟨orbitConjugation R o.c o.b,s.conjugation_kernel_le⟩ m

/-- The binary linear action of the descended conjugation automorphisms. -/
def action : Representation (ZMod 2) (Equiv.Perm (Fin 6))
    (Additive (OrbitQuotient R o.c o.b)) where
  toFun g := { (s.conjugation g).toAdditive.toAddMonoidHom with
    map_smul' := ZMod.map_smul (s.conjugation g).toAdditive.toAddMonoidHom }
  map_one' := by
    ext x
    change s.conjugation 1 x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change s.conjugation (g*h) x.toMul = s.conjugation g (s.conjugation h x.toMul)
    rw [map_mul]
    rfl

omit [Finite M] in
theorem action_projection (m : (⊤ : Subgroup M)) :
    s.action (s.projection m) = orbitRepresentation R o.c o.b m := by
  ext x
  change s.conjugation (s.projection m) x.toMul = orbitConjugation R o.c o.b m x.toMul
  rw [s.conjugation_projection]

omit [Finite M] in
theorem action_comp : s.action.comp s.topProjection = orbitRepresentation R o.c o.b :=
  MonoidHom.ext s.action_projection

omit [Finite M] [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem component_map : (K.subgroupOf ⊤).map s.topProjection = alternatingGroup (Fin 6) := by
  rw [show s.topProjection = s.projection.comp (⊤ : Subgroup M).subtype from rfl,
    ← map_map,map_subgroupOf_eq_of_le (show K ≤ ⊤ from le_top),s.component_image]

/-- Whole movement is inherited from the same orbit, not from a marked submodule. -/
theorem action_full_movement : subspaceCommutator s.action ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
  have hh := PairedOrbit.quotient_full_movement o
  rw [← s.action_comp,subspaceCommutator_comp_map,s.component_map] at hh
  exact hh

omit [Finite M] in
/-- The nonfixed critical plane makes the component action nontrivial. -/
theorem action_component_nontrivial : ∃ g : alternatingGroup (Fin 6), s.action g ≠ 1 := by
  by_contra! hn
  apply o.plane_not_fixed
  intro y hy
  apply (mem_orbitFixedKernel_iff K R o.c o.b ⟨y,le_normalClosure hy⟩).mpr
  intro k
  change orbitRepresentation R o.c o.b ⟨k,mem_top _⟩ _ = _
  rw [← s.action_projection]
  have hkp : s.projection k ∈ alternatingGroup (Fin 6) :=
    s.component_image ▸ mem_map_of_mem s.projection k.property
  rw [hn ⟨s.projection k,hkp⟩]
  rfl

omit [Finite M] in
/-- The literal quotient representation is faithful. -/
theorem action_injective : Function.Injective s.action := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply s.action.ker_eq_bot_iff.mp
  by_contra hn
  have hle := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot
    (alternatingGroup (Fin 6)) (Group.IsPerfect.not_isMulCommutative _)
    (GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)) s.action.ker hn
  obtain ⟨g,hg⟩ := s.action_component_nontrivial
  exact hg (hle g.property)

/-- The descended action retains the original quotient coordinates. -/
def sectionData : BinaryConjugationSection ⊤ (criticalOrbitNative R o.c o.b)
    (orbitLayer R) (s.action.comp s.topProjection) := by
  rw [s.action_comp]
  exact orbitSection R o.c o.b o.layer_le

include s in
omit [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
/-- SQTK is inherited by the literal alternating section of M/O₂(M). -/
theorem alternating_sqtk (hsq : IsSQTK KnownSimple.IsKnownSimple M) :
    IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)) := by
  have hquot : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 M) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let e : M ⧸ pCore 2 M ≃* Equiv.Perm (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq s.kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective s.projection s.onto)
  exact (IsSQTK.knownSimple_of_equiv e hquot).subgroup (alternatingGroup (Fin 6))



end PermutationModel
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
