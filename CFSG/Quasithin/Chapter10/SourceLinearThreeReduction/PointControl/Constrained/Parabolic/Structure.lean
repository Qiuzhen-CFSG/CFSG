module
public import Theory.Representation.BinaryFivePointStabilizers
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Centralizer
public import Theory.Representation.BinaryNaturalDual.Transport
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual rank-five and rank-ten plane parabolics

The opposite involution u is a nonzero vector of the literal orbit module VI.
Its stabilizer in the faithful action quotient pulls back exactly to
C_{I C_T(v)}(E). The previously proved two-group kernel therefore identifies
both intrinsic two-core quotients. In dimension five the faithful natural
recognition gives L₄(2); in dimension ten the irreducible exterior recognition
and the actual Sylow-fixed point give S₃ × L₃(2). Both stabilizers are maximal.

This proves the centralizer structure used in the two terminal paragraphs of
Aschbacher--Smith 10.2.9, printed pp.752--753. It does not yet construct the
rank-one subgroups P, Pc and Pf or prove their exchange contradictions.
The same owner, qt-d-10-nona5-point-constrained, retains those obligations and
construction of LinearFiveData from the original constrained context.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open BinaryNaturalDual.VectorStabilizers
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

abbrev planeCentralizer (T : Sylow 2 G) (t v : G) (I : Subgroup G) : Subgroup G :=
  pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)

def LinearFiveData.quotientActor {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.normal
    ActionQuotient (internalModule D v I) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := by
  let := c.reduced.normal
  exact ((Subgroup.topEquiv).symm.trans
    (MulEquiv.subgroupCongr m.actor_eq_top.symm)).trans m.actor

theorem LinearFiveData.module_irreducible {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    IsIrreducible (action (internalModule D v I)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  have hs : Function.Surjective A.subtype := by
    intro x
    exact ⟨⟨x, by change x ∈ (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I)); rw [m.actor_eq_top]; trivial⟩,rfl⟩
  exact (irreducible_comp_surjective_iff A.subtype hs _).mp m.irreducible

/-- The point is the original u, regarded as a vector of the literal VI. -/
def LinearFiveData.pointVector {c : Context D t v I} (m : LinearFiveData c) :
    Additive (internalModule D v I) :=
  Additive.ofMul ⟨⟨oppositePoint t v,c.orbit_le_join m.opposite_mem_orbit⟩,m.opposite_mem_orbit⟩

theorem LinearFiveData.pointVector_ne_zero {c : Context D t v I} (m : LinearFiveData c) :
    m.pointVector ≠ 0 := by
  intro he
  have hh := congrArg (fun x : Additive (internalModule D v I) =>
    (((x.toMul : internalModule D v I) : pointJoin T v I) : G)) he
  exact c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp hh)

theorem LinearFiveData.pointVector_fixed_iff {c : Context D t v I} (m : LinearFiveData c)
    (h : pointJoin T v I) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    action (internalModule D v I) (actionMk (internalModule D v I) h) m.pointVector =
      m.pointVector ↔ (h : G) ∈ planeCentralizer T t v I := by
  let := c.reduced.normal
  let := c.reduced.elementary
  rw [planeCentralizer,c.join_plane_centralizer]
  constructor
  · intro he
    refine ⟨h.property,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg (fun x : Additive (internalModule D v I) =>
      (((x.toMul : internalModule D v I) : pointJoin T v I) : G)) he
    have ha := congrArg (pointJoin T v I).subtype
      (action_apply (internalModule D v I) h m.pointVector)
    change _ = (h : G) * oppositePoint t v * (h : G)⁻¹ at ha
    change _ = oppositePoint t v at hh
    exact mul_inv_eq_iff_eq_mul.mp (ha.symm.trans hh)
  · intro hh
    have hc := mem_centralizer_singleton_iff.mp hh.2
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have ha := congrArg (pointJoin T v I).subtype
      (action_apply (internalModule D v I) h m.pointVector)
    change _ = (h : G) * oppositePoint t v * (h : G)⁻¹ at ha
    exact ha.trans (mul_inv_eq_iff_eq_mul.mpr hc)

/-- Removing the literal action kernel preserves the intrinsic two-core quotient
of the original plane centralizer. -/
def LinearFiveData.planeQuotientEquiv {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    (planeCentralizer T t v I ⧸ pCore 2 (planeCentralizer T t v I)) ≃*
      (representationStabilizer (action (internalModule D v I)) m.pointVector ⧸
        pCore 2 (representationStabilizer (action (internalModule D v I)) m.pointVector)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  let q := actionMk (internalModule D v I)
  let B := representationStabilizer (action (internalModule D v I)) m.pointVector
  let i : C →* H := inclusion inf_le_left
  let f : C →* B := (q.comp i).codRestrict B (fun x =>
    (m.pointVector_fixed_iff (i x)).mpr x.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (centralizer
      (internalModule D v I : Set H)) b.val
    have hc : (h : G) ∈ C := (m.pointVector_fixed_iff h).mp (by
      change action (internalModule D v I) (q h) m.pointVector = m.pointVector
      rw [show q h = b.val from hh]
      exact b.property)
    exact ⟨⟨h,hc⟩,Subtype.ext hh⟩
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* q.ker := {
      toFun := fun x => ⟨i x.val, congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact m.action_kernel_two.of_injective j (by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : q.ker => ((x : H) : G)) he)
  exact f.pCoreQuotientEquiv hf hk

/-- The prescribed point Sylow has a full Sylow image fixing the actual u. -/
theorem LinearFiveData.pointVector_sylow {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    ∃ S : Sylow 2 (ActionQuotient (internalModule D v I)),
      (S : Subgroup _) ≤ representationStabilizer (action (internalModule D v I)) m.pointVector := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let H := pointJoin T v I
  let q := actionMk (internalModule D v I)
  obtain ⟨S,hS⟩ := c.join_sylow
  refine ⟨S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _),?_⟩
  rintro _ ⟨s,hs,rfl⟩
  apply (m.pointVector_fixed_iff s).mpr
  refine ⟨s.property,m.pointSylow_centralizes_plane ?_⟩
  exact hS ▸ mem_map_of_mem H.subtype hs

private theorem LinearFiveData.plane_maximal_of_stabilizer {c : Context D t v I}
    (m : LinearFiveData c)
    (hm : letI := c.reduced.normal; letI := c.reduced.elementary
      IsCoatom (representationStabilizer (action (internalModule D v I)) m.pointVector)) :
    IsCoatom ((planeCentralizer T t v I).subgroupOf (pointJoin T v I)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  have he : (planeCentralizer T t v I).subgroupOf (pointJoin T v I) =
      (representationStabilizer (action (internalModule D v I)) m.pointVector).comap
        (actionMk (internalModule D v I)) := by
    ext h
    exact (m.pointVector_fixed_iff h).symm
  rw [he]
  exact isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hm

/-- Source 10.2.9's rank-five centralizer is a maximal parabolic in the actual
point join, with intrinsic quotient L₄(2). -/
theorem LinearFiveData.plane_structure_five {c : Context D t v I} (m : LinearFiveData c)
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 5) :
    IsCoatom ((planeCentralizer T t v I).subgroupOf (pointJoin T v I)) ∧
      Nonempty ((planeCentralizer T t v I ⧸ pCore 2 (planeCentralizer T t v I)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨hm,⟨e⟩⟩ := BinaryFivePointStabilizers.natural_structure
    (action (internalModule D v I)) (action_faithful _) m.quotientActor hd
    m.pointVector m.pointVector_ne_zero
  exact ⟨m.plane_maximal_of_stabilizer hm,⟨m.planeQuotientEquiv.trans e⟩⟩

/-- Source 10.2.9's rank-ten centralizer is a maximal parabolic in the actual
point join. Its intrinsic quotient is S₃ × L₃(2), with no model callback. -/
theorem LinearFiveData.plane_structure_ten {c : Context D t v I} (m : LinearFiveData c)
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 10) :
    IsCoatom ((planeCentralizer T t v I).subgroupOf (pointJoin T v I)) ∧
      Nonempty ((planeCentralizer T t v I ⧸ pCore 2 (planeCentralizer T t v I)) ≃*
        Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let : IsIrreducible (action (internalModule D v I)) := m.module_irreducible
  obtain ⟨S,hS⟩ := m.pointVector_sylow
  obtain ⟨hm,⟨e⟩⟩ := BinaryFivePointStabilizers.exterior_structure
    (action (internalModule D v I)) m.quotientActor hd S m.pointVector m.pointVector_ne_zero hS
  let e₂ := (BinaryLinear.OuterCyclic.slEquivLinear 2).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  let e₃ := (BinaryLinear.OuterCyclic.slEquivLinear 3).trans
    BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective
  exact ⟨m.plane_maximal_of_stabilizer hm,
    ⟨(m.planeQuotientEquiv.trans e).trans (e₂.prodCongr e₃)⟩⟩

/-- Both source dimensions give the genuine maximal plane centralizer. -/
theorem LinearFiveData.plane_maximal {c : Context D t v I} (m : LinearFiveData c) :
    IsCoatom ((planeCentralizer T t v I).subgroupOf (pointJoin T v I)) := by
  rcases m.dimension with hd | hd
  · exact (m.plane_structure_five hd).1
  · exact (m.plane_structure_ten hd).1

end CFSG.Quasithin.Chapter10.PointControl.Constrained
