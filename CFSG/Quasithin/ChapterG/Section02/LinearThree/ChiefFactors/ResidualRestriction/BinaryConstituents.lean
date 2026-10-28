module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Terminal
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Coordinates
public import Theory.Representation.PSL3Two.AffineConstituents
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Binary constituents on the literal G.2.5 local residual

The affine matrix calculation gives the natural flag 1|2, the dual flag 2|1,
and the irreducible translation radical. The two-spaces have the same action
through the literal quotient by the two-core. We transport these flags by the
aligned star map, retaining the natural source coordinates and both genuine
marked quotient maps. Coordinatewise constructions allow multiplicity zero.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.2.5(8),
printed pp.335–336, and the application 12.8.8, printed pp.851–852.
The preceding G.2.2 and G.2.5 layer markings remain explicit inputs; chief
refinement and intersection assembly are not asserted here.
-/

@[expose] public section
open Subgroup Matrix Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryConstituents
open Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
open Binary

abbrev Three := AffineConstituents.V
abbrev Two := AffineConstituents.W

variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g h : G}
  {d : Hypothesis D (ZMod 2) 1 g h} (a : PointAlignment d)

abbrev localLift (l : D.L₁) : D.L :=
  ⟨l, ((map_subtype_le _).trans inf_le_left) l.property⟩

def naturalBasis : Three ≃ₗ[K] Three := SpecialLinearGroup.toLin' a.basis⁻¹

def dualBasis : Three ≃ₗ[K] Three := SpecialLinearGroup.toLin' (inverseTranspose a.basis⁻¹)

/-- Source V, with the same change of basis as the local star projection. -/
def sourceCoordinates : D.V ≃* Multiplicative Three :=
  d.coordinates.trans (naturalBasis a).toAddEquiv.toMultiplicative

theorem source_equivariant (l : D.L₁) (v : D.V) :
    (sourceCoordinates a ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq (localLift l).property) v).mp
        v.property⟩).toAdd = natural (localProjection a l) (sourceCoordinates a v).toAdd := by
  change a.basis⁻¹ • (d.coordinates _).toAdd = _
  rw [d.equivariant (localLift l) v]
  exact (a.projection_natural (localLift l) (d.coordinates v).toAdd).symm

theorem source_point (v : D.V) :
    (sourceCoordinates a v).toAdd ∈ point ↔ (v : G) ∈ D.V₁ := by
  rw [d.point_mem v]
  change a.basis⁻¹ • (d.coordinates v).toAdd ∈ point ↔ _
  rw [mem_point]
  change _ ↔ (d.coordinates v).toAdd ∈ (d.point : Set Three)
  rw [a.point_eq]
  constructor
  · intro hv
    exact ⟨a.basis⁻¹ • (d.coordinates v).toAdd, hv, smul_inv_smul _ _⟩
  · rintro ⟨w, hw, he⟩
    rw [← he, inv_smul_smul]
    exact hw

/-- The genuine natural quotient map on the original V. -/
def sourceProjection : D.V →* Multiplicative Two :=
  tail.toAddMonoidHom.toMultiplicative.comp (sourceCoordinates a).toMonoidHom

theorem sourceProjection_surjective : Function.Surjective (sourceProjection a) :=
  tail_surjective.comp (sourceCoordinates a).surjective

theorem sourceProjection_kernel :
    (sourceProjection a).ker = D.V₁.subgroupOf D.V := by
  ext v
  exact source_point a v

include a in
/-- Relative normality with the original point denominator. -/
theorem sourcePoint_normal : (D.V₁.subgroupOf D.V).Normal := by
  rw [← sourceProjection_kernel a]
  infer_instance

noncomputable def sourceQuotientEquiv :
    (D.V ⧸ (sourceProjection a).ker) ≃* Multiplicative Two :=
  QuotientGroup.quotientKerEquivOfSurjective _ (sourceProjection_surjective a)

/-- The same quotient with the literal source denominator V₁. The required
normality is supplied without extra hypotheses by `sourcePoint_normal`. -/
noncomputable def sourcePointQuotientEquiv [(D.V₁.subgroupOf D.V).Normal] :
    (D.V ⧸ D.V₁.subgroupOf D.V) ≃* Multiplicative Two :=
  (QuotientGroup.quotientMulEquivOfEq (sourceProjection_kernel a).symm).trans
    (sourceQuotientEquiv a)

include a in
theorem sourcePoint_fixed (l : D.L₁) (v : D.V) (hv : (v : G) ∈ D.V₁) :
    (⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq (localLift l).property) v).mp
        v.property⟩ : D.V) = v := by
  apply (sourceCoordinates a).injective
  apply Multiplicative.toAdd.injective
  rw [source_equivariant]
  exact point_fixed _ _ ((source_point a v).mpr hv)

/-- The same irreducible binary plane for all noncentral constituents. -/
def localConstituent : Representation K D.L₁ Two := constituent (localProjection a)

theorem localConstituent_irreducible : Representation.IsIrreducible (localConstituent a) :=
  constituent_irreducible _ (localProjection_surjective a)

theorem localConstituent_on_core_quotient (l : D.L₁) :
    localConstituent a l =
      cubicAction (coreQuotientEquiv a (QuotientGroup.mk' (pCore 2 D.L₁) l)) := rfl

theorem localConstituent_noncentral : ∃ l : D.L₁, localConstituent a l ![1,0] ≠ ![1,0] := by
  obtain ⟨l, hl⟩ := localProjection_surjective a ⟨cubic,cubic_mem⟩
  refine ⟨l, ?_⟩
  change planeAction (localProjection a l) ![1,0] ≠ ![1,0]
  rw [hl]
  exact planeAction_nontrivial

theorem sourceProjection_equivariant (l : D.L₁) (v : D.V) :
    (sourceProjection a ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq (localLift l).property) v).mp
        v.property⟩).toAdd = localConstituent a l (sourceProjection a v).toAdd := by
  change tail _ = planeAction (localProjection a l) (tail _)
  exact (congrArg tail (source_equivariant a l v)).trans
    (tail_natural (localProjection a l) (sourceCoordinates a v).toAdd)

theorem dual_basis_equivariant (l : D.L₁) (v : Three) :
    dual (localProjection a l) (dualBasis a v) =
      dualBasis a ((modelProjection d (localLift l))⁻¹.val.transpose *ᵥ v) := by
  rw [← inverseTranspose_val (modelProjection d (localLift l))]
  have hproj : (localProjection a l).val =
      a.basis⁻¹ * modelProjection d (localLift l) * a.basis := by
    change a.basis⁻¹ * modelProjection d (localLift l) * (a.basis⁻¹)⁻¹ = _
    rw [inv_inv]
  change inverseTranspose (localProjection a l).val •
    (inverseTranspose a.basis⁻¹ • v) =
      inverseTranspose a.basis⁻¹ • (inverseTranspose (modelProjection d (localLift l)) • v)
  rw [hproj, map_mul, map_mul, map_inv, mul_smul, mul_smul, smul_inv_smul]

variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  {hLI : D.L ≤ I D g h} {r s : ℕ} (c : MarkedLayers d hLI r s)

def upperCoordinates : UpperQuotient D g h ≃* Multiplicative (Fin r → Three) :=
  c.upper.trans (LinearEquiv.piCongrRight fun _ : Fin r => naturalBasis a).toAddEquiv.toMultiplicative

def lowerCoordinates : LowerQuotient D g h ≃* Multiplicative (Fin s → Three) :=
  c.lower.trans (LinearEquiv.piCongrRight fun _ : Fin s => dualBasis a).toAddEquiv.toMultiplicative

theorem upper_equivariant (l : D.L₁) (v : S D g h) (i : Fin r) :
    (upperCoordinates a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h (hLI (localLift l).property)) v).mp
          v.property⟩)).toAdd i =
    natural (localProjection a l)
      ((upperCoordinates a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v)).toAdd i) := by
  change naturalBasis a ((c.upper _).toAdd i) = _
  rw [c.upper_equivariant (localLift l) v i]
  exact (a.projection_natural (localLift l) _).symm

theorem lower_equivariant (l : D.L₁) (v : S₃ D g h) (i : Fin s) :
    (lowerCoordinates a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.lower_normalizes (localLift l).property) v).mp
          v.property⟩)).toAdd i =
    dual (localProjection a l)
      ((lowerCoordinates a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) v)).toAdd i) := by
  change dualBasis a ((c.lower _).toAdd i) = _
  rw [c.lower_equivariant (localLift l) v i, map_inv]
  exact (dual_basis_equivariant a l
    ((c.lower (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) v)).toAdd i)).symm

/-- The upper natural layer's quotient by all of its central points. -/
def upperProjection : UpperQuotient D g h →* Multiplicative (Fin r → Two) :=
  (tailCopies r).toAddMonoidHom.toMultiplicative.comp (upperCoordinates a c).toMonoidHom

/-- The lower dual layer's central quotient, retaining every scalar factor. -/
def lowerProjection : LowerQuotient D g h →* Multiplicative (Fin s → K) :=
  (firstCopies s).toAddMonoidHom.toMultiplicative.comp (lowerCoordinates a c).toMonoidHom

theorem upperProjection_surjective : Function.Surjective (upperProjection a c) :=
  (tailCopies_surjective r).comp (upperCoordinates a c).surjective

theorem lowerProjection_surjective : Function.Surjective (lowerProjection a c) :=
  (firstCopies_surjective s).comp (lowerCoordinates a c).surjective

noncomputable def upperQuotientEquiv :
    (UpperQuotient D g h ⧸ (upperProjection a c).ker) ≃* Multiplicative (Fin r → Two) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (upperProjection_surjective a c)

noncomputable def lowerQuotientEquiv :
    (LowerQuotient D g h ⧸ (lowerProjection a c).ker) ≃* Multiplicative (Fin s → K) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (lowerProjection_surjective a c)

/-- Actual transported invariant flags, with all central constituents retained. -/
def upperFlag : Subrepresentation ((copies natural r).comp (localProjection a)) :=
  naturalFlag (localProjection a) r

def lowerFlag : Subrepresentation ((copies dual s).comp (localProjection a)) :=
  dualFlag (localProjection a) s

theorem upper_kernel_mem (v : UpperQuotient D g h) :
    v ∈ (upperProjection a c).ker ↔ (upperCoordinates a c v).toAdd ∈ upperFlag a (r := r) := Iff.rfl

theorem lower_kernel_mem (v : LowerQuotient D g h) :
    v ∈ (lowerProjection a c).ker ↔ (lowerCoordinates a c v).toAdd ∈ lowerFlag a (s := s) := Iff.rfl

/-- The central points in the upper layer, including multiplicity zero. -/
def upperKernelEquiv : (upperProjection a c).ker ≃* Multiplicative (Fin r → K) :=
  (kernelCoordinates (upperCoordinates a c) (tailCopies r)).trans
    (pointCopiesEquiv r).toAddEquiv.toMultiplicative

/-- The lower annihilator planes with the genuine natural two-space action. -/
def lowerKernelEquiv : (lowerProjection a c).ker ≃* Multiplicative (Fin s → Two) :=
  (kernelCoordinates (lowerCoordinates a c) (firstCopies s)).trans
    (dualPlaneCopiesEquiv s).symm.toAddEquiv.toMultiplicative

omit [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal] in
theorem upperFlag_fixed (l : D.L₁) (v : (upperFlag a (r := r)).toSubmodule) :
    (copies natural r).comp (localProjection a) l v.val = v.val :=
  naturalFlag_fixed (localProjection a) r l v

omit [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal] in
theorem lowerFlag_central (l : D.L₁) (v : Fin s → Three) :
    firstCopies s ((copies dual s).comp (localProjection a) l v) = firstCopies s v :=
  dualFlag_central_quotient (localProjection a) s l v

omit [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal] in
theorem lowerFlag_noncentral_action (l : D.L₁) (v : Fin s → Two) :
    (copies dual s).comp (localProjection a) l (dualPlaneCopiesEquiv s v).val =
      (dualPlaneCopiesEquiv s (fun i => localConstituent a l (v i))).val :=
  dualFlag_intertwines (localProjection a) s l v

omit [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal] in
theorem upperFlag_noncentral_action (l : D.L₁) (v : Fin r → Three) (i : Fin r) :
    tailCopies r ((copies natural r).comp (localProjection a) l v) i =
      localConstituent a l (tailCopies r v i) :=
  naturalFlag_quotient_map (localProjection a) r l v i

omit [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal] in
theorem radical_local_action (l : D.L₁) (t : pointV) :
    (radicalEquiv (radicalConj (localProjection a l) t)).toAdd =
      localConstituent a l (radicalEquiv t).toAdd :=
  radical_equivariant _ _

/-- The kernel in the upper layer is fixed by the actual local actor. -/
theorem upper_kernel_fixed (l : D.L₁) (v : S D g h)
    (hv : QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v ∈ (upperProjection a c).ker) :
    QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h (hLI (localLift l).property)) v).mp
          v.property⟩ =
      QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v := by
  apply (upperCoordinates a c).injective
  apply Multiplicative.toAdd.injective
  funext i
  rw [upper_equivariant]
  apply point_fixed
  exact congrFun hv i

/-- The entire scalar quotient of the lower layer is central, with no
nonzero-multiplicity assumption. -/
theorem lower_quotient_central (l : D.L₁) (v : S₃ D g h) :
    lowerProjection a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.lower_normalizes (localLift l).property) v).mp
          v.property⟩) =
    lowerProjection a c (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) v) := by
  apply Multiplicative.toAdd.injective
  funext i
  change first ((lowerCoordinates a c _).toAdd i) = first ((lowerCoordinates a c _).toAdd i)
  rw [lower_equivariant,first_dual]

theorem upper_quotient_action (l : D.L₁) (v : S D g h) (i : Fin r) :
    (upperProjection a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h (hLI (localLift l).property)) v).mp
          v.property⟩)).toAdd i =
    localConstituent a l
      ((upperProjection a c (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v)).toAdd i) := by
  change tail ((upperCoordinates a c _).toAdd i) = planeAction (localProjection a l) _
  rw [upper_equivariant]
  exact tail_natural _ _

theorem upperQuotientEquiv_mk (v : UpperQuotient D g h) :
    upperQuotientEquiv a c (QuotientGroup.mk' (upperProjection a c).ker v) =
      upperProjection a c v := rfl

theorem lowerQuotientEquiv_mk (v : LowerQuotient D g h) :
    lowerQuotientEquiv a c (QuotientGroup.mk' (lowerProjection a c).ker v) =
      lowerProjection a c v := rfl

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryConstituents
