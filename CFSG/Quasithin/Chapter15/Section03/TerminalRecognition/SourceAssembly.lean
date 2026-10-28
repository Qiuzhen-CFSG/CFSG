module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Basic
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The terminal recognition alternative for Theorem 15.3.1

The actual pre-intersection input and its aligned earlier ambient geometry
give two outcomes. In the S₃ case, the residual X_E and the centralization
of Z and F retain precisely the identities used by the short normalizer
contradiction. In the other case, the completed classification intersection,
source-cover comparison and representation recognition identify G₀/O₂(G₀)
with the full hexacode group on the original six-dimensional conjugate span.
Both original definite planes have actual A₅ quotients of their stabilizers.

The intrinsic normalizer quotient is transported through the inclusion of
G₀ to X ∩ N_G(V_i), where X is the ambient image of J(G₀). This transport
does not assume that the two-core quotient is injective on X. The source
omega-center is restricted from the original Sylow group, and the S₃
centralizer premises are derived from its centrality and X_E = O²(C_G(E)).

Earlier local geometry, the centrality clause 15.3.68(2), the singular-line
span identity, and the genuine F.6.18/B.5 classification implications remain
with the source assembly of 15.3.1. No recognized model, vector coordinates,
plane orbit or normalizer quotient is an input to this terminal alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final proof
of Theorem 15.3.1, printed p.1155 (PDF p.1172), using 15.3.66–68. The hatted
symmetric group is the nonsplit cubic-cover extension from A.3.5 and K.1.3.
-/

@[expose] public section

open Subgroup Atlas.Codes Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

open ExceptionalAction AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u
variable {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  {a : Intersection.SourceInput (V.subgroupOf G₀)}

/-- The source X = J(G₀), embedded in the original ambient group. -/
noncomputable abbrev ambientThompson (G₀ : Subgroup G) : Subgroup G :=
  (thompsonGroup G₀).map G₀.subtype

/-- The normalizer intersection is the same actual group before and after
restricting to G₀; the plane is the specified definite summand. -/
noncomputable def ExceptionalAction.EarlierGeometry.planeNormalizerEquiv (g : EarlierGeometry d a)
    (i : OrthogonalPlaneIndex) :
    (thompsonGroup G₀ ⊓ normalizer (localPlane G₀ M V d i : Set G₀) : Subgroup G₀) ≃*
      (ambientThompson G₀ ⊓ normalizer (d.plane i : Set G) : Subgroup G) := by
  have hX : (ambientThompson G₀).subgroupOf G₀ = thompsonGroup G₀ :=
    by rw [← comap_subtype, comap_map_eq_self_of_injective G₀.subtype_injective]
  refine (MulEquiv.subgroupCongr ?_).trans
    (localNormalizerIntersectionEquiv G₀ (ambientThompson G₀) (d.plane i)
      (map_subtype_le _) ((d.plane_le i).trans g.vector_le))
  change thompsonGroup G₀ ⊓ normalizer ((d.plane i).subgroupOf G₀ : Set G₀) =
    (ambientThompson G₀).subgroupOf G₀ ⊓ normalizer ((d.plane i).subgroupOf G₀ : Set G₀)
  rw [hX]

/-- The actual ambient X ∩ N_G(V_i) has an A₅ quotient in the non-S₃
branch, after specializing the classifiers to the given local group. -/
theorem ExceptionalAction.EarlierGeometry.exists_surjective_ambientPlaneNormalizer
    (g : EarlierGeometry d a) {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3)))
    (i : OrthogonalPlaneIndex) :
    ∃ f : (ambientThompson G₀ ⊓ normalizer (d.plane i : Set G) : Subgroup G) →*
      alternatingGroup (Fin 5), Function.Surjective f := by
  obtain ⟨f, hf⟩ := g.exists_surjective_localPlaneNormalizer
    hG₀ classificationF classificationB hnot i
  let e := g.planeNormalizerEquiv i
  exact ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective⟩

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]

/-- The complete non-S₃ output. Every action and normalizer refers to the
original quotient, conjugate-span module and definite planes. -/
structure ExceptionalConclusion (d : NaturalOrthogonalAction M V)
    (a : Intersection.SourceInput (V.subgroupOf G₀)) where
  coordinates : HexacodeCoordinates (V.subgroupOf G₀)
    a.centralizer_isTwoGroup a.core_centralizes
  dimension : Module.finrank (ZMod 2) (Additive (moduleClosure (V.subgroupOf G₀))) = 6
  vector_dimension : Module.finrank (ZMod 2)
    (planeSubspace (V.subgroupOf G₀) (V.subgroupOf G₀)) = 4
  field_involution : ∃ t : coreQuotient G₀, t * t = 1 ∧
    t ∉ (thompsonGroup G₀).map coreProjection ∧
    ∀ (v : Additive (moduleClosure (V.subgroupOf G₀))) (j : Fin 3),
      Representation.Hexacode.binaryCoordinates
          (coordinates.vectors (quotientAction (V.subgroupOf G₀)
            a.centralizer_isTwoGroup a.core_centralizes t v)) j =
        Representation.SL2FourNatural.fieldFrobenius
          (Representation.Hexacode.binaryCoordinates (coordinates.vectors v) j)
  plane_map : ∀ i : OrthogonalPlaneIndex,
    (localPlane G₀ M V d i).map G₀.subtype = d.plane i
  plane_dimension : ∀ i : OrthogonalPlaneIndex, Module.finrank (ZMod 2)
    (planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)) = 2
  plane_fullWeight : ∀ i : OrthogonalPlaneIndex,
    Representation.Hexacode.IsFullWeightScalarPlane
      ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
        coordinates.vectors.toLinearMap)
  stabilizer_quotients : ∀ i : OrthogonalPlaneIndex,
    ∃ f : ((thompsonGroup G₀).map coreProjection ⊓
        subspaceStabilizer
          (quotientAction (V.subgroupOf G₀) a.centralizer_isTwoGroup a.core_centralizes)
          (planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)) :
            Subgroup (coreQuotient G₀)) →* alternatingGroup (Fin 5),
      Function.Surjective f
  local_normalizer_quotients : ∀ i : OrthogonalPlaneIndex,
    ∃ f : (thompsonGroup G₀ ⊓ normalizer (localPlane G₀ M V d i : Set G₀) :
      Subgroup G₀) →* alternatingGroup (Fin 5), Function.Surjective f
  ambient_normalizer_quotients : ∀ i : OrthogonalPlaneIndex,
    ∃ f : (ambientThompson G₀ ⊓ normalizer (d.plane i : Set G) : Subgroup G) →*
      alternatingGroup (Fin 5), Function.Surjective f

/-- Assemble recognition and both ambient A₅ quotients, with no additional
model, coordinate, full-weight or plane-normalizer premise. -/
theorem ExceptionalAction.EarlierGeometry.nonS3_conclusion (g : EarlierGeometry d a)
    (hF : FSource.Alternative (a.G1.map coreProjection) (a.G2.map coreProjection)
        a.quotientSylow ∨
      FSource.Alternative (a.G2.map coreProjection) (a.G1.map coreProjection)
        a.quotientSylow)
    (hB : Intersection.SourceFFAlternative a.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Nonempty (ExceptionalConclusion d a) := by
  obtain ⟨c, h6, h4, ht, hp⟩ := g.exists_exceptional_action_and_plane_quotients hF hB hnot
  refine ⟨{ coordinates := c
            dimension := h6
            vector_dimension := h4
            field_involution := ht
            plane_map := fun i => (hp i).1
            plane_dimension := fun i => (hp i).2.1
            plane_fullWeight := fun i => (hp i).2.2.1
            stabilizer_quotients := fun i => (hp i).2.2.2.1
            local_normalizer_quotients := fun i => (hp i).2.2.2.2
            ambient_normalizer_quotients := ?_ }⟩
  intro i
  obtain ⟨f, hf⟩ := (hp i).2.2.2.2
  let e := g.planeNormalizerEquiv i
  exact ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective⟩

omit [Finite G] [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The actual source omega-center centralizes the intrinsic Sylow group,
and the actual X_E centralizes the original singular plane. -/
theorem ExceptionalAction.EarlierGeometry.seed_centralizers (g : EarlierGeometry d a) :
    a.XE ≤ centralizer (g.E.subgroupOf G₀ : Set G₀) ∧
      (centralInvolutions g.T).subgroupOf G₀ ≤ centralizer (a.T : Set G₀) := by
  constructor
  · intro x hx e he
    have hxE : (x : G) ∈ lineX g.E := g.second_map ▸ mem_map_of_mem G₀.subtype hx
    exact Subtype.ext (lineX_le_centralizer g.E hxE e.val he)
  · intro z hz t ht
    have htE : (t : G) ∈ lineT g.T g.E := g.sylow_map ▸ mem_map_of_mem G₀.subtype ht
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow g.T hz t.val htE.1)

/-- The source terminal alternative. The only extra seed inputs are the
earlier containment Z ≤ E and F = ⟨Z^{Y_F}⟩ from the singular-line construction. -/
theorem ExceptionalAction.EarlierGeometry.terminal_alternative (g : EarlierGeometry d a)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hFspan : a.F = conjugateSpanBy ((centralInvolutions g.T).subgroupOf G₀) a.YF)
    (hF : FSource.Alternative (a.G1.map coreProjection) (a.G2.map coreProjection)
        a.quotientSylow ∨
      FSource.Alternative (a.G2.map coreProjection) (a.G1.map coreProjection)
        a.quotientSylow)
    (hB : Intersection.SourceFFAlternative a.offenderAction) :
    Cases.SymmetricThreeConclusion a ((centralInvolutions g.T).subgroupOf G₀) ∨
      Nonempty (ExceptionalConclusion d a) := by
  by_cases hs : Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))
  · obtain ⟨hXE, hZT⟩ := g.seed_centralizers
    obtain ⟨hres, hZ, hspan⟩ := symmetricThree_branch a.T a.XE (g.E.subgroupOf G₀)
      ((centralInvolutions g.T).subgroupOf G₀) a.YF
      a.second_commutator a.second_escape a.second_perfect
      ((a.second_local.symm ▸ le_sup_right).trans a.second_normalized)
      (fun _ hz => hZE hz) hXE hZT hs.some
    exact Or.inl ⟨hs, hres, hZ, hspan, hFspan.symm ▸ hspan⟩
  · exact Or.inr (g.nonS3_conclusion hF hB hs)

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- Specialize the genuine full classifiers and construct elementarity
before applying the terminal alternative on the unchanged local input. -/
theorem ExceptionalAction.EarlierGeometry.terminal_alternative_of_full_classifications
    (g : EarlierGeometry d a) {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hFspan : a.F = conjugateSpanBy ((centralInvolutions g.T).subgroupOf G₀) a.YF) :
    let _ := g.moduleClosure_elementary
    Cases.SymmetricThreeConclusion a ((centralInvolutions g.T).subgroupOf G₀) ∨
      Nonempty (ExceptionalConclusion d a) := by
  let _ := g.moduleClosure_elementary
  exact g.terminal_alternative hZE hFspan
    (a.full_goldschmidt_alternative hG₀ classificationF)
    (a.full_sourceFF_alternative hG₀ classificationB)

omit [Finite G] [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- Transfer the actual ambient singular-line span through the inclusion
of G₀, preserving its chosen residual actor and conjugate plane. -/
theorem ExceptionalAction.EarlierGeometry.intrinsic_seed_span (g : EarlierGeometry d a)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hspan : otherLine g.E g.s = conjugateSpanBy (centralInvolutions g.T)
      (otherLine (lineY (residualY M g.Mc) g.E) g.s)) :
    a.F = conjugateSpanBy ((centralInvolutions g.T).subgroupOf G₀) a.YF := by
  have hZG : centralInvolutions g.T ≤ G₀ :=
    hZE.trans (g.singular.1.trans g.vector_le)
  apply Subgroup.map_injective G₀.subtype_injective
  rw [g.singular_map, map_conjugateSpanBy, map_subgroupOf_eq_of_le hZG, g.first_map]
  exact hspan

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The terminal source implication with the singular span stated in the
original ambient group, as supplied by 15.3.66 and its conjugate. -/
theorem ExceptionalAction.EarlierGeometry.terminal_alternative_of_ambient_span
    (g : EarlierGeometry d a) {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hspan : otherLine g.E g.s = conjugateSpanBy (centralInvolutions g.T)
      (otherLine (lineY (residualY M g.Mc) g.E) g.s)) :
    let _ := g.moduleClosure_elementary
    Cases.SymmetricThreeConclusion a ((centralInvolutions g.T).subgroupOf G₀) ∨
      Nonempty (ExceptionalConclusion d a) :=
  g.terminal_alternative_of_full_classifications hG₀ classificationF classificationB hZE
    (g.intrinsic_seed_span hZE hspan)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
