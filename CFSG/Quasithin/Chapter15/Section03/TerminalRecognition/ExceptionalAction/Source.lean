module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition

/-!
# The exceptional action and its actual definite-plane quotients

On the original pre-intersection input, the corrected F.6.18 and B.5
witnesses and the non-S₃ hypothesis recognize the full quotient action.
The earlier ambient geometry constructs the marked-plane configuration,
so the same coordinates recognize both original definite planes. Composing
the equivariant stabilizer identification with the concrete six-plane action
gives an A₅ quotient, and lifting through the actual two-core quotient gives
an A₅ quotient of each plane normalizer in J(G₀).

The coordinates retain the full actor isomorphism, the literal quotient
action and the Thompson image. They also identify an actual odd involution
with the field involution on the three-dimensional F₄ model. The source
vector space has binary dimension four and its conjugate span has dimension
six. No action equivalence, plane orbit or stabilizer quotient is an input.

This is the conditional module calculation in the last paragraph of 15.3.1.
The earlier local geometry, including 15.3.68(2), and the classification
witnesses remain inputs; their source construction and the two terminal
contradictions belong to the assembly of Theorem 15.3.1.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed p.1155 (PDF p.1172); A.3.5, printed p.43,
and K.1.3, printed p.453 (PDF p.464).
-/

public section

open Subgroup Atlas.Codes Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace HexacodeCoordinates

variable {H : Type*} [Group H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)]
  {hC : IsPGroup 2 (centralizer (V : Set H))}
  {hcore : pCore 2 H ≤ centralizer (V : Set H)}
  (c : HexacodeCoordinates V hC hcore)

/-- The concrete plane action gives a quotient of the stabilizer in the
literal Thompson image, before lifting through the two-core quotient. -/
theorem exists_surjective_planeStabilizer (P : Subgroup H)
    (hP : Representation.Hexacode.IsFullWeightScalarPlane
      ((planeSubspace V P).map c.vectors.toLinearMap)) :
    ∃ f : ((thompsonGroup H).map coreProjection ⊓
        subspaceStabilizer (quotientAction V hC hcore) (planeSubspace V P) :
          Subgroup (coreQuotient H)) →* alternatingGroup (Fin 5),
      Function.Surjective f := by
  obtain ⟨f, hf⟩ := Representation.Hexacode.exists_surjective_planeStabilizer_A5 _ hP
  let e := planeStabilizerEquiv_hexacode V hC hcore (thompsonGroup H) P
    c.actor c.vectors c.equivariant c.thompson_image
  exact ⟨f.comp e.toMonoidHom, hf.comp e.surjective⟩

/-- The recognized quotient contains an odd involution acting by the actual
Frobenius on the three field coordinates of its original conjugation module. -/
theorem exists_field_involution :
    ∃ t : coreQuotient H, t * t = 1 ∧
      t ∉ (thompsonGroup H).map coreProjection ∧
      ∀ (v : Additive (moduleClosure V)) (i : Fin 3),
        Representation.Hexacode.binaryCoordinates
            (c.vectors (quotientAction V hC hcore t v)) i =
          Representation.SL2FourNatural.fieldFrobenius
            (Representation.Hexacode.binaryCoordinates (c.vectors v) i) := by
  let t := c.actor.symm Representation.Hexacode.fieldInvolution
  have ht : c.actor t = Representation.Hexacode.fieldInvolution := c.actor.apply_symm_apply _
  refine ⟨t, ?_, ?_, ?_⟩
  · apply c.actor.injective
    rw [map_mul, ht, Representation.Hexacode.fieldInvolution_sq, map_one]
  · intro hmem
    have himage : c.actor t ∈ hexSign.ker := by
      rw [← c.thompson_image]
      exact Subgroup.mem_map.mpr ⟨t, hmem, rfl⟩
    have hsign : hexSign Representation.Hexacode.fieldInvolution = 1 := by
      simpa only [ht, MonoidHom.mem_ker] using himage
    rw [Representation.Hexacode.fieldInvolution_odd] at hsign
    exact (by decide : (-1 : ℤˣ) ≠ 1) hsign
  · intro v i
    rw [c.equivariant, ht]
    exact Representation.Hexacode.fieldInvolution_coordinates _ i

end HexacodeCoordinates

universe u

/-- The remaining conditional calculation of 15.3.1, starting with the
genuine earlier local geometry and classification witnesses on their original
actors. Both quotient maps concern the specified source definite planes. -/
theorem EarlierGeometry.exists_exceptional_action_and_plane_quotients
    {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
    {d : NaturalOrthogonalAction M V}
    {a : Intersection.SourceInput (V.subgroupOf G₀)} (g : EarlierGeometry d a)
    (hF : FSource.Alternative (a.G1.map coreProjection) (a.G2.map coreProjection)
        a.quotientSylow ∨
      FSource.Alternative (a.G2.map coreProjection) (a.G1.map coreProjection)
        a.quotientSylow)
    (hB : let _ := g.moduleClosure_elementary
      Intersection.SourceFFAlternative a.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    let _ := g.moduleClosure_elementary
    ∃ c : HexacodeCoordinates (V.subgroupOf G₀)
        a.centralizer_isTwoGroup a.core_centralizes,
      Module.finrank (ZMod 2) (Additive (moduleClosure (V.subgroupOf G₀))) = 6 ∧
      Module.finrank (ZMod 2)
        (planeSubspace (V.subgroupOf G₀) (V.subgroupOf G₀)) = 4 ∧
      (∃ t : coreQuotient G₀, t * t = 1 ∧
        t ∉ (thompsonGroup G₀).map coreProjection ∧
        ∀ (v : Additive (moduleClosure (V.subgroupOf G₀))) (j : Fin 3),
          Representation.Hexacode.binaryCoordinates
              (c.vectors (quotientAction (V.subgroupOf G₀)
                a.centralizer_isTwoGroup a.core_centralizes t v)) j =
            Representation.SL2FourNatural.fieldFrobenius
              (Representation.Hexacode.binaryCoordinates (c.vectors v) j)) ∧
      ∀ i : OrthogonalPlaneIndex,
        (localPlane G₀ M V d i).map G₀.subtype = d.plane i ∧
        Module.finrank (ZMod 2)
          (planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)) = 2 ∧
        Representation.Hexacode.IsFullWeightScalarPlane
          ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
            c.vectors.toLinearMap) ∧
        (∃ f : ((thompsonGroup G₀).map coreProjection ⊓
            subspaceStabilizer
              (quotientAction (V.subgroupOf G₀) a.centralizer_isTwoGroup a.core_centralizes)
              (planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)) :
                Subgroup (coreQuotient G₀)) →* alternatingGroup (Fin 5),
          Function.Surjective f) ∧
        (∃ f : (thompsonGroup G₀ ⊓ normalizer (localPlane G₀ M V d i : Set G₀) :
            Subgroup G₀) →* alternatingGroup (Fin 5), Function.Surjective f) := by
  let _ := g.moduleClosure_elementary
  obtain ⟨c, hc⟩ := g.exists_coordinates_and_planes hF hB hnot
  refine ⟨c, moduleClosure_finrank_of_hexacode_equiv _ c.vectors,
    localVectorSubspace_finrank G₀ M V d g.vector_le, c.exists_field_involution, ?_⟩
  intro i
  obtain ⟨f, hf⟩ := c.exists_surjective_planeStabilizer (localPlane G₀ M V d i) (hc i)
  exact ⟨localPlane_map G₀ M V d g.vector_le i,
    localPlaneSubspace_finrank G₀ M V d g.vector_le i, hc i, ⟨f, hf⟩,
    exists_surjective_planeNormalizer_to_A5 (V.subgroupOf G₀)
      a.centralizer_isTwoGroup a.core_centralizes (thompsonGroup G₀)
      (localPlane G₀ M V d i) ((localPlane_le G₀ M V d i).trans le_normalClosure) f hf⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction
