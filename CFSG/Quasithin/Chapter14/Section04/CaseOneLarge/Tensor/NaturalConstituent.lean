module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Actor
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural

/-!
# The selected natural constituent in the original central quotient

The inverse tensor coordinates lift the selected subspace to its full
preimage in U. The marked A₅-module identification gives the actual
SL₂(4) constituent used by the natural geometry. Its displacement description
and the invariant index-two hyperplane put the preimage in W, using the
original Wᵍ and [W,Wᵍ] ≤ E. The next source consumer applies these results
to obtain X₂ ∈ Y.

Source: Aschbacher--Smith 14.4.10, printed pp.1010--1011.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorGeometry
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open LargerDimension LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {F : InvariantFlag T V 3} [IsElementaryAbelian 2 F.Uhat]

/-- The full actual preimage of a tensor constituent. -/
def preimage (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] W)) : Subgroup G :=
  (M.toAddSubgroup.toSubgroup'.comap c.quotientMap).map F.U.subtype

omit [Finite G] [IsElementaryAbelian 2 F.Uhat] in
theorem preimage_le (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] W)) :
    preimage c M ≤ F.U := map_subtype_le _

omit [Finite G] [IsElementaryAbelian 2 F.Uhat] in
theorem image_preimage (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] W)) :
    c.image (preimage c M) = M := by
  ext v
  constructor
  · rintro ⟨u, ⟨a, ha, he⟩, rfl⟩
    have he' : a = u := Subtype.ext he
    subst a
    exact ha
  · intro hv
    obtain ⟨a, ha⟩ := c.quotientMap_surjective (Multiplicative.ofAdd v)
    refine (c.mem_image _ _).mpr ⟨a, ?_, congrArg Multiplicative.toAdd ha⟩
    exact mem_map_of_mem F.U.subtype (show c.quotientMap a ∈ M.toAddSubgroup.toSubgroup' from ha.symm ▸ hv)

omit [Finite G] in
/-- Evaluation of the natural-geometry action in the prescribed tensor coordinates. -/
theorem natural_coordinates_equivariant
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) (a : F.H) (w : Additive F.Uhat) :
    linearCoordinates c (Natural.Geometry.representation c.H_normalizes_U a w) =
      sourceTensorAction c.constituent (c.actor (QuotientGroup.mk' (pCore 2 F.H) a))
        (linearCoordinates c w) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
  have hw : Additive.ofMul (QuotientGroup.mk' (center F.U) u) = w := congrArg Additive.ofMul hu
  rw [← hw, Natural.Geometry.representation_mk, linearCoordinates_apply, linearCoordinates_apply]
  exact congrArg Multiplicative.toAdd (c.equivariant a u)

/-- The constituent map retains both the group quotient and its module action. -/
def naturalConstituent (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    {g : G} (s : c.SelectedConstituent T (F.Vi 2) g)
    (e : AltFive ≃* Representation.SL2FourNatural.SL)
    (f : W ≃ₗ[ZMod 2] Representation.SL2FourNatural.V)
    (hf : ∀ a w, f (c.constituent (inclusion hAD a) w) =
      Representation.SL2FourNatural.action (e a) (f w)) :
    Natural.Geometry.Constituent F.H F.U (preimage c s.firstSpace) c.H_normalizes_U := by
  let l := linearCoordinates c
  let Q := binarySpace (Natural.tilde F.U (preimage c s.firstSpace))
  have hQ : Q.map l.toLinearMap = s.firstSpace := by
    exact (image_eq_map c (preimage c s.firstSpace)).symm.trans (image_preimage c s.firstSpace)
  let q : Q ≃ₗ[ZMod 2] s.firstSpace :=
    (l.submoduleMap Q).trans (LinearEquiv.ofEq _ _ hQ)
  let m := (f.symm.trans s.constituentEquiv).trans q.symm
  let eK := starComponentEquiv hAD c.actor
  refine ⟨eK.trans e, m, ?_⟩
  intro a ha v
  apply l.injective
  have hm (w : Representation.SL2FourNatural.V) :
      l (m w).val = (s.constituentEquiv (f.symm w)).val := by
    change (q (q.symm (s.constituentEquiv (f.symm w)))).val = _
    rw [q.apply_symm_apply]
  rw [natural_coordinates_equivariant, hm, hm]
  let b : star F.H (component F.H) := ⟨QuotientGroup.mk' (pCore 2 F.H) a, ha⟩
  have hmark : c.actor b.val = (1, inclusion hAD (eK b)) := by
    have hk := mem_map_of_mem c.actor.toMonoidHom b.property
    rw [star_component_marked hAD c.actor] at hk
    exact Prod.ext hk.1 rfl
  have heq : f.symm (Representation.SL2FourNatural.action (e (eK b)) v) =
      c.constituent (inclusion hAD (eK b)) (f.symm v) := by
    apply f.injective
    rw [f.apply_symm_apply, hf, f.apply_symm_apply]
  change sourceTensorAction c.constituent (c.actor b.val) _ =
    (s.constituentEquiv (f.symm (Representation.SL2FourNatural.action (e (eK b)) v))).val
  rw [hmark, heq, s.constituent_equivariant]

omit [Finite G] [IsElementaryAbelian 2 F.Uhat] in
/-- The selected displacement constituent lies in the actual hyperplane W. -/
theorem preimage_le_hyperplane (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    {g : G} (s : c.SelectedConstituent T (F.Vi 2) g)
    (hindex : F.W.relIndex F.U = 2)
    (hsource : ⁅F.W, F.X g⁆ ≤ F.E g) :
    preimage c s.firstSpace ≤ F.W := by
  obtain ⟨a, ha, he⟩ := s.element_mem
  have haX : (a : G) ∈ F.X g := ha
  let A : Subgroup G := zpowers (a : G)
  have hAH : A ≤ F.H := zpowers_le.mpr a.property
  have hAX : A ≤ F.X g := zpowers_le.mpr haX
  have hXW : F.X g ≤ normalizer (F.W : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hsource.trans inf_le_left)
  have hmove : ⁅F.U, A⁆ ≤ F.W :=
    Natural.commutator_le_of_invariant_index_two hindex
      (hAH.trans c.H_normalizes_U) (hAX.trans hXW)
  have hrange : s.firstSpace ≤ c.image ⁅F.U, A⁆ := by
    change s.firstSpace ≤ c.image (LargerDimension.movedSpace F.U A)
    rw [s.first_eq_range, c.image_commutator le_rfl hAH]
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    refine ⟨c.actor s.element, ?_, w, ?_, rfl⟩
    · refine ⟨s.element, ?_, rfl⟩
      exact ⟨a, mem_zpowers (a : G), he⟩
    · obtain ⟨u, hu⟩ := c.quotientMap_surjective (Multiplicative.ofAdd w)
      exact (c.mem_image F.U w).mpr ⟨u, u.property, congrArg Multiplicative.toAdd hu⟩
  have hZW : center F.U ≤ F.W.subgroupOf F.U := by
    intro z hz
    exact ⟨z.property, mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val ((mem_center_iff.mp hz) ⟨x, (F.le_seed 2).trans
        (le_conjugateSpanBy V F.H) hx⟩)⟩
  apply Natural.le_of_tilde_le (preimage_le c _) hZW
  apply c.image_le_iff.mp
  rw [image_preimage]
  exact hrange.trans (c.image_mono hmove)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorGeometry
