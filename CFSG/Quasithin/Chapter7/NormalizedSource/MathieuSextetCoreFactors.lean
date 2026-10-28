module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetFactors
public import Theory.GroupTheory.PCoreImage

/-!
# The full residual action on sextet translations

The native conjugation identity transports the full hexacode translation
module to any marked core section with its literal kernel. The perfect sextet
residual covers the even hexacode group, so this action is irreducible while
retaining the cubic center of 3.A₆. The sign quotient also shows that every
intermediate subgroup above the perfect residual has the full translation
two-core, with its original embedding.

NonFFSourceMathieuM24CoreFactors applies this to the original O₂(L_z)/V,
providing the dual irreducibility interval used in source 8.2.12. It adds no
module marking beyond the earlier whole-cocode marking.
Source: Aschbacher–Smith H.15.3 and 8.2.11(4), printed pp.400,722,
refs/quasithin.pdf. Imported Golay and affine hexacode constructions are by
Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers MathieuCode.SextetLayers.CoordinateTransport Atlas.Codes
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
set_option backward.isDefEq.respectTransparency false

/-- The actual conjugation action on all sextet translations. -/
@[expose] def coreAction {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) : Representation (ZMod 2) A hexacode :=
  (nativeHexacodeRepresentation S).comp r

/-- The full translation module stays irreducible on the perfect residual. -/
theorem core_residual_irreducible {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) (hr : r.range = solvableResidual (sextetStabilizer S)) :
    IsIrreducible (coreAction S r) := by
  obtain ⟨p,hp,hval⟩ := marked_even_quotient S r hr
  have he : coreAction S r = Hexacode.evenAction.comp p := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change Hexacode.action (nativeQuotient S (r g)) v = Hexacode.action (p g).val v
    rw [hval]
  rw [he]
  exact (irreducible_comp_surjective_iff p hp _).mpr Hexacode.evenAction_isIrreducible

/-- Native translation coordinates retain the original core and kernel. -/
theorem marked_core_section {G : Type*} [Group G]
    (S : Sextet) (R X W : Subgroup G) (hXR : X ≤ R) (hWX : W ≤ X)
    (hRX : R ≤ normalizer (X : Set G))
    (r : R →* sextetStabilizer S) (hk : r.ker = W.subgroupOf R)
    (hX : (X.subgroupOf R).map r = (nativeTranslation S).range) :
    Nonempty (BinaryConjugationSection R X W (coreAction S r)) := by
  let e : Multiplicative hexacode ≃* (nativeTranslation S).range :=
    MonoidHom.ofInjective (nativeTranslation_injective S)
  let b : X →* (nativeTranslation S).range :=
    (r.comp (inclusion hXR)).codRestrict _ (fun x => hX ▸ mem_map_of_mem r x.property)
  let f := e.symm.toMonoidHom.comp b
  have hf (x : X) : nativeTranslation S (f x) = r (inclusion hXR x) :=
    congrArg Subtype.val (e.apply_symm_apply (b x))
  refine ⟨{
    section_le := hXR
    kernel_le := hWX
    normalized := hRX
    coordinates := f
    onto := ?_
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · intro t
    obtain ⟨x,hx,hxt⟩ := hX.ge (show nativeTranslation S t ∈ (nativeTranslation S).range from ⟨t,rfl⟩)
    refine ⟨⟨x,hx⟩,?_⟩
    apply nativeTranslation_injective S
    exact (hf ⟨x,hx⟩).trans hxt
  · ext x
    change f x = 1 ↔ (x : G) ∈ W
    rw [←(nativeTranslation_injective S).eq_iff, map_one, hf]
    exact show r (inclusion hXR x) = 1 ↔ (x : G) ∈ W from
      Iff.of_eq (congrArg (fun K : Subgroup R => inclusion hXR x ∈ K) hk)
  · intro g x
    apply Multiplicative.ofAdd.injective
    apply nativeTranslation_injective S
    simp only [ofAdd_toAdd]
    change _ = nativeTranslation S (Multiplicative.ofAdd
      (nativeHexacodeRepresentation S (r g) (f x).toAdd))
    rw [hf, ←nativeHexacodeRepresentation_conjugation, hf]
    change r (g * inclusion hXR x * g⁻¹) = r g * r (inclusion hXR x) * (r g)⁻¹
    rw [map_mul,map_mul,map_inv]

private theorem native_residual_sign_kernel (S : Sextet) :
    solvableResidual (sextetStabilizer S) = (hexSign.comp (nativeQuotient S)).ker := by
  have hh : solvableResidual HexAutomorphisms = hexSign.ker := by
    let : Group.IsPerfect HexEvenAutomorphisms := Hexacode.even_isPerfect
    apply le_antisymm
    · intro x hx
      have hm := map_solvableResidual_le hexSign (mem_map_of_mem hexSign hx)
      rw [solvableResidual_eq_bot] at hm
      exact hm
    · exact le_solvableResidual_of_isPerfect hexSign.ker
  have hm : (solvableResidual (sextetStabilizer S)).map (nativeQuotient S) = hexSign.ker := by
    rw [map_solvableResidual_eq _ (nativeQuotient_surjective S),hh]
  have hk : (nativeQuotient S).ker ≤ solvableResidual (sextetStabilizer S) :=
    (native_core_kernel S).symm ▸ native_core_le_residual S
  change _ = hexSign.ker.comap (nativeQuotient S)
  rw [←hm,comap_map_eq_self hk]

/-- Every intermediate native subgroup above the perfect residual has
exactly the same embedded two-core, the full translation subgroup. -/
theorem residual_overgroup_core (S : Sextet) (Y : Subgroup (sextetStabilizer S))
    (hY : solvableResidual (sextetStabilizer S) ≤ Y) :
    Y.pCoreIn 2 = (nativeTranslation S).range := by
  have hcomm : _root_.commutator (sextetStabilizer S) ≤ solvableResidual (sextetStabilizer S) := by
    rw [native_residual_sign_kernel]
    apply commutator_le.mpr
    intro x _ y _
    change (hexSign.comp (nativeQuotient S)) ⁅x,y⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  let : Y.Normal := Normal.of_commutator_le _ (hcomm.trans hY)
  have hc := (inferInstance : Y.Normal).isSubnormal.pCore_subgroupOf 2
  have hm := congrArg (Subgroup.map Y.subtype) hc
  rw [map_subgroupOf_eq_of_le ((native_core_le_residual S).trans hY)] at hm
  exact hm.symm.trans ((native_core_kernel S).trans (nativeQuotient_kernel S))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
