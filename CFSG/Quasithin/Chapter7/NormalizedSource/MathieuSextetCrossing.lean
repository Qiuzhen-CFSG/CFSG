module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCoreFactors
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioMarking
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneCentralizer

/-!
# Comparing the original sextet and trio markings

Every nonzero vector of the native trio three-space is a tetrad class of a
sextet refining that same trio. The full GL₃(2) action reduces the comparison
to the existing coordinate sextet. Consequently its seven-dimensional pair
space lies in the original nine-dimensional trio pair space.

The point-commutator transport retains an arbitrary compatible component
marking, its full two-group kernel, the perfect centralizer residual and all
64 native translations. NonFFSourceMathieuM24Crossing applies these results
to the same selected pair and the original central involution, discharging
the incidence premise in the crossing step of source 8.2.12.

Source: Aschbacher–Smith H.15.8 and 8.2.12, printed pp.402,722,
refs/quasithin.pdf. The imported Golay and affine coordinates are by Gerald
Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.Stabilizers
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
set_option backward.isDefEq.respectTransparency false

private theorem vector_conjugate (g : M24) (S : Sextet) :
    sextetVector (conjugateSextet g S) = cocodeRepresentation g (sextetVector S) := by
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  have hgB : g • B ∈ (conjugateSextet g S).parts := Finset.smul_mem_smul_finset hB
  rw [sextetVector_eq S hB,evenSetVector_equivariant,sextetVector_eq _ hgB]

private theorem linear_transitive {v w : Vector} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ f : Vector ≃ₗ[ZMod 2] Vector, f v = w := by
  let d := (LinearEquiv.coord (ZMod 2) Vector v hv).trans
    (LinearEquiv.coord (ZMod 2) Vector w hw).symm
  obtain ⟨f,hf⟩ := Submodule.exists_linearEquiv_restrict_eq d
  refine ⟨f,?_⟩
  have hh := hf ⟨v,Submodule.mem_span_singleton_self v⟩
  have hd : d ⟨v,Submodule.mem_span_singleton_self v⟩ =
      ⟨w,Submodule.mem_span_singleton_self w⟩ := by
    apply (LinearEquiv.coord (ZMod 2) Vector w hw).injective
    simp [d,LinearEquiv.coord_self]
  rw [hd] at hh
  exact hh.symm

/-- Every sextet whose tetrad class lies in the original trio plane refines
that same trio. The two independently constructed markings are compared. -/
theorem sextet_refines_of_vector_mem_plane (S : Sextet)
    (hS : sextetVector S ∈ standardPlaneMap.range) :
    ∀ B ∈ S.parts, ∃ O ∈ standardTrio.parts, B ⊆ O := by
  obtain ⟨v,hv⟩ := hS
  have hv0 : v ≠ 0 := by
    intro he
    rw [he,map_zero] at hv
    exact sextetVector_ne_zero S hv.symm
  have he0 : (Pi.single (0 : Fin 3) (1 : ZMod 2) : Vector) ≠ 0 := by decide
  obtain ⟨f,hf⟩ := linear_transitive he0 hv0
  obtain ⟨g,hg⟩ := standardPlaneMap_full_action f
  have hEq : conjugateSextet g.val (coordinateSextet 0) = S := by
    apply sextetVector_injective
    rw [vector_conjugate,coordinateSextet_vector,hg,hf,hv]
  intro B hB
  rw [←hEq] at hB
  obtain ⟨A,hA,rfl⟩ := Finset.mem_smul_finset.mp hB
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hA
  have hsub : half 0 p.1 p.2 ⊆ standardTrioOctad p.1 := by
    intro x hx
    have hxi := (Finset.mem_filter.mp hx).2.1
    rw [←point_coordinates x]
    exact (point_mem_octad_iff _ _ _).mpr hxi
  refine ⟨g.val • standardTrioOctad p.1,?_,Finset.image_mono _ hsub⟩
  exact (mem_trioStabilizer_iff _ _).mp g.property _ (Finset.mem_image.mpr ⟨p.1,Finset.mem_univ _,rfl⟩)

/-- The point seven-space lies in the original trio nine-space whenever
its central tetrad vector belongs to the original three-space. -/
theorem sextet_pair_le_of_vector_mem_plane (S : Sextet)
    (hS : sextetVector S ∈ standardPlaneMap.range) :
    (⨆ B ∈ S.parts, supportedPairSpace B) ≤ standardPairSpace := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  obtain ⟨O,hO,hBO⟩ := sextet_refines_of_vector_mem_plane S hS B hB
  exact le_iSup_of_le O (le_iSup_of_le hO (supportedPairSpace_mono hBO))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
open Chapter8.Section02.Centralizer MathieuCode.SextetLayers.CoordinateTransport
variable {G : Type*} [Group G] [Finite G]

/-- The original point commutator has its native sextet coordinates under
any compatible component marking, including the independently selected trio marking. -/
theorem marked_point_commutator_coordinates
    (W L : Subgroup G) [IsElementaryAbelian 2 W] (hWL : W ≤ L)
    (hLW : L ≤ normalizer (W : Set G))
    (q : L →* M24) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (z : W) (S : Sextet) (hz : F (Additive.ofMul z) = sextetVector S) :
    ∀ w : W, (w : G) ∈ commutatorSpace L W z ↔
      F (Additive.ofMul w) ∈ ⨆ B ∈ S.parts, supportedPairSpace B := by
  obtain ⟨c,hc,hck,hcval⟩ := marked_centralizer_action W L hLW q hq hk F hF z S hz
  obtain ⟨r,_,_,hcore,hrval⟩ := marked_residual_core_action L z S c hc hck
  let R := localResidual L z
  let X := localTwoCore L z
  have hRL : R ≤ L := (localResidual_le L z).trans inf_le_left
  let j : R →* L := inclusion hRL
  have he : (sextetStabilizer S).subtype.comp r = q.comp j := by
    apply MonoidHom.ext
    intro x
    exact (congrArg Subtype.val (hrval x)).trans (hcval _)
  have hX : X.subgroupOf L = (pCore 2 R).map j := by
    ext l
    change (l : G) ∈ (pCore 2 R).map R.subtype ↔ l ∈ (pCore 2 R).map j
    constructor
    · rintro ⟨x,hx,hxl⟩
      exact ⟨x,hx,Subtype.ext hxl⟩
    · rintro ⟨x,hx,hxl⟩
      exact ⟨x,hx,congrArg Subtype.val hxl⟩
  have hmap : (X.subgroupOf L).map q =
      (nativeTranslation S).range.map (sextetStabilizer S).subtype := by
    rw [hX,map_map,←he,←map_map,hcore,nativeQuotient_kernel]
  have htop : ((AddSubgroup.toZModSubmodule 2 (W.subgroupOf W).toAddSubgroup).map
      F.toLinearMap) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨w,rfl⟩ := F.surjective v
    exact ⟨w,w.toMul.property,rfl⟩
  intro w
  have hm := marked_commutator_mem W L hWL hLW q F hF X W
    ((localTwoCore_le L z).trans hRL) le_rfl w
  rw [htop,hmap,native_translation_moved] at hm
  exact hm

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
