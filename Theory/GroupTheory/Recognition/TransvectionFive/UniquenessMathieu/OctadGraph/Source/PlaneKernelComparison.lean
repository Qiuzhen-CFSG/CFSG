module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativePlaneGroup
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.GeneratedSystem

/-!
# The native plane map preserves the literal permutation kernel

The image of a normal cubic subgroup in S₆ is trivial: otherwise it contains
A₆, contradicting its order. Thus the source's specified cubic kernel maps
to the native hexacode cubic kernel under the full quotient comparison.
Pulling this identity back through the original quotient maps identifies
the kernel on the fifteen source plane points with the native tetrad kernel.

The final consumers supply this plane-group isomorphism on the literal
uniqueness systems and on the same oriented normalizer span obtained from
the original fusion hypothesis. Common-flag compatibility with the vertex
map is still required to construct a similarity.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1 and 41.4, pp.219–222.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open Atlas.Codes Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

private theorem normal_cubic_eq_hex_kernel (C : Subgroup HexAutomorphisms)
    [C.Normal] (hC : Nat.card C = 3) : C = hexCoordinateSixHom.ker := by
  let N := C.map hexCoordinateSixHom
  let : N.Normal := Normal.map inferInstance hexCoordinateSixHom hexCoordinateSix_surjective
  have hN : N = ⊥ := by
    by_contra hne
    have hnt : Nontrivial N := (nontrivial_iff_ne_bot _).mpr hne
    have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hnt
    have hd := (card_dvd_of_le hle).trans (C.card_map_dvd hexCoordinateSixHom)
    rw [hC,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  have hle : C ≤ hexCoordinateSixHom.ker := by
    intro g hg
    exact mem_bot.mp (hN ▸ (mem_map_of_mem hexCoordinateSixHom hg : hexCoordinateSixHom g ∈ N))
  apply eq_of_le_of_card_ge hle
  rw [hC,hexCoordinateSix_kernel,Nat.card_zpowers,hexZ_order]

variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

/-- The source's specified normal cubic subgroup is the native cubic kernel
under the full quotient comparison. -/
theorem threeSpaceHexQuotientEquiv_cubic :
    D.cubicKernel.map (threeSpaceHexQuotientEquiv F D).toMonoidHom =
      hexCoordinateSixHom.ker := by
  let := D.cubicKernel_normal
  let e := threeSpaceHexQuotientEquiv F D
  let : (D.cubicKernel.map e.toMonoidHom).Normal :=
    Normal.map inferInstance e.toMonoidHom e.surjective
  apply normal_cubic_eq_hex_kernel
  rw [card_map_of_injective e.injective,D.cubicKernel_card]

/-- The actual fifteen-point source action kernel maps to the native six-tetrad
kernel under every isomorphism retaining the proved quotient coordinates. -/
theorem native_plane_equiv_action_kernel
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (he : ∀ n, SextetCore.quotientHom (e n) =
      threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n)) :
    (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  have hmem (n : threeSpaceNormalizer F) :
      n ∈ (planePointAction F).ker ↔ e n ∈ SextetCore.columnHom.ker := by
    rw [planePointAction_kernel_eq F D]
    change QuotientGroup.mk n ∈ D.cubicKernel ↔
      hexCoordinateSixHom (SextetCore.quotientHom (e n)) = 1
    rw [he]
    change QuotientGroup.mk n ∈ D.cubicKernel ↔
      threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n) ∈ hexCoordinateSixHom.ker
    rw [← threeSpaceHexQuotientEquiv_cubic F D,mem_map_equiv,MulEquiv.symm_apply_apply]
  ext g
  rw [mem_map_equiv]
  simpa only [e.apply_symm_apply] using hmem (e.symm g)

/-- The constructed plane isomorphism retains every rectangle element,
the full quotient, and the literal kernel on plane points. -/
theorem exists_native_plane_equiv_action_kernel :
    ∃ e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet,
      (∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
        (M24ChapterHStabilizers.SextetAction.translationEquiv
          (threeSpaceHexCoordinates F a) : sextetStabilizer standardSextet)) ∧
      (∀ n, SextetCore.quotientHom (e n) = threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n)) ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  obtain ⟨e,hker,hq⟩ := exists_native_plane_equiv F D
  exact ⟨e,hker,hq,native_plane_equiv_action_kernel F D e hq⟩

/-- The plane component on the literal uniqueness systems, retaining its actual action kernel.
This supplies the local group map; agreement with the vertex map is still required. -/
theorem exists_native_local_equiv_action_kernel
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).H ≃* OctadGraph.system.H,
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  obtain ⟨e,_,_,hk⟩ := exists_native_plane_equiv_action_kernel F D
  exact ⟨e,hk⟩

/-- Original fusion gives an actual plane-group map for the same oriented source span,
with its plane-point action kernel matched to the native tetrad kernel. -/
theorem oriented_normalizerSpan_local_equiv_action_kernel (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    let U := normalizerSpan_system E.oriented.marking E.localData
    ∃ e : U.H ≃* OctadGraph.system.H,
      (planePointAction (normalizerSpanMarking E.oriented.marking)).ker.map e.toMonoidHom =
        SextetCore.columnHom.ker := by
  let E := SourceData.ofFusion F hfusion
  exact exists_native_local_equiv_action_kernel (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
