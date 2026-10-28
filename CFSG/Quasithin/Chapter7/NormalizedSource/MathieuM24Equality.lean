module
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.Classifications
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Coordinates
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.FixedSpace

/-!
# The canonical M24 cocode offender in the equality row

The native sextet kernel has full element-fixed-space span: eleven short
words in its established generators fix the eleven pair-coordinate vectors.
Their point actions and nonidentity are checked by the kernel. Thus H.14.1's
classification of elementary groups of order 64 leaves the trio kernel
whenever the fixed-space span is proper.

Both the group and module markings are transported to the literal ambient
automizer. The same native conjugator identifies its fixed space with the
actual affine-plane three-space, not only with a space of dimension three.
NonFFSourceMathieuM24Equality applies this to the original chosen offender.

Source: Aschbacher--Smith H.14.1, H.15.3(3), H.15.6(1) and 8.1.3,
printed pp.396,400--401,713, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open MathieuCode MathieuCode.CocodeOctad.Involutions
open CFSG.Quasithin.ChapterH.Section13To16
open scoped BigOperators IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuEquality
open CFSG.Quasithin.ChapterE

private def fixingWord : Fin 11 → List (Fin 6) :=
  ![[3],[1,4],[0,3,4],[1,4],[1],[0,5],[2,5],[0,3,4],[1,4],[2,5],[0]]
private def wordElement (w : List (Fin 6)) : M24 :=
  (w.map (EvenCandidates.generator 1)).prod
private theorem wordElement_apply (w : List (Fin 6)) (x : Fin 24) :
    (wordElement w).val x = EvenCandidates.evaluatePoint 1 w x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (EvenCandidates.generator 1 a).val ((wordElement w).val x) = _
    rw [EvenCandidates.generator_apply, ih]
    rfl
private theorem wordElement_mem (w : List (Fin 6)) :
    wordElement w ∈ EvenCandidates.elementary 1 := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
  exact EvenCandidates.generator_mem 1 a
private def fixingElement (j : Fin 11) : M24 :=
  (MulAut.conj transport) (wordElement (fixingWord j))
private def fixingPoint (j : Fin 11) (x : Fin 24) : Fin 24 :=
  transportPerm (EvenCandidates.evaluatePoint 1 (fixingWord j) (transportPerm.symm x))
private theorem fixingElement_apply (j : Fin 11) (x : Fin 24) :
    (fixingElement j).val x = fixingPoint j x := by
  change transportPerm ((wordElement (fixingWord j)).val (transportPerm.symm x)) = _
  rw [wordElement_apply]
  rfl
private theorem fixingElement_mem (j : Fin 11) :
    fixingElement j ∈ sextetKernel standardSextet := by
  change fixingElement j ∈ SextetCore.core
  rw [←sextetCandidate_eq_core]
  exact ⟨wordElement (fixingWord j),wordElement_mem _,rfl⟩
private theorem fixingElement_ne (j : Fin 11) : fixingElement j ≠ 1 := by
  intro he
  have hh := congrArg (fun g : M24 => g.val 0) he
  rw [fixingElement_apply] at hh
  exact (show ∀ j, fixingPoint j 0 ≠ 0 by decide +kernel) j hh
private theorem fixingElement_fixed (j : Fin 11) :
    cocodeRepresentation (fixingElement j) (codeInCore.mkQ (coordinateWord j)) =
      codeInCore.mkQ (coordinateWord j) := by
  rw [cocodeRepresentation_mk]
  congr 1
  apply Subtype.ext
  change fullRepresentation (fixingElement j)
      (Pi.single (nonpivot j) 1 + Pi.single 23 1) = _
  rw [map_add]
  have hs (g : M24) (i : Fin 24) :
      fullRepresentation g (Pi.single i 1) = Pi.single (g.val i) 1 := by
    ext k
    simp [fullRepresentation, BinaryPermutation.representation, Pi.single_apply, Equiv.symm_apply_eq]
  rw [hs,hs,fixingElement_apply,fixingElement_apply]
  exact (show ∀ j : Fin 11,
    (Pi.single (fixingPoint j (nonpivot j)) 1 + Pi.single (fixingPoint j 23) 1 : Full) =
      Pi.single (nonpivot j) 1 + Pi.single 23 1 by decide +kernel) j

/-- H.15.3(3) for the native sextet: the element fixed spaces span the entire cocode. -/
theorem sextet_fixedSpaceSpan :
    fixedSpaceSpan cocodeRepresentation (sextetKernel standardSextet) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨c,rfl⟩ := sectionMap_surjective v
  change (∑ j, c j • codeInCore.mkQ (coordinateWord j)) ∈ _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  apply fixedSpace_le_fixedSpaceSpan cocodeRepresentation (fixingElement_mem j) (fixingElement_ne j)
  exact (mem_fixedSpace_zpowers_iff _ _ _).mpr (fixingElement_fixed j)
/-- H.14.1 and the concrete fixed-span calculation identify a rank-six actor
with proper fixed-space span as an actual conjugate of the intrinsic trio kernel. -/
theorem rank_six_trio_of_fixedSpan_ne_top (A : Subgroup M24)
    (hA : IsElementaryAbelian 2 A) (hr : rank A = 6)
    (hspan : fixedSpaceSpan cocodeRepresentation A ≠ ⊤) :
    ∃ c : M24, A.map (MulAut.conj c).toMonoidHom =
      trioKernel PairOvergroups.standardTrio := by
  let := hA
  have hc : Nat.card A = 64 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hn6 : n = 6 := by simpa only [rank,hn,Nat.log_pow Nat.one_lt_two] using hr
    rw [hn,hn6]
    rfl
  obtain ⟨c,hS | hT⟩ := m24_large_elementary_fusion A hA (by omega : 32 ≤ Nat.card A)
  · have he : A.map (MulAut.conj c).toMonoidHom = sextetKernel standardSextet :=
      Subgroup.eq_of_le_of_card_ge hS (by
        rw [card_map_of_injective (MulAut.conj c).injective,hc,
          standardM24_large_kernel_structure.1.2.1])
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom c)
    have hmap := fixedSpaceSpan_map_equivariant cocodeRepresentation cocodeRepresentation
      (MulAut.conj c).toMonoidHom (MulAut.conj c).injective e (by
        intro b v
        change cocodeRepresentation c (cocodeRepresentation b v) =
          cocodeRepresentation (c*b*c⁻¹) (cocodeRepresentation c v)
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group) A
    rw [he,sextet_fixedSpaceSpan] at hmap
    exact (hspan ((Submodule.map_eq_top_iff (e := e)).mp hmap)).elim
  · exact ⟨c,Subgroup.eq_of_le_of_card_ge hT (by
      rw [card_map_of_injective (MulAut.conj c).injective,hc,trioKernel_card])⟩

/-- Transport from the literal internal action, including its E.3.30 core.
The group marking is preserved; the conclusion supplies its native conjugator. -/
theorem marked_rank_six_trio {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (a : Automizer W ≃* M24) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = cocodeRepresentation (a b) (E v))
    (I : Subgroup (Automizer W)) [IsElementaryAbelian 2 I]
    (hr : rank I = 6) (hcore : ChapterE.automizerDualCore W I 5 < W) :
    ∃ c : M24, (I.map a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
      trioKernel PairOvergroups.standardTrio := by
  apply rank_six_trio_of_fixedSpan_ne_top _ (IsElementaryAbelian.map a.toMonoidHom)
    (by rw [rank_map_injective a.toMonoidHom a.injective,hr])
  intro hspan
  have hm := fixedSpaceSpan_map_equivariant (automizerRepresentation W)
    cocodeRepresentation a.toMonoidHom a.injective E hE I
  rw [hspan] at hm
  have ht : fixedSpaceSpan (automizerRepresentation W) I = ⊤ :=
    (Submodule.map_eq_top_iff (e := E)).mp hm
  have he := Chapter7.automizerDualCore_eq_fixedSpaceSpan W I (by omega : 0 < rank I)
  rw [hr] at he
  have hamb : Chapter7.ambientSubmodule W ⊤ = W := by
    change ((Chapter7.moduleSubgroup W) ⊤).map W.subtype = W
    rw [(Chapter7.moduleSubgroup W).map_top, ←MonoidHom.range_eq_map, W.range_subtype]
  rw [show 6-1 = 5 from rfl,ht,hamb] at he
  exact (ne_of_lt hcore) he

/-- The same conjugator identifies the actual fixed space with the native
three-space of affine planes; this is stronger than a dimension equality. -/
theorem marked_trio_fixedSpace {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (a : Automizer W ≃* M24) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = cocodeRepresentation (a b) (E v))
    (I : Subgroup (Automizer W)) (c : M24)
    (hc : (I.map a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
      trioKernel PairOvergroups.standardTrio) :
    ((fixedSpace (automizerRepresentation W) I).map E.toLinearMap).map
        (cocodeRepresentation c) = TrioCalculation.standardPlaneMap.range ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation W) I) = 3 := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom c)
  have hm := fixedSpace_map_equivariant cocodeRepresentation cocodeRepresentation
    (MulAut.conj c).toMonoidHom e (by
      intro b v
      change cocodeRepresentation c (cocodeRepresentation b v) =
        cocodeRepresentation (c*b*c⁻¹) (cocodeRepresentation c v)
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      group) (I.map a.toMonoidHom)
  have he := fixedSpace_map_equivariant (automizerRepresentation W)
    cocodeRepresentation a.toMonoidHom E hE I
  rw [hc] at hm
  change (fixedSpace cocodeRepresentation (I.map a.toMonoidHom)).map
      (cocodeRepresentation c) = _ at hm
  have hplane : ((fixedSpace (automizerRepresentation W) I).map E.toLinearMap).map
      (cocodeRepresentation c) = TrioCalculation.standardPlaneMap.range := by
    rw [he,hm]
    exact TrioCalculation.standard_fixedSpace_eq_planeRange
  refine ⟨hplane,?_⟩
  calc
    Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation W) I) =
        Module.finrank (ZMod 2) ((fixedSpace (automizerRepresentation W) I).map E.toLinearMap) :=
      (E.finrank_map_eq _).symm
    _ = Module.finrank (ZMod 2) (((fixedSpace (automizerRepresentation W) I).map E.toLinearMap).map
        (cocodeRepresentation c)) := (e.finrank_map_eq _).symm
    _ = 3 := by rw [hplane]; exact TrioCalculation.finrank_standardPlaneMap_range

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuEquality
