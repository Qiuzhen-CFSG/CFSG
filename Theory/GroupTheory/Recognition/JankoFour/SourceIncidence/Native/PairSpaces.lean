module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.TrioRadicals
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.ConjugationTools

/-!
# Cocode pair spaces for the five native line labels

The intrinsic trio two-core generates the within-octad pair space. Transport
of the proved standard commutator calculation retains the actual M24 action.
For labels 2, 3 and 4, short paths in the union of the two octad partitions
express every even coordinate difference in the sum of the two pair spaces.
Only the three existing orbit representatives are checked; no catalogue is
re-enumerated. The combined probe took 35 seconds and about 2 GB peak memory.

Source: Aschbacher–Segev (1991), (5.4)(6), pp.600–601; the cocode
commutator calculation is Aschbacher–Smith H.15.6(1), p.401.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode MathieuCode.TrioCalculation Representation.BinaryOffender
open scoped Pointwise BigOperators Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativePairSpaces
open SourceCycleBase.Native NativeLineOrbit
noncomputable def pairSpace (l : Line) : Submodule (ZMod 2) Cocode :=
  ⨆ B ∈ l.parts, supportedPairSpace B

theorem pairSpace_transport (g : M24) (l : Line) {v : Cocode} (hv : v ∈ pairSpace l) :
    cocodeRepresentation g v ∈ pairSpace (g • l) := by
  have hh : pairSpace l ≤ (pairSpace (g • l)).comap (cocodeRepresentation g) := by
    refine iSup_le fun B => iSup_le fun hB => Submodule.span_le.mpr ?_
    rintro _ ⟨P,hP,rfl⟩
    change cocodeRepresentation g (pairVector P) ∈ pairSpace (g • l)
    rw [pairVector_equivariant]
    exact Submodule.mem_iSup_of_mem (g • B) (Submodule.mem_iSup_of_mem
      (Finset.mem_smul_finset.mpr ⟨B,hB,rfl⟩)
      (pairVector_mem_supportedPairSpace (mapPair g P) (Finset.smul_finset_subset_smul_finset hP)))
  exact hh hv

theorem pairSpace_map (g : M24) (l : Line) :
    (pairSpace l).map (cocodeRepresentation g) = pairSpace (g • l) := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩; exact pairSpace_transport g l hv
  · intro v hv
    refine ⟨cocodeRepresentation g⁻¹ v,?_,cocodeRepresentation.self_inv_apply g v⟩
    have hh := pairSpace_transport g⁻¹ (g • l) hv
    rw [inv_smul_smul] at hh
    exact hh

theorem pairSpace_eq_commutator (l : Line) : pairSpace l =
    subspaceCommutator cocodeRepresentation ⊤ (M24ChapterHStabilizers.TrioAction.coreAt l) := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M24 standardTrio l
  rw [←pairSpace_map,NativeTrioRadicals.core_smul,
    ←Representation.BinaryOffender.subspaceCommutator_top_map_conj]
  exact congrArg (fun U : Submodule (ZMod 2) Cocode => U.map (cocodeRepresentation g))
    standard_pairSpace_eq_twoCore_commutator

private def edge (r : Fin 5) (x y : Fin 24) : Prop :=
  (∃ j : Fin 3, x ∈ FarOrbit.support (standardMasks j) ∧ y ∈ FarOrbit.support (standardMasks j)) ∨
  (∃ j : Fin 3, x ∈ FarOrbit.support (rootMasks r j) ∧ y ∈ FarOrbit.support (rootMasks r j))
private instance (r : Fin 5) (x y : Fin 24) : Decidable (edge r x y) := inferInstanceAs (Decidable (_ ∨ _))

private theorem paths (r : Fin 5) (hr : 1 < r.val) (x : Fin 24) :
    ∃ y w : Fin 24, edge r x y ∧ edge r y w ∧ edge r w 0 := by
  revert r x
  decide +kernel

private def difference (x y : Fin 24) : Core :=
  ⟨Pi.single x 1 - Pi.single y 1,by
    change BinaryPermutation.augmentation (Fin 24) _ = 0
    rw [map_sub]
    simp [BinaryPermutation.augmentation]⟩

private theorem difference_add (x y w : Fin 24) :
    difference x y + difference y w = difference x w := by
  apply Subtype.ext
  exact sub_add_sub_cancel _ _ _

private theorem difference_pair (x y : Fin 24) (hne : x ≠ y) :
    codeInCore.mkQ (difference x y) = pairVector ⟨{x,y},by simp [hne]⟩ := by
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  funext i
  by_cases hx : i = x <;> by_cases hy : i = y <;>
    simp_all [difference,wordOfSet,Ne.symm hne]

private theorem difference_mem (l : Line) (B : Finset (Fin 24)) (hB : B ∈ l.parts)
    (x y : Fin 24) (hx : x ∈ B) (hy : y ∈ B) :
    codeInCore.mkQ (difference x y) ∈ pairSpace l := by
  by_cases he : x = y
  · subst y
    have hz : difference x x = 0 := Subtype.ext (sub_self _)
    rw [hz,map_zero]; exact Submodule.zero_mem _
  · rw [difference_pair x y he]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB
      (pairVector_mem_supportedPairSpace _ (by simpa only [Finset.insert_subset_iff,
        Finset.singleton_subset_iff] using And.intro hx hy)))

private theorem root_sum (r : Fin 5) (hr : 1 < r.val) :
    pairSpace standardTrio ⊔ pairSpace (rootLine r) = ⊤ := by
  have part (m : Fin 3 → BitVec 24) (j : Fin 3) :
      FarOrbit.support (m j) ∈ FarOrbit.parts m := by
    apply Finset.mem_image.mpr
    refine ⟨m j,?_,rfl⟩
    fin_cases j <;> simp [FarOrbit.maskParts]
  let U := pairSpace standardTrio ⊔ pairSpace (rootLine r)
  have he (x y : Fin 24) (hh : edge r x y) : codeInCore.mkQ (difference x y) ∈ U := by
    rcases hh with ⟨j,hx,hy⟩ | ⟨j,hx,hy⟩
    · exact Submodule.mem_sup_left (difference_mem standardTrio _ (standard_parts ▸ part standardMasks j) x y hx hy)
    · exact Submodule.mem_sup_right (difference_mem (rootLine r) _ ((root_parts r) ▸ part (rootMasks r) j) x y hx hy)
  have h0 (x : Fin 24) : codeInCore.mkQ (difference x 0) ∈ U := by
    obtain ⟨y,w,hxy,hyw,hw0⟩ := paths r hr x
    have hh := U.add_mem (U.add_mem (he x y hxy) (he y w hyw)) (he w 0 hw0)
    simpa only [←map_add,difference_add] using hh
  apply top_unique
  intro q _
  obtain ⟨v,rfl⟩ := codeInCore.mkQ_surjective q
  have hv : v = ∑ x : Fin 24, v.val x • difference x 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul,difference]
    change v.val = ∑ x : Fin 24, v.val x • (Pi.single x 1 - Pi.single 0 1)
    simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul]
    have hz : ∑ x, v.val x = 0 := v.property
    rw [hz,zero_smul,sub_zero]
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  rw [hv,map_sum]
  exact U.sum_mem (fun x _ => by rw [map_smul]; exact U.smul_mem _ (h0 x))

/-- For precisely the source labels greater than one, the two literal trio
pair spaces span the whole cocode. -/
theorem sup_eq_top (l m : Line) (i : Fin 5) (hi : 1 < i.val) (hm : Delta i l m) :
    pairSpace l ⊔ pairSpace m = ⊤ := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M24 standardTrio l
  have ht : Delta i standardTrio (g⁻¹ • m) := by
    simpa only [inv_smul_smul] using NativeOrbitals.delta_transport g⁻¹ i _ _ hm
  obtain ⟨k,hk,hkm⟩ := NativeLineOrbit.transitive standardTrio (rootLine i) (g⁻¹ • m) i
    ((root_delta_iff i i).mpr rfl) ht
  have hl : (g*k) • standardTrio = g • standardTrio := by rw [mul_smul,hk]
  have hm' : (g*k) • rootLine i = m := by rw [mul_smul,hkm,smul_inv_smul]
  rw [←hl,←hm',←pairSpace_map,←pairSpace_map,←Submodule.map_sup,root_sum i hi]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (fun v => ⟨cocodeRepresentation (g*k)⁻¹ v,
    cocodeRepresentation.self_inv_apply (g*k) v⟩)
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativePairSpaces
