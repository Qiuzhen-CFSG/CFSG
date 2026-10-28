module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.Perm.MaximalSubgroups
/-!
# Maximality of the native sextet stabilizer

Reuse the checked plane forest: each nontrivial root has 78 distinct entries.
Thus a strict overgroup of the sextet stabilizer has an orbit of at least 78
sextets and index at most 22. The faithful coset action of simple M24 excludes
that index because 23 divides its order. Transport gives every sextet stabilizer.
Only selected entries of the existing forest are checked; no new enumeration
is introduced. The sample certificate took 46.79 seconds including import
preparation and 2,261,712 KiB peak memory.

Source: Aschbacher–Segev (1991), §3 and (5.3)(2), p.600. This supplies the
point-side maximality used in the actual nonneighbor stabilizer argument.
-/
public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeSextets
private def samples : Fin 3 → Fin 78 → Fin 1771 :=
  ![![9,10,11,12,13,14,146,147,148,149,150,151,160,299,300,301,302,303,304,305,306,307,308,309,310,398,399,487,488,489,490,491,498,597,667,668,669,670,671,672,681,729,808,809,866,909,910,911,912,913,914,923,957,958,959,960,961,1037,1052,1053,1104,1179,1180,1181,1182,1186,1223,1276,1277,1278,1279,1307,1308,1348,1371,1430,1431,1432],
    ![1,2,3,4,5,6,7,8,15,16,17,18,35,36,37,38,63,68,70,71,72,73,97,103,111,118,123,125,126,127,128,129,167,172,188,194,203,207,210,211,212,235,236,244,247,251,259,261,267,271,277,281,289,292,295,296,297,298,311,312,313,314,329,344,345,365,368,373,393,402,410,429,432,439,445,449,452,460],
    ![19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,64,65,66,67,69,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,98,99,100,101,102,104,105,106,107,108]]
private theorem samples_root (r : Fin 3) (i : Fin 78) :
    (PlaneOrbit.row (samples r i)).root = r.succ := by
  revert r i; decide +kernel
private theorem samples_injective (r : Fin 3) : Function.Injective (samples r) := by
  revert r; decide +kernel

private theorem root_zero : PlaneOrbit.rootPlane 0 = standardSextet := by
  apply plane_parts_injective
  decide +kernel

private theorem strict_overgroup_orbit (K : Subgroup M24)
    (hK : sextetStabilizer standardSextet < K) :
    78 ≤ Nat.card (MulAction.orbit K standardSextet) := by
  obtain ⟨k,hkK,hk⟩ := SetLike.exists_of_lt hK
  obtain ⟨i,hi⟩ := PlaneOrbit.entry_surjective (k • standardSextet)
  let g := (PlaneOrbit.exists_transport i).choose
  have hg : (g : M24) • PlaneOrbit.rootPlane (PlaneOrbit.row i).root = k • standardSextet := hi
  have hr : (PlaneOrbit.row i).root ≠ 0 := by
    intro he
    rw [he,root_zero] at hg
    apply hk
    have hgfix : (g : M24) • standardSextet = standardSextet := plane_parts_injective g.property
    exact congrArg Sextet.parts (hg.symm.trans hgfix)
  let r : Fin 3 := ⟨(PlaneOrbit.row i).root.val - 1,by
    have hh := (PlaneOrbit.row i).root.isLt
    have hh0 : (PlaneOrbit.row i).root.val ≠ 0 := fun h => hr (Fin.ext h)
    omega⟩
  have hrs : r.succ = (PlaneOrbit.row i).root := by
    apply Fin.ext
    have hh0 : (PlaneOrbit.row i).root.val ≠ 0 := fun h => hr (Fin.ext h)
    simp only [Fin.val_succ,r]
    omega
  let f : Fin 78 → MulAction.orbit K standardSextet := fun j =>
    ⟨PlaneOrbit.entry (samples r j),by
      let b := (PlaneOrbit.exists_transport (samples r j)).choose
      refine ⟨⟨(b : M24)*(g : M24)⁻¹*k,
        K.mul_mem (K.mul_mem (hK.le b.property) (K.inv_mem (hK.le g.property))) hkK⟩,?_⟩
      change ((b : M24)*(g : M24)⁻¹*k) • standardSextet =
        (b : M24) • PlaneOrbit.rootPlane (PlaneOrbit.row (samples r j)).root
      rw [samples_root,hrs,mul_smul,mul_smul,←hg,inv_smul_smul]⟩
  have hf : Function.Injective f := by
    intro j l he
    exact samples_injective r (PlaneOrbit.entry_injective (congrArg Subtype.val he))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem standard_index : (sextetStabilizer standardSextet).index = 1771 := by
  have hc := (sextetStabilizer standardSextet).card_mul_index
  rw [SextetCore.stabilizer_card,m24_order] at hc
  omega

private theorem standard_maximal : IsCoatom (sextetStabilizer standardSextet) := by
  refine ⟨?_,?_⟩
  · intro he
    have hi := standard_index
    rw [he,index_top] at hi
    contradiction
  · intro K hK
    have hc := strict_overgroup_orbit K hK
    have he : MulAction.stabilizer K standardSextet = (sextetStabilizer standardSextet).subgroupOf K := by
      ext k
      exact ⟨fun hk => congrArg Sextet.parts hk,fun hk => plane_parts_injective hk⟩
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K standardSextet),he] at hc
    change 78 ≤ (sextetStabilizer standardSextet).relIndex K at hc
    have hi := relIndex_mul_index hK.le
    rw [standard_index] at hi
    have hb : K.index ≤ 22 := by nlinarith
    by_contra hn
    let := m24_isSimpleGroup
    have hd := (K.card_dvd_factorial_index_of_simple hn).trans (Nat.factorial_dvd_factorial hb)
    rw [m24_order] at hd
    norm_num [Nat.factorial] at hd

theorem sextet_maximal (S : Sextet) : IsCoatom (sextetStabilizer S) := by
  obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator S
  change IsCoatom (MulAction.stabilizer M24 S.parts)
  rw [←hg,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr standard_maximal
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeSextets
