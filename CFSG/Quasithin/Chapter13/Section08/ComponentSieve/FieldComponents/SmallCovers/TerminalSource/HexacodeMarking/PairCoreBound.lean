module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.ThreeDimensional
public import Theory.Representation.HexacodeAction.PairCore
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.CoreBound
public import Theory.GroupTheory.PCoreImage

/-!
# The upper bound for the original hexacode parabolic two-core

A faithful hexacode actor containing the even cover acts faithfully on the
coordinates of any two-subgroup. For a double-zero pair point, the cubic
scalar forces the stabilizer's two-core into the even cover. Its coordinate
image is normal in the entire even pair stabilizer and therefore has order
at most four. This removes the order assumption from the pair geometry;
the original critical rank supplies the opposite inequality.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
open Atlas.Codes Representation.Hexacode Subgroup
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm pairHom first second basePair)
variable {A : Type*} [Group A] [Finite A]

/-- A pair-point stabilizer has two-core of order at most four. -/
theorem pair_point_twoCore_card_le_four (e : A →* HexAutomorphisms)
    (hinj : Function.Injective e) (heven : hexSign.ker ≤ e.range)
    (D : Submodule F hexacode) (s : Pair)
    (hs : D.restrictScalars (ZMod 2) = zeroPairPlane s) :
    Nat.card ((pointStabilizer e D).pCoreIn 2) ≤ 4 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := pointStabilizer e D
  let Q := P.pCoreIn 2
  have hP (a : A) : a ∈ P ↔ pairPerm (coordinate e a) s = s := by
    change e a ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action (D.restrictScalars (ZMod 2)) ↔ _
    rw [hs]
    exact zeroPairPlane_stabilizer_iff (e a) s
  have hz : hexZ ∈ P.map e := by
    obtain ⟨a,ha⟩ := heven (show hexZ ∈ hexSign.ker from hexSign_Z)
    refine mem_map.mpr ⟨a, ?_, ha⟩
    change e a ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action (D.restrictScalars (ZMod 2))
    rw [ha]
    exact fieldPoint_scalar_mem D
  have hker : IsPGroup 2 e.ker := by
    rw [(MonoidHom.ker_eq_bot_iff e).mpr hinj]
    exact IsPGroup.of_bot
  have hmap : Q.map e = (P.map e).pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup e hker P
  have hQeven : Q.map e ≤ hexSign.ker := by
    rw [hmap]
    exact twoCore_le_even_of_scalar_mem (P.map e) hz
  have hcinj : Function.Injective ((coordinate e).comp Q.subtype) := by
    have hi := coordinate_injective_on_two_subgroup (Q.map e)
      ((isPGroup_pCoreIn 2 P).map e)
    intro a b hab
    apply Subtype.ext
    apply hinj
    have heq : (⟨e a.val,mem_map_of_mem e a.property⟩ : Q.map e) =
        ⟨e b.val,mem_map_of_mem e b.property⟩ := hi hab
    exact congrArg Subtype.val heq
  let R := Q.map (coordinate e)
  have hReven : R ≤ alternatingGroup (Fin 6) := by
    rintro g ⟨a,ha,rfl⟩
    exact hQeven (mem_map_of_mem e ha)
  have hRfix : ∀ g ∈ R, pairPerm g s = s := by
    rintro g ⟨a,ha,rfl⟩
    exact (hP a).mp (pCoreIn_le 2 P ha)
  have hPn : P ≤ normalizer (Q : Set A) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hRn : ∀ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 →
      pairPerm g s = s → ∀ x ∈ R, g * x * g⁻¹ ∈ R := by
    intro g hg hgfix x hx
    obtain ⟨a,ha⟩ := coordinate_coversAlternating e heven ⟨g,hg⟩
    change coordinate e a = g at ha
    have haP : a ∈ P := (hP a).mpr (ha ▸ hgfix)
    have hgn : g ∈ normalizer (R : Set (Equiv.Perm (Fin 6))) := by
      rw [←ha]
      exact Q.le_normalizer_map (coordinate e)
        (mem_map_of_mem (coordinate e) (hPn haP))
    exact (mem_normalizer_iff.mp hgn x).mp hx
  have hRi : Function.Injective ((coordinate e).subgroupMap Q) := by
    intro a b hab
    apply hcinj
    exact congrArg Subtype.val hab
  calc
    Nat.card Q = Nat.card R := Nat.card_congr
      (Equiv.ofBijective ((coordinate e).subgroupMap Q)
        ⟨hRi,(coordinate e).subgroupMap_surjective Q⟩)
    _ ≤ 4 := BinaryPermutation.SixPairsQuadratic.even_pair_normal_two_card_le_four
      s R ((isPGroup_pCoreIn 2 P).map (coordinate e)) hReven hRfix hRn
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
