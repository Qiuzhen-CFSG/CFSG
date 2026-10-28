module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.ThreeDimensional
public import Theory.Representation.HexacodeAction.PairCore
public import Theory.GroupTheory.PCoreImage

/-!
# Intrinsic two-core lifts for a hexacode pair point

For a faithful actor containing the even hexacode cover, suppose its field
point is the double-zero plane of a pair and its point stabilizer has two-core
of order four. The scalar lies in the actual stabilizer image, forcing its
two-core into the even cover. The cubic coordinate kernel is disjoint from
this two-core. Its nontrivial coordinate image is normalized by the entire
even pair stabilizer, so after relabeling it contains both standard double
transpositions. Their image witnesses give lifts in the original two-core.

This discharges the two-core calculation in the alternative-section repair
of Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973). The double-zero-plane
hypothesis is explicit: the parent separately excludes full-weight points
and obtains this hypothesis from the field-point dichotomy.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
open Atlas.Codes Representation.Hexacode Subgroup
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm pairHom first second basePair)
variable {A : Type*} [Group A] [Finite A]

private theorem pair_conjugate_fix (r g : Equiv.Perm (Fin 6)) (s : Pair) :
    pairPerm (r * g * r⁻¹) (pairPerm r s) = pairPerm r s ↔ pairPerm g s = s := by
  change pairHom (r * g * r⁻¹) (pairHom r s) = pairHom r s ↔ _
  rw [map_mul, map_mul, map_inv]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
    Equiv.apply_eq_iff_eq]
  rfl

/-- After a coordinate relabeling, the actual two-core contains lifts of
`(01)(23)` and `(02)(13)`. No preferred pair position or core image is assumed. -/
theorem exists_pair_twoCore_lifts (e : A →* HexAutomorphisms)
    (hinj : Function.Injective e) (heven : hexSign.ker ≤ e.range)
    (D : Submodule F hexacode) (s : Pair)
    (hs : D.restrictScalars (ZMod 2) = zeroPairPlane s)
    (hcard : Nat.card ((pointStabilizer e D).pCoreIn 2) = 4) :
    ∃ (r : Equiv.Perm (Fin 6)) (a b : A),
      a ∈ (pointStabilizer e D).pCoreIn 2 ∧
      b ∈ (pointStabilizer e D).pCoreIn 2 ∧
      r * coordinate e a * r⁻¹ = first ∧
      r * coordinate e b * r⁻¹ = second := by
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
  obtain ⟨r,hr⟩ := BinaryPermutation.SixPairsQuadratic.exists_even_pair_transport s basePair
  let f : A →* Equiv.Perm (Fin 6) := (MulAut.conj r.val).toMonoidHom.comp (coordinate e)
  have hPf (a : A) : a ∈ P ↔ pairPerm (f a) basePair = basePair := by
    rw [hP a, ← hr]
    exact (pair_conjugate_fix r.val (coordinate e a) s).symm
  let T := Q.map f
  have hTeven : T ≤ alternatingGroup (Fin 6) := by
    rintro g ⟨a,ha,rfl⟩
    change Equiv.Perm.sign (r.val * coordinate e a * r.val⁻¹) = 1
    have hae : Equiv.Perm.sign (coordinate e a) = 1 :=
      hQeven (mem_map_of_mem e ha)
    rw [map_mul, map_mul, map_inv, hae, mul_one, mul_inv_cancel]
  have hTfix : ∀ g ∈ T, pairPerm g basePair = basePair := by
    rintro g ⟨a,ha,rfl⟩
    exact (hPf a).mp (pCoreIn_le 2 P ha)
  have hPn : P ≤ normalizer (Q : Set A) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hTnormal : ∀ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 →
      pairPerm g basePair = basePair → ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg hgfix x hx
    obtain ⟨a,ha⟩ := conjugate_coversAlternating (coordinate e)
      (coordinate_coversAlternating e heven) r.val ⟨g,hg⟩
    change f a = g at ha
    have haP : a ∈ P := (hPf a).mpr (ha ▸ hgfix)
    have hgn : g ∈ normalizer (T : Set (Equiv.Perm (Fin 6))) := by
      rw [← ha]
      exact Q.le_normalizer_map f (mem_map_of_mem f (hPn haP))
    exact (mem_normalizer_iff.mp hgn x).mp hx
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card ((pointStabilizer e D).pCoreIn 2)
    rw [hcard]
    decide)
  obtain ⟨x,hx⟩ := exists_ne (1 : Q)
  have hTne : ∃ g ∈ T, g ≠ 1 := by
    refine ⟨f x.val,mem_map_of_mem f x.property,?_⟩
    intro he
    apply hx
    apply hcinj
    apply (MulAut.conj r.val).injective
    change f x.val = (MulAut.conj r.val) ((coordinate e) (Q.subtype 1))
    simpa only [map_one] using he
  obtain ⟨hf,hs'⟩ := BinaryPermutation.SixPairsQuadratic.basePair_normal_contains_klein
    T hTeven hTfix hTnormal hTne
  obtain ⟨a,ha,haf⟩ := hf
  obtain ⟨b,hb,hbf⟩ := hs'
  exact ⟨r.val,a,b,ha,hb,haf,hbf⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
