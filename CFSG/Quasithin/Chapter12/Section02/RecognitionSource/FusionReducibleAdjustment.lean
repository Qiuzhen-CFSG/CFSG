module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAlternatingEight
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Adjusting the literal alternating-eight fusion pair

The permutation-core marking makes the constant word the unique nonzero
fixed vector. Under the original NoEscape and structural hypotheses it is
central in N_G(L), hence in T. The given Sylow of C_G(v) therefore also
centralizes vz. Sylow conjugacy adjusts the original outside transporter
to normalize that same Sylow image, preserving its being outside N_G(L).

The seed below is an intermediate geometric input, not a source hypothesis.
Its existence still requires reconstruction of the augmentation core, orbit
selection and the literal C_T(v) Sylow witness. The constructor proves the
fixed-line fields and the adjustment in the published AlternatingEightFusion;
it neither assumes nor proves the terminal omega-center containment.

Source: Aschbacher–Smith, 12.2.16, printed p.800, middle paragraph.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual core, selected pair and point Sylow before adjusting its transporter. -/
structure AlternatingEightFusionSeed (T : Sylow 2 G) (L V : Subgroup G) where
  groupEquiv : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)
  vectorEquiv : V ≃* Multiplicative (BinaryPermutation.core (Fin 8))
  intertwines : ∀ (l : L) (w : V),
    ((vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (vectorEquiv w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹
  v : V
  z : V
  weight_two : (Finset.univ.filter fun i : Fin 8 => (vectorEquiv v).toAdd.val i ≠ 0).card = 2
  constant : ∀ i : Fin 8, (vectorEquiv z).toAdd.val i = 1
  sylow : Sylow 2 (centralizer ({(v : G)} : Set G))
  sylow_image : (sylow : Subgroup (centralizer ({(v : G)} : Set G))).map
    (centralizer ({(v : G)} : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  g : G
  outside : g ∉ normalizer (L : Set G)
  conjugates : g * (v : G) * g⁻¹ = (v : G) * (z : G)

namespace AlternatingEightFusionSeed
variable (C : AlternatingEightFusionSeed T L V)

omit [Finite G] in
/-- The constant word is a nonidentity element of the original V. -/
theorem z_ne : (C.z : G) ≠ 1 := by
  intro he
  have he' : C.z = 1 := Subtype.ext he
  have hh := C.constant 0
  rw [he', map_one] at hh
  exact zero_ne_one hh

omit [Finite G] in
/-- The selected weight-two vector is nonidentity. -/
theorem v_ne : (C.v : G) ≠ 1 := by
  intro he
  have he' : C.v = 1 := Subtype.ext he
  have hh := C.weight_two
  rw [he', map_one] at hh
  norm_num at hh

omit [Finite G] in
/-- The actual L-action fixes the constant word. -/
theorem z_fixed : (C.z : G) ∈ centralizer (L : Set G) := by
  intro l hl
  have he := C.intertwines ⟨l,hl⟩ C.z
  have hf : BinaryPermutation.alternatingCoreRepresentation (Fin 8)
      (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
      (C.vectorEquiv C.z).toAdd = (C.vectorEquiv C.z).toAdd := by
    apply Subtype.ext
    funext i
    exact (C.constant _).trans (C.constant i).symm
  rw [hf, ofAdd_toAdd, C.vectorEquiv.symm_apply_apply] at he
  exact mul_inv_eq_iff_eq_mul.mp he.symm

omit [Finite G] in
/-- There are precisely two fixed vectors under the marked alternating action. -/
theorem fixed_line : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = (C.z : G) := by
  intro w hw hL
  let w' : V := ⟨w,hw⟩
  have hfixed : ∀ a : alternatingGroup (Fin 8),
      BinaryPermutation.coreRepresentation (Fin 8) a.val
        (C.vectorEquiv w').toAdd = (C.vectorEquiv w').toAdd := by
    intro a
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (C.groupEquiv.symm a)
    have ha : C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = a := by
      rw [hl, C.groupEquiv.apply_symm_apply]
    have he := C.intertwines l w'
    rw [ha] at he
    have hcomm : (l : G) * (w' : G) * (l : G)⁻¹ = (w' : G) :=
      mul_inv_eq_iff_eq_mul.mpr (hL l l.property)
    rw [hcomm] at he
    have he' := congrArg (fun x : V => (C.vectorEquiv x).toAdd) (Subtype.ext he)
    simpa only [C.vectorEquiv.apply_symm_apply, toAdd_ofAdd,
      BinaryPermutation.alternatingCoreRepresentation, MonoidHom.comp_apply,
      Subgroup.coe_subtype] using he'
  obtain ⟨c,hc⟩ := BinaryPermutation.mem_constants_iff _ |>.mp
    ((BinaryPermutation.core_fixed_iff_constant (by norm_num) _).mp hfixed)
  have htwo : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases htwo with rfl | rfl
  · left
    have he : C.vectorEquiv w' = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      exact hc i
    exact congrArg Subtype.val (C.vectorEquiv.map_eq_one_iff.mp he)
  · right
    apply congrArg (fun x : V => (x : G)) (show w' = C.z from ?_)
    apply C.vectorEquiv.injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact (hc i).trans (C.constant i).symm

include C in
/-- Construct the published configuration by adjusting the actual outside conjugator. -/
theorem exists_adjusted
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) :
    Nonempty (AlternatingEightFusion T L V) := by
  have hTz : (T : Subgroup G) ≤ centralizer ({(C.z : G)} : Set G) :=
    (structural G T L h).1.trans
      (normalizer_centralizes_fixed_line h D structural
        C.z.property C.z_ne C.z_fixed C.fixed_line)
  have hy : (C.sylow : Subgroup (centralizer ({(C.v : G)} : Set G))).map
      (centralizer ({(C.v : G)} : Set G)).subtype ≤
        centralizer ({(C.v : G) * (C.z : G)} : Set G) := by
    rw [C.sylow_image]
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    have hv := mem_centralizer_singleton_iff.mp ht.2
    have hz := mem_centralizer_singleton_iff.mp (hTz ht.1)
    calc
      t * ((C.v : G) * (C.z : G)) = (t * (C.v : G)) * (C.z : G) := (mul_assoc _ _ _).symm
      _ = ((C.v : G) * t) * (C.z : G) := by rw [hv]
      _ = (C.v : G) * ((C.z : G) * t) := by rw [mul_assoc, hz]
      _ = ((C.v : G) * (C.z : G)) * t := (mul_assoc _ _ _).symm
  obtain ⟨g,hg,he⟩ := exists_normalizer_conjugator_of_centralizer_sylow
    (C.v : G) ((C.v : G) * (C.z : G)) C.sylow hy
    (isConj_iff.mpr ⟨C.g,C.conjugates⟩)
  have hout : g ∉ normalizer (L : Set G) := by
    intro hm
    apply C.outside
    apply conjugator_mem_of_centralizer_le (hnone _ C.v.property C.v_ne)
    exact ⟨g,hm,he.trans C.conjugates.symm⟩
  refine ⟨{
    groupEquiv := C.groupEquiv
    vectorEquiv := C.vectorEquiv
    intertwines := C.intertwines
    v := C.v
    z := C.z
    weight_two := C.weight_two
    constant := C.constant
    z_ne := C.z_ne
    z_fixed := C.z_fixed
    fixed_line := C.fixed_line
    sylow := C.sylow
    sylow_image := C.sylow_image
    g := g
    outside := hout
    conjugates := he
    normalizes := ?_ }⟩
  rwa [C.sylow_image] at hg
end AlternatingEightFusionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
