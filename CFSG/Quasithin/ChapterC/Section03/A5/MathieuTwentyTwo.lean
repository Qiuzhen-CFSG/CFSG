module
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyTwoReduction
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Action

/-!
# The native M22 obstruction for the original alternating-five block

The intrinsic core reduction leaves the quintet case. Its genuine natural
SL2(4) actor contains a cubic whose action on the core fixes no nonzero
vector. Source normalizer control makes that same element normalize the
original block. The existing normalizer action then realizes it as a
permutation of five letters. Such a cubic fixes two letters, and their
pair vector is a nonzero fixed vector in the actual augmentation core.

The contradiction uses the literal quintet inclusion and native conjugation
coordinates. No full quintet-normalizer classification is required. The
last theorem transports the result to the original source group under its
specified M22 isomorphism, retaining both the block and its characteristic U.

Source: Aschbacher--Smith C.1.13(c), printed pp.124--125, H.14.3(1--2),
printed p.397, and the deleted-five branch of 13.5.15, printed p.921.
-/

public section

open Subgroup BinaryPermutation
open CFSG.Quasithin.ChapterC

private theorem five_core_cubic_fixed (p : Equiv.Perm (Fin 5)) (hp : p ^ 3 = 1) :
    ∃ v : core (Fin 5), v ≠ 0 ∧ coreRepresentation (Fin 5) p v = v := by
  have hpair : ∀ p : Equiv.Perm (Fin 5), p ^ 3 = 1 →
      ∃ i j : Fin 5, i ≠ j ∧ p i = i ∧ p j = j := by decide +kernel
  obtain ⟨i,j,hij,hi,hj⟩ := hpair p hp
  let v : core (Fin 5) := ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
  refine ⟨v, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun w : core (Fin 5) => w.val i) h
    simp [v, hij] at hh
  · apply Subtype.ext
    ext k
    change (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) (p.symm k) =
      (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) k
    simp [Pi.single_apply, Equiv.symm_apply_eq, hi, hj]

namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] {A : Subgroup G}

/-- An actual alternating-five block cannot have a fixed-point-free cubic action in its normalizer. -/
theorem IsAlternatingBlock.no_fixedFree_cubic_in_normalizer (hA : IsAlternatingBlock A 5)
    (g : G) (hg : g ∈ normalizer (A : Set G))
    (f : MulAut ((blockU A).map A.subtype)) (hf3 : f ^ 3 = 1)
    (hfixed : ∀ v, f v = v → v = 1)
    (hact : ∀ v, (f v : G) = g * (v : G) * g⁻¹) : False := by
  let H := normalizer (A : Set G)
  obtain ⟨q,e,hq,_,he⟩ := Section05.BlockAnalysis.AlternatingSetup.exists_action
    hA A.le_normalizer (le_rfl : H ≤ normalizer (A : Set G))
  have hp3 : (q ⟨g,hg⟩) ^ 3 = 1 := by
    rw [←map_pow, ←MonoidHom.mem_ker, hq]
    apply mem_centralizer_iff.mpr
    intro v hv
    have hf := congrArg Subtype.val (DFunLike.congr_fun hf3 ⟨v,hv⟩)
    change (f (f (f ⟨v,hv⟩)) : G) = v at hf
    rw [hact,hact,hact] at hf
    have hc : g ^ 3 * v * (g ^ 3)⁻¹ = v := by
      calc
        g ^ 3 * v * (g ^ 3)⁻¹ = g * (g * (g * v * g⁻¹) * g⁻¹) * g⁻¹ := by simp [pow_succ, mul_assoc]
        _ = v := hf
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  obtain ⟨v,hv,hpv⟩ := five_core_cubic_fixed (q ⟨g,hg⟩) hp3
  let u : (blockU A).map A.subtype := e.symm (Multiplicative.ofAdd v)
  have hu : f u = u := by
    apply Subtype.ext
    rw [hact]
    rw [←he ⟨g,hg⟩ u]
    change (e.symm (Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (q ⟨g,hg⟩) (e (e.symm (Multiplicative.ofAdd v))).toAdd)) : G) = _
    rw [e.apply_symm_apply]
    change (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q ⟨g,hg⟩) v)) : G) = _
    rw [hpv]
  have hz : Multiplicative.ofAdd v = 1 := by
    calc
      Multiplicative.ofAdd v = e u := (e.apply_symm_apply _).symm
      _ = e 1 := congrArg e (hfixed _ hu)
      _ = 1 := e.map_one
  exact hv hz
end CFSG.Quasithin.ChapterC
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
open Representation.SL2FourNatural
open MathieuCode.M22Quintet.CocodeTransfer
namespace CFSG.Quasithin.ChapterC

private theorem native_m22_no_standard_quintet_alternatingFive
    (A : Subgroup M22) (hA : IsAlternatingBlock A 5)
    (hU : (blockU A).map A.subtype = m22InnerQuintetKernel m22SourceSextet)
    (hctrl : normalizer ((blockU A).map A.subtype : Set M22) ≤
      normalizer (A : Set M22)) : False := by
  let E := m22InnerQuintetKernel m22SourceSextet
  let j := m22ToPairStabilizer
  have hj : Function.Injective j := by
    intro x y h
    apply m22Embedding_injective
    exact congrArg Subtype.val h
  obtain ⟨q,hq⟩ := M22ChapterH.Quintet.naturalActorModelEquiv.surjective PointCommutator.cubic
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective M22ChapterH.Quintet.naturalActorTranslations q
  have hm : M22ChapterH.Quintet.naturalActorModelEquiv (QuotientGroup.mk a) =
      PointCommutator.cubic := (congrArg M22ChapterH.Quintet.naturalActorModelEquiv ha).trans hq
  obtain ⟨g,hg⟩ := M22ChapterH.Quintet.naturalActor_inner a
  have hmap : E.map j = A0 := M22ChapterH.inner_quintet_map_pair
  have hmem (x : M22) : j x ∈ A0 ↔ x ∈ E := by
    rw [←hmap]
    exact mem_map_iff_mem hj
  have hng : g ∈ normalizer (E : Set M22) := by
    apply mem_normalizer_iff.mpr
    intro x
    rw [←hmem, ←hmem, map_mul, map_mul, map_inv, hg]
    exact mem_normalizer_iff.mp
      (M22ChapterH.Quintet.innerIntersection_normalizer a.val.property) (j x)
  have hngU : g ∈ normalizer ((blockU A).map A.subtype : Set M22) := by simpa only [hU] using hng
  let e : (blockU A).map A.subtype ≃* Multiplicative V :=
    (MulEquiv.subgroupCongr hU).trans (M22ChapterH.Quintet.innerCoreGroupEquiv.trans
      M22ChapterH.Quintet.innerCoreNaturalEquiv.toAddEquiv.toMultiplicativeRight)
  let f0 : MulAut (Multiplicative V) :=
    (action PointCommutator.cubic).toAddEquiv.toMultiplicative
  let f : MulAut ((blockU A).map A.subtype) := MulAut.congr e.symm f0
  have hf_apply (v : (blockU A).map A.subtype) : f v = e.symm (f0 (e v)) := by
    simp only [f, MulAut.congr, MulEquiv.symm_symm]
    rfl
  have hf03 : f0 ^ 3 = 1 := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    have hp : (action PointCommutator.cubic) ^ 3 = 1 := by
      rw [←map_pow, PointCommutator.cubic_pow_three, map_one]
    exact DFunLike.congr_fun hp v.toAdd
  apply hA.no_fixedFree_cubic_in_normalizer g (hctrl hngU) f
  · rw [←map_pow, hf03, map_one]
  · intro v hv
    have hv' : action PointCommutator.cubic (e v).toAdd = (e v).toAdd := by
      rw [hf_apply] at hv
      have hh := congrArg e hv
      rw [e.apply_symm_apply] at hh
      exact congrArg Multiplicative.toAdd hh
    have ho : orderOf PointCommutator.cubic = 3 :=
      orderOf_eq_prime PointCommutator.cubic_pow_three (by decide +kernel)
    have hz := Matrix.SL2.cubic_fixed_eq_zero PointCommutator.cubic ho (e v).toAdd hv'
    apply e.injective
    rw [e.map_one]
    exact Multiplicative.toAdd.injective hz
  · intro v
    let w : Additive A0 := Additive.ofMul
      (M22ChapterH.Quintet.innerCoreGroupEquiv ((MulEquiv.subgroupCongr hU) v))
    let v' : (blockU A).map A.subtype :=
      ⟨g * (v : M22) * g⁻¹, (mem_normalizer_iff.mp hngU _).mp v.property⟩
    have hw : Additive.ofMul
        (M22ChapterH.Quintet.innerCoreGroupEquiv ((MulEquiv.subgroupCongr hU) v')) =
        innerConjugation M22ChapterH.Quintet.innerInputs a.val w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change j (g * (v : M22) * g⁻¹) = a.val.val * j v * a.val.val⁻¹
      rw [map_mul, map_mul, map_inv, hg]
    have he : e v' = f0 (e v) := by
      apply Multiplicative.toAdd.injective
      change M22ChapterH.Quintet.innerCoreNaturalEquiv (Additive.ofMul
        (M22ChapterH.Quintet.innerCoreGroupEquiv ((MulEquiv.subgroupCongr hU) v'))) =
        action PointCommutator.cubic (M22ChapterH.Quintet.innerCoreNaturalEquiv w)
      rw [hw, M22ChapterH.Quintet.innerCore_natural, hm]
    rw [hf_apply, ←he, e.symm_apply_apply]

/-- The native quintet natural actor excludes the last intrinsic core. -/
theorem native_m22_no_normalized_alternatingFive
    (A : Subgroup M22) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hctrl : normalizer ((blockU A).map A.subtype : Set M22) ≤
      normalizer (A : Set M22)) : False := by
  obtain ⟨g,hg⟩ := native_m22_normalized_alternatingFive_quintet_core A hA hc hctrl
  let e := MulAut.conj g⁻¹
  let B := A.map e.toMonoidHom
  let a : A ≃* B := e.subgroupMap A
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a hA
  have hU : (blockU B).map B.subtype = ((blockU A).map A.subtype).map e.toMonoidHom := by
    rw [← RankOne.Solvable.blockU_map_equiv a, map_map, map_map]
    rfl
  apply native_m22_no_standard_quintet_alternatingFive B hB
  · rw [hU, hg, map_map]
    have he : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id M22 := by
      ext x
      simp [e, MulAut.conj_apply, mul_assoc]
    rw [he, map_id]
  · rw [hU, ←map_equiv_normalizer_eq]
    exact (map_mono hctrl).trans (map_equiv_normalizer_eq A e).le

/-- The source group and block retain their original carriers under the specified model marking. -/
theorem no_normalized_alternatingFive_of_m22_equiv
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* M22) (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hctrl : normalizer ((blockU A).map A.subtype : Set G) ≤ normalizer (A : Set G)) : False := by
  let B := A.map e.toMonoidHom
  let a : A ≃* B := e.subgroupMap A
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a hA
  have hU : (blockU B).map B.subtype = ((blockU A).map A.subtype).map e.toMonoidHom := by
    rw [← RankOne.Solvable.blockU_map_equiv a, map_map, map_map]
    rfl
  apply native_m22_no_normalized_alternatingFive B hB
  · rw [hU, ←hc]
    exact (Nat.card_congr (e.subgroupMap ((blockU A).map A.subtype)).toEquiv).symm
  · rw [hU, ←map_equiv_normalizer_eq]
    exact (map_mono hctrl).trans (map_equiv_normalizer_eq A e).le

end CFSG.Quasithin.ChapterC
