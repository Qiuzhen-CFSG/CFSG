module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry.PermutationContract
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry.PermutationGeometry.Normalized
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# The marked pivot permutation geometry

Conjugate the supplied marking so that z becomes (01). The literal even
fusion subgroup is normalized by the centralizer of z, and its elementary
abelian structure makes every element commute with each such conjugate.
The normalized permutation calculation therefore places every nonidentity
b in the Klein four on the other four letters. It supplies the triple cycle
type of zb and generation by its centralizer together with that of z.

Both conclusions are transported back through the original marking and
then through the inclusion of S in G. This discharges the permutation input
of `nonempty_markedGeometry_of_square_roots_and_permutation_geometry`;
it does not use the independent square-root input of that assembly.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), proof of Lemma 4.8, p.41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

open Subgroup Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- Every nonidentity member of the literal even fusion four gives the
source's triple-transposition pivot and the two generating centralizers. -/
public theorem pivotPermutationGeometry (s : SymmetricSixData h a) (d : FusionEightData z) (b : G)
    (hb : b ∈ s.evenFusion z) (hb1 : b ≠ 1) : PivotPermutationGeometry s b := by
  let := d.elementary
  have bS := s.fusionCore_le_S hb.1
  let Z : s.S := ⟨z, s.z_mem⟩
  let B : s.S := ⟨b, bS⟩
  have tS : z * b ∈ s.S := s.S.mul_mem s.z_mem bS
  let T : s.S := ⟨z * b, tS⟩
  have hT : T = Z * B := rfl
  obtain ⟨i, j, hij, hmark⟩ := s.z_swap
  have hc : IsConj (s.equiv Z) PivotPermutations.base := by
    rw [show s.equiv Z = swap i j from hmark]
    exact isConj_swap hij (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  let e : s.S ≃* PivotPermutations.P := s.equiv.trans (MulAut.conj c)
  have hez : e Z = PivotPermutations.base := hc
  let q := e B
  have hq2 : q * q = 1 := by
    have hh : B * B = 1 := Subtype.ext (by
      change b * b = 1
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb.1)
    change e B * e B = 1
    rw [← map_mul, hh, map_one]
  have hcomm : b * z = z * b :=
    mem_centralizer_singleton_iff.mp (coreInG_le z (fusionCore_le z hb.1))
  have hqbase : q * PivotPermutations.base = PivotPermutations.base * q := by
    rw [← hez]
    change e B * e Z = e Z * e B
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hcomm)
  have hq1 : q ≠ 1 := fun hh => hb1 (congrArg Subtype.val (e.map_eq_one_iff.mp hh))
  have hqsign : sign q = 1 := by
    have hbsgn : sign (s.equiv B) = 1 := mem_alternatingGroup.mp
      ((s.mem_markedAlternating_iff b bS).mp hb.2)
    change sign (c * s.equiv B * c⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hbsgn]
    simp
  have hconj (g : PivotPermutations.P) (hg : g * PivotPermutations.base = PivotPermutations.base * g) :
      PivotPermutations.commutesConjugate q g := by
    let v : s.S := e.symm g
    have hv : v * Z = Z * v := e.injective (by
      simpa only [map_mul, hez, v, e.apply_symm_apply] using hg)
    have hvC : (v : G) ∈ Centralizer z := mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val hv)
    have hn : (v : G) ∈ normalizer (s.evenFusion z : Set G) :=
      (s.centralizer_le_relative_normalizer z ⟨v.property, hvC⟩).2
    have hconjb : (v : G) * b * (v : G)⁻¹ ∈ fusionCore z :=
      ((mem_normalizer_iff.mp hn b).mp hb).1
    have hbc : b * ((v : G) * b * (v : G)⁻¹) = ((v : G) * b * (v : G)⁻¹) * b :=
      congrArg Subtype.val (mul_comm (⟨b, hb.1⟩ : fusionCore z) ⟨_, hconjb⟩)
    have hi : B * (v * B * v⁻¹) = (v * B * v⁻¹) * B := Subtype.ext hbc
    have he := congrArg e hi
    simpa only [PivotPermutations.commutesConjugate, q, v, map_mul, map_inv, e.apply_symm_apply] using he
  obtain ⟨htype, hgen⟩ := PivotPermutations.normalized q hq2 hqbase hq1 hqsign hconj
  have het : e T = PivotPermutations.base * q := by rw [hT, map_mul, hez]
  have hgenS : centralizer ({Z} : Set s.S) ⊔ centralizer ({T} : Set s.S) = ⊤ :=
    PivotPermutations.generation_transport e Z T (by rw [hez, het]; exact hgen)
  refine ⟨tS, ?_, ?_⟩
  · rw [← het] at htype
    exact (cycleType_conj (σ := s.equiv T) (τ := c)).symm.trans htype
  · have hm := congrArg (Subgroup.map s.S.subtype) hgenS
    simpa only [Subgroup.map_sup, map_subtype_centralizer_singleton,
      ← MonoidHom.range_eq_map, range_subtype] using hm

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
