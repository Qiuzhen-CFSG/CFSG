module
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds.NativeNormalizers
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect normalizers of large elementary subgroups in M₂₄

The native Sylow calculation puts every elementary subgroup of order at
least 64 in one of the two elementary groups of order 64. Its normalizer
is conjugate to a sextet or trio stabilizer. The sextet order is prime to
seven. Perfectness kills the trio quotient's S₃ coordinate, leaving a
map to SL₃(2) with two-group kernel, so nine cannot divide the perfect
subgroup's order. Neither case admits an order divisible by 63.

Source: Aschbacher–Smith H.14.1(1,5), pp.396–397; GLS3 Table 5.3e.
The non-A₅ point-component consumer uses the original moved image of
order at least 64 and the actual PSL₂(8) two-core quotient.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open M24LocalGeometry PairOvergroups PairOvergroups.QuotientConstruction

private theorem perfect_trio_nine_free
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (f : A →* trioStabilizer standardTrio) (hf : Function.Injective f) :
    ¬ 9 ∣ Nat.card A := by
  let q := (affineQuotient affineCoverage).comp f
  have hq : IsPGroup 2 q.ker :=
    (affineQuotient_kernel_isPGroup affineCoverage).comap_of_injective f hf
  let χ := (MonoidHom.fst (Equiv.Perm (Fin 3)) SL(3,ZMod 2)).comp q
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsPerfect χ.range := Group.IsPerfect.range χ
  have hs : Subsingleton χ.range := by
    by_contra! h
    exact Group.IsPerfect.not_isSolvable χ.range inferInstance
  let := hs
  have hχ (a : A) : χ a = 1 :=
    congrArg Subtype.val (Subsingleton.elim (χ.rangeRestrict a) 1)
  let r := (MonoidHom.snd (Equiv.Perm (Fin 3)) SL(3,ZMod 2)).comp q
  have hr : r.ker = q.ker := by
    ext a
    constructor
    · intro h
      exact Prod.ext (hχ a) h
    · intro h
      exact congrArg Prod.snd h
  have hp : IsPGroup 2 r.ker := hr.symm ▸ hq
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [←r.ker.card_mul_index,index_ker,hn]
  intro hd
  have h9 := ((by decide : Nat.Coprime 9 2).pow_right n).dvd_of_dvd_mul_left hd
  have hi := h9.trans r.range.card_subgroup_dvd_card
  rw [Matrix.PSL3Two.card_SL] at hi
  norm_num at hi

private theorem perfect_candidate_sixtythree_free (k : Fin 2)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (f : A →* EvenCandidates.localGroup k) (hf : Function.Injective f) :
    ¬ 63 ∣ Nat.card A := by
  fin_cases k
  · exact fun h => perfect_trio_nine_free
      (EvenCatalogue.NormalSeeds.trioNormalizerEquiv.toMonoidHom.comp f)
      (EvenCatalogue.NormalSeeds.trioNormalizerEquiv.injective.comp hf)
      ((by decide : 9 ∣ 63).trans h)
  · intro h
    have hd := (by decide : 7 ∣ 63).trans h
    have hi := hd.trans (Subgroup.card_dvd_of_injective
      (EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toMonoidHom.comp f)
      (EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.injective.comp hf))
    rw [SextetCore.stabilizer_card] at hi
    norm_num at hi

/-- A perfect normalizer of an elementary subgroup of order at least 64
cannot have an order divisible by 63 in the native Mathieu group. -/
theorem no_perfect_large_elementary_normalizer
    (B E : Subgroup M24) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (hBE : B ≤ normalizer (E : Set M24)) (hE : 64 ≤ Nat.card E)
    (h63 : 63 ∣ Nat.card B) : False := by
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  let a := MulAut.conj g
  let U := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
  have hUP : U ≤ SylowNormalizer.candidate := by
    have h := map_mono (f := a.toMonoidHom) hES
    change U ≤ (g • S : Sylow 2 M24) at h
    rw [hg] at h
    exact h
  have hU : 64 ≤ Nat.card U := by rwa [card_map_of_injective a.injective]
  have hcases : ∃ k : Fin 2, U = EvenCandidates.elementary k := by
    rcases large_elementary_le_candidate U (by omega) hUP with h | h | ⟨i,h⟩
    · exact ⟨0,eq_of_le_of_card_ge h (by rw [candidate_card]; exact hU)⟩
    · exact ⟨1,eq_of_le_of_card_ge h (by rw [candidate_card]; exact hU)⟩
    · have hc := (Subgroup.card_le_of_le h).trans (smallCandidate_card_le i)
      omega
  obtain ⟨k,hk⟩ := hcases
  have hBN : B.map a.toMonoidHom ≤ EvenCandidates.localGroup k := by
    have h := (map_mono (f := a.toMonoidHom) hBE).trans (le_normalizer_map a.toMonoidHom)
    change B.map a.toMonoidHom ≤ normalizer (U : Set M24) at h
    rw [hk] at h
    exact h
  let f : B →* EvenCandidates.localGroup k := (a.toMonoidHom.comp B.subtype).codRestrict _
    (fun b => hBN (mem_map_of_mem a.toMonoidHom b.property))
  have hf : Function.Injective f := fun b c h => Subtype.ext
    (a.injective (congrArg Subtype.val h))
  exact perfect_candidate_sixtythree_free k f hf h63
end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion

