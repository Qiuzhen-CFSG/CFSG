module
public import Theory.Mathieu.M22.Properties.LocalA5Placement.Quintet
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# Perfect normalizers of large elementary subgroups in Aut(M₂₂)

The actual outer Sylow has a unique elementary subgroup of order 32.
Its intersection with the native inner group is the quintet translation
sixteen. A perfect subgroup normalizing that intersection fixes its
four common points, and therefore lies in the literal natural actor of
order 960. Thus nine cannot divide the perfect subgroup's order.
The automorphism rank bound and Sylow conjugation extend this obstruction
to every elementary subgroup of order at least 32 in the full automorphism
group. All pair embeddings and the inner intersection are the original ones.

Source: Aschbacher--Smith H.14.3, p.397, and the M₂₂ exclusion in 12.6.12,
pp.825--826. The concrete geometry and licensed ATLAS calculations are
reused from the native ChapterHLocalClassification and LocalA5Placement.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22LargeElementary
open M22ChapterH M22ChapterH.Quintet

private theorem pair_inner_normal : m22ToPairStabilizer.range.Normal := by
  apply Subgroup.normal_of_index_eq_two
  have hinj : Function.Injective m22ToPairStabilizer :=
    fun _ _ h => m22Embedding_injective (congrArg Subtype.val h)
  have hc : Nat.card m22ToPairStabilizer.range = 443520 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm).trans m22_order
  have h := m22ToPairStabilizer.range.card_mul_index
  rw [hc, MathieuCode.m22PairStabilizer_card] at h
  omega

private theorem pair_card_le (E : Subgroup MathieuCode.m22PairStabilizer)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 32 := by
  let f := MathieuCode.m22PairStabilizerEquivAut.toMonoidHom
  have h := (primeRank_le_iff_elementary_card_le (MulAut M22)).mp
    m22_automorphism_twoRank_le_five (E.map f) (IsElementaryAbelian.map f)
  rwa [card_map_of_injective MathieuCode.m22PairStabilizerEquivAut.injective] at h

private theorem pair_no_perfect_large_elementary_normalizer
    (B E : Subgroup MathieuCode.m22PairStabilizer) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (hBE : B ≤ normalizer (E : Set MathieuCode.m22PairStabilizer))
    (hE : 32 ≤ Nat.card E) (h9 : 9 ∣ Nat.card B) : False := by
  have he : Nat.card E = 32 := Nat.le_antisymm (pair_card_le E) hE
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq MathieuCode.m22PairStabilizer S CompatibleSylow.outer
  let a := MulAut.conj g
  let U := E.map a.toMonoidHom
  let P := B.map a.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let : Group.IsPerfect P := Group.IsPerfect.map _
  have hUS : U ≤ CompatibleSylow.outer.toSubgroup := by
    have h := map_mono (f := a.toMonoidHom) hES
    change U ≤ (g • S : Sylow 2 MathieuCode.m22PairStabilizer) at h
    rwa [hg] at h
  have hU : U = Sextet.outerTranslations := CompatibleSylow.outer_card32 U inferInstance
    ((card_map_of_injective a.injective).trans he) hUS
  have hn : P ≤ normalizer (Sextet.outerTranslations : Set MathieuCode.m22PairStabilizer) := by
    rw [← hU]
    exact (map_mono (f := a.toMonoidHom) hBE).trans (le_normalizer_map a.toMonoidHom)
  let := pair_inner_normal
  have hN : P ≤ normalizer (innerTranslationGroup : Set MathieuCode.m22PairStabilizer) := by
    change P ≤ normalizer ((Sextet.outerTranslations ⊓ m22ToPairStabilizer.range :
      Subgroup MathieuCode.m22PairStabilizer) : Set MathieuCode.m22PairStabilizer)
    exact (le_inf hn (show P ≤ normalizer (m22ToPairStabilizer.range : Set MathieuCode.m22PairStabilizer) by
      rw [normalizer_eq_top]; exact le_top)).trans inf_normalizer_le_normalizer_inf
  have hd := (show 9 ∣ Nat.card P by rwa [card_map_of_injective a.injective]).trans
    (card_dvd_of_le (M22LocalA5Placement.perfect_normalizer_le_naturalActor P hN))
  rw [card_map_of_injective M22Quintet.Q.subtype_injective,
    M22LocalA5Placement.natural_actor_card] at hd
  norm_num at hd

/-- A perfect normalizer whose order is divisible by nine excludes every elementary subgroup of order at least 32. -/
theorem no_perfect_large_elementary_normalizer
    (B E : Subgroup (MulAut M22)) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (hBE : B ≤ normalizer (E : Set (MulAut M22)))
    (hE : 32 ≤ Nat.card E) (h9 : 9 ∣ Nat.card B) : False := by
  let e := MathieuCode.m22PairStabilizerEquivAut.symm
  let : Group.IsPerfect (B.map e.toMonoidHom) := Group.IsPerfect.map _
  let : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map _
  exact pair_no_perfect_large_elementary_normalizer (B.map e.toMonoidHom) (E.map e.toMonoidHom)
    ((map_mono (f := e.toMonoidHom) hBE).trans (le_normalizer_map e.toMonoidHom))
    (by rwa [card_map_of_injective e.injective])
    (by rwa [card_map_of_injective e.injective])
end Sporadic.Mathieu.M22LargeElementary
