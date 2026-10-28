module
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.InvolutionGeometry
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic
public import Theory.ElementaryAbelian.Injective

/-!
# Two-rank of the native Hall–Janko automorphism group

An inner elementary subgroup of rank at least three contains a conjugate
of the noncentral involution. Its centralizer has order 240, so the elementary
subgroup has rank at most four. The existing literal outer Sylow calculation
bounds every elementary subgroup containing an outer element by eight elements.
Transport through the proved permutation-extension identification gives
`primeRank 2 (MulAut Carrier) ≤ 4` without module-recognition hypotheses.

The native involution-actor calculations currently live in Chapter K, so this
extension stays with those dependencies. It supplies the rank input to the
J₂ quadratic-ratio degree bound in the A₅ terminal argument of 13.6.
Source: Aschbacher–Smith K.4.5, printed p.460, and 13.6.6, printed p.927.
The imported native permutation certificates retain their ATLAS attribution.
-/

public section
namespace Sporadic.LeechRelated.J2
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ExceptionalParabolics GeneratorPair InnerInvolutionCores

/-- Elementary subgroups of the Hall--Janko carrier have order at most sixteen. -/
theorem carrier_elementary_card_le_sixteen (A : Subgroup Carrier)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 16 := by
  classical
  let := hA
  by_cases hbot : A = ⊥
  · subst A
    simp
  have hAt : IsElementaryTwo A := ⟨hbot, hA⟩
  suffices hr : rank A ≤ 4 by
    rw [hAt.card_eq_two_pow_rank]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr).trans_eq (by decide)
  by_contra! hr
  obtain ⟨x, hx, ht⟩ := CFSG.Quasithin.ChapterK.JankoTwo.exists_noncentral_involution
    A hAt (by omega)
  obtain ⟨g, rfl⟩ := isConj_iff.mp ht
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : IsElementaryTwo B := hAt.map_conj g⁻¹
  let : IsElementaryAbelian 2 B := hB.2
  have ha : a ∈ B := by
    convert mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx using 1
    simp [mul_assoc]
  have hBC : B ≤ centralizer ({a} : Set Carrier) := by
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : B) ⟨a, ha⟩)
  have hcard : Nat.card (centralizer ({a} : Set Carrier)) = 240 := by
    rw [Nat.card_congr a_centralizer_equiv.toEquiv, Nat.card_prod,
      nat_card_alternatingGroup, Nat.card_fin]
    norm_num [E4, C2, Nat.card_fun, Nat.factorial]
  have hd := card_dvd_of_le hBC
  rw [hB.card_eq_two_pow_rank, hcard, show rank B = rank A from rank_map_conj A g⁻¹] at hd
  have hp : 2 ^ 5 ∣ 2 ^ rank A := pow_dvd_pow 2 (by omega)
  have hf : 32 ∣ 240 := hp.trans hd
  norm_num at hf

/-- The same bound holds in the literal full permutation extension. -/
theorem extension_elementary_card_le_sixteen (A : Subgroup Extension)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 16 := by
  classical
  let := hA
  by_cases hinner : A ≤ intoExtension.range
  · let B := A.comap intoExtension
    have hB : IsElementaryAbelian 2 B :=
      IsElementaryAbelian.comap_of_injective intoExtension
        SecondParabolic.intoExtension_injective A
    have he : B.map intoExtension = A := map_comap_eq_self hinner
    rw [← he, card_map_of_injective SecondParabolic.intoExtension_injective]
    exact carrier_elementary_card_le_sixteen B hB
  · obtain ⟨x, hx, hout⟩ := Set.not_subset.mp hinner
    exact (CFSG.Quasithin.ChapterK.JankoTwo.outer_elementary_card_le A hA x hx hout).trans
      (by decide)

/-- The native full automorphism group of J₂ has two-rank at most four. -/
theorem automorphism_primeRank_le_four : primeRank 2 (MulAut Carrier) ≤ 4 := by
  rw [← primeRank_equiv 2 extensionEquivAut]
  exact (primeRank_le_iff_elementary_card_le Extension).mpr
    extension_elementary_card_le_sixteen

end Sporadic.LeechRelated.J2
