module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreDegree
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure

/-!
# The size of the original prime-pair Sylow subgroup

The original moved reduced subgroup gives |O₂(L)| ≥ 2^(2n). The image
of T ∩ L in the literal PSL₂(2ⁿ) quotient is Sylow, of order 2ⁿ.
The quotient kernel is contained in T ∩ L, so multiplication of these
two orders gives |T ∩ L| ≥ 2^(3n).

The selected source S contains T ∩ L properly. Equality would make its
Cartan prime actor normalize S, contrary to the already proved original
common-normal argument. Hence |S| > 2^(3n). Any embedding into a finite
model must respect this bound through its Sylow two-subgroups.
The binary unitary exclusion is the immediate consumer of this bound.

Source: Aschbacher–Smith 5.2.2, printed p.647, using the original reduced
module and the E.2.13(4) constituent bound, p.225 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original two-core and its quotient Sylow contribute their separate two-parts. -/
theorem Input.left_sylow_card_lower_bound {κ : GroupClass}
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) :
    2 ^ (3*n) ≤ Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
  obtain ⟨hU,hUT,hlower⟩ := h.moved_reduced_size
  let := hU
  have hUC : ⁅W,L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 (⁅W,L⁆ : Subgroup G)) (hUT.trans inf_le_right)
      (normalizer_commutator_ge_right W L)
  have hcore : 2 ^ (2*n) ≤ Nat.card (pCore 2 L) := by
    have hc := hlower.trans (Nat.card_le_card_of_injective
      (inclusion hUC) (inclusion_injective hUC))
    simpa only [pCoreIn,card_map_of_injective L.subtype_injective] using hc
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  let q := QuotientGroup.mk' (pCore 2 L)
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : Nat.card Q = 2^n := by
    calc
      Nat.card Q = Nat.card Q' := Nat.card_congr
        ((Q : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _ = Nat.card F := (Nat.card_congr
        (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive Q').symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd)
      _ = 2^n := hF
  have hcP : pCore 2 L ≤ (P : Subgroup L) := pCore_isPGroup.le_sylow_of_normal P
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup L) (pCore 2 L)
    (P : Subgroup L) bot_le hcP
  simp only [relIndex_bot_left] at hmul
  have hi : (pCore 2 L).relIndex (P : Subgroup L) = Nat.card Q := by
    have hh := relIndex_ker (P : Subgroup L) q
    simpa only [q,QuotientGroup.ker_mk', Q, Sylow.coe_mapSurjective] using hh
  rw [hi,hQ] at hmul
  have hcardP : Nat.card P = Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
    rw [←card_map_of_injective (f := L.subtype) L.subtype_injective (K := (P : Subgroup L)),hP,
      subgroupOf_map_subtype]
  calc
    2 ^ (3*n) = 2^(2*n) * 2^n := by rw [←pow_add]; congr 1; omega
    _ ≤ Nat.card (pCore 2 L) * 2^n := Nat.mul_le_mul_right _ hcore
    _ = Nat.card P := hmul
    _ = _ := hcardP

namespace Prime

/-- Nonnormality under the prime actor forces S to be larger than the left Sylow intersection. -/
theorem LocalData.sourceS_card_gt
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    2 ^ (3*n) < Nat.card (Global.sourceS L H) := by
  have hle : (T : Subgroup G) ⊓ L ≤ Global.sourceS L H := by
    rw [←d.S_intersection_left]; exact inf_le_left
  have hlt : (T : Subgroup G) ⊓ L < Global.sourceS L H := by
    refine lt_of_le_of_ne hle ?_
    intro he
    apply d.prime_actor_not_normalizes_sourceS h hH hd
    rw [←he]
    exact hd.le_cartan.trans (c.left_le.trans inf_le_right)
  exact h.left_sylow_card_lower_bound.trans_lt (lt_of_not_ge
    (fun hh => hlt.ne (eq_of_le_of_card_ge hle hh)))

/-- The actual source S cannot embed in a group with a smaller Sylow two-subgroup. -/
theorem LocalData.sourceS_no_small_sylow_embedding
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    (hP : Nat.card P ≤ 2^(3*n))
    (f : Global.sourceS L H →* X) (hf : Function.Injective f) : False := by
  have hS := (T.isPGroup'.to_le
    (Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2))
  have hr : IsPGroup 2 f.range := hS.of_surjective _ f.rangeRestrict_surjective
  obtain ⟨Q,hQ⟩ := hr.exists_le_sylow
  have hbound : Nat.card (Global.sourceS L H) ≤ Nat.card P := calc
    _ = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    _ ≤ Nat.card Q := Nat.card_le_card_of_injective (inclusion hQ) (inclusion_injective hQ)
    _ = Nat.card P := Nat.card_congr (Q.equiv P).toEquiv
  exact (not_lt_of_ge (hbound.trans hP)) (d.sourceS_card_gt h hH c hd)

end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
