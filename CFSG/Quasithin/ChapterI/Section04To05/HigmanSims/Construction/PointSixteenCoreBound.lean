module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreElementaryBound
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedConjugateTypes
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.EightQuotientRank
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreSeedCoverage

/-!
# The actual point-core intersections of an elementary sixteen

The marked S5 quotient bounds the image of an elementary sixteen by four.
The original point core contains no elementary subgroup larger than eight.
Consequently the literal intersection has order four or eight. This is the
local size input for the reciprocal-incidence calculation on the sixteen.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- An elementary sixteen containing the marked involution meets its
original whole point core in order four or eight. -/
theorem TypeAt.elementary_sixteen_core_intersection_card (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hzA : z ∈ A) :
    Nat.card (A ⊓ (involutionCentralizer z).pCoreIn 2 : Subgroup G) = 4 ∨
      Nat.card (A ⊓ (involutionCentralizer z).pCoreIn 2 : Subgroup G) = 8 := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  have hAH : A ≤ H := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha hzA)
  let AH := A.subgroupOf H
  let : IsElementaryAbelian 2 AH := IsElementaryAbelian.subgroupOf hAH
  obtain ⟨e⟩ := h.centralizer_quotient
  let f : H →* Equiv.Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (localCore z))
  have hk : f.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (localCore z) x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    change (x : H ⧸ localCore z) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, h.centralizer_fitting]
  let B := AH.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB : Nat.card B ≤ 4 :=
    (primeRank_le_iff_elementary_card_le (Equiv.Perm (Fin 5))).mp
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two B inferInstance
  have hcap : Nat.card (AH ⊓ f.ker : Subgroup H) = Nat.card (A ⊓ Q : Subgroup G) := by
    rw [← card_subtype H (AH ⊓ f.ker), map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hAH, hk]
    rfl
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map AH f
  rw [hcap, Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv, hA] at hprod
  have hlow : 4 ≤ Nat.card (A ⊓ Q : Subgroup G) := by
    change Nat.card (A ⊓ Q : Subgroup G) * Nat.card B = 16 at hprod
    nlinarith
  let D := (A ⊓ Q : Subgroup G).subgroupOf Q
  let j : D →* A := {
    toFun x := ⟨x, x.property.1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) he
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective j hj
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)
  have hbound := hs.elementary_card_le_eight D inferInstance
  have hDc : Nat.card D = Nat.card (A ⊓ Q : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ Q ≤ Q from inf_le_right)).toEquiv
  rw [hDc] at hbound
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_card_eq
  rw [hDc] at hn
  have hnle : n ≤ 3 := by
    by_contra hn4
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ n by omega)
    rw [← hn] at hh
    change 16 ≤ Nat.card (A ⊓ Q : Subgroup G) at hh
    omega
  change Nat.card (A ⊓ Q : Subgroup G) = 4 ∨ Nat.card (A ⊓ Q : Subgroup G) = 8
  rw [hn] at hlow hbound ⊢
  interval_cases n <;> simp_all only [Nat.reducePow, Nat.reduceLeDiff, or_true, true_or, le_refl]

/-- The same literal intersection bound holds at every point in the original
marked involution class, using its actual conjugate seed and full local type. -/
theorem TypeAt.elementary_sixteen_conjugate_point_core_card (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (x : G) (hxA : x ∈ A) (hx : IsConj x z) :
    Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 4 ∨
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8 := by
  obtain ⟨W, hw⟩ := h.exists_typeAt_of_isConj x hx
  exact hw.elementary_sixteen_core_intersection_card A hA hxA

/-- Membership in the original point cores is reciprocal on the original
marked conjugacy class. Both cores are the literal ambient local cores. -/
theorem TypeAt.conjugate_point_core_reciprocal (h : TypeAt z V)
    (x y : G) (hx : IsConj x z) (hy : IsConj y z) :
    y ∈ (involutionCentralizer x).pCoreIn 2 ↔
      x ∈ (involutionCentralizer y).pCoreIn 2 := by
  obtain ⟨X, hxT⟩ := h.exists_typeAt_of_isConj x hx
  obtain ⟨Y, hyT⟩ := h.exists_typeAt_of_isConj y hy
  exact ⟨fun hyQ => hxT.centralizer_core_involution_reciprocal y hyQ hyT.involution,
    fun hxQ => hyT.centralizer_core_involution_reciprocal x hxQ hxT.involution⟩

end CFSG.Quasithin.HigmanSims
