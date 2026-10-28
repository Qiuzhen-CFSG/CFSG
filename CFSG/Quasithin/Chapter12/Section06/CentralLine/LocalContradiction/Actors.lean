module

public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
public import Theory.Representation.BinaryPermutation.FiveQuadraticActors
public import Theory.Representation.BinaryPermutation.EightTransvectionActors
public import Theory.LinearAlgebra.DisplacementFiltration
public import Theory.ElementaryAbelian.Quotient

/-!
# The local actor contradiction in the fixed-space elimination

For the actual source span V_H=⟨Zᴴ⟩, an elementary conjugate A=Vᵍ has
image of order at most four in the marked H/C_H(V_H). The source r≥4 bound
makes V_H normalize A, so A acts quadratically on V_H. An embedded A₅
permutation core then forces that same quotient image to have order at most
two. In the seven-dimensional core action on A, the resulting group of
transvections has order at most two. This bounds |V_H:C_{V_H}(A)| by two,
contradicting the displacement of a nonidentity actor on the A₅ summand.

All actions are ambient conjugation, and the local quotient is the original
kernel quotient. The five-point summand only intertwines A; it need not be
invariant under all of H. No rank-one or centralizer-index witness is assumed.

This finishes the local action comparison in Lemma 12.6.23, conditional on
the preceding source geometry and markings. Constructing the local structure,
its A₅ summand, the core marking and r≥4 remains with the source assembly of
qt-d-12634-central. This module does not assert C_V(L)=1 or Theorem 12.6.2.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.6.23, printed p.830.
-/

public section

open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
variable {G : Type*} [Group G] [Finite G]

/-- On the seven-dimensional core, a group of transvections has at most
one nonidentity actor. The two centralizer indices refer to the original
ambient subgroups. -/
theorem core_centralizer_index_le_two {A U : Subgroup G}
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 U]
    (hn : U ≤ normalizer (A : Set G))
    (e : Additive A ≃ₗ[ZMod 2] core (Fin 8))
    (β : U →* Equiv.Perm (Fin 8))
    (he : ∀ u a, e (seedRepresentation U A hn u a) =
      coreRepresentation (Fin 8) (β u) (e a))
    (hi : (centralizer (U : Set G)).relIndex A ≤ 2) :
    (centralizer (A : Set G)).relIndex U ≤ 2 := by
  have hker : β.ker = (centralizer (A : Set G)).subgroupOf U := by
    rw [← conjugation_ker U A hn]
    ext u
    change β u = 1 ↔ conjugation U A hn u = 1
    constructor
    · intro hu
      apply MulEquiv.ext
      intro a
      have h := he u (Additive.ofMul a)
      rw [hu, map_one, Module.End.one_apply] at h
      exact e.injective h
    · intro hu
      apply EightTransvectionActors.core_faithful
      rw [map_one]
      apply LinearMap.ext
      intro w
      obtain ⟨a, rfl⟩ := e.surjective w
      rw [← he]
      change e (seedRepresentation U A hn u a) = e a
      apply congrArg e
      change Additive.ofMul (conjugation U A hn u a.toMul) = a
      rw [hu]
      rfl
  have hsmall (u : U) : Module.finrank (ZMod 2)
      (coreRepresentation (Fin 8) (β u) - LinearMap.id).range ≤ 1 := by
    have hb := LinearMap.finrank_range_le_of_surjective_intertwining
      (seedRepresentation U A hn u - LinearMap.id)
      (coreRepresentation (Fin 8) (β u) - LinearMap.id)
      e.toLinearMap e.surjective (by intro a; simp only [LinearMap.sub_apply,
        LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, he])
      (fixedSeed U A hn).toSubmodule ⊥ (by
        intro a ha
        change seedRepresentation U A hn u a - a = 0
        exact sub_eq_zero.mpr (ha u))
    simp only [finrank_bot, add_zero] at hb
    have hd := fixed_quotient_finrank hn
    have hl := Nat.log_mono_right (b := 2) hi
    norm_num at hl
    exact hb.trans (hd ▸ hl)
  have : IsElementaryAbelian 2 (β.range) :=
    IsElementaryAbelian.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hc := EightTransvectionActors.card_le_two_of_small_displacements β.range
    (by rintro _ ⟨u, rfl⟩; exact hsmall u)
  rw [← index_ker, hker] at hc
  exact hc

private def evenActor {T : Sylow 2 G} {H A : Subgroup G}
    (hAH : A ≤ H) (α : LocalQuotient T H →* Equiv.Perm (Fin 5))
    (heven : ∀ a : A, α (localActorMap (T := T) hAH a) ∈ alternatingGroup (Fin 5)) :
    A →* alternatingGroup (Fin 5) where
  toFun a := ⟨α (localActorMap hAH a), heven a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

omit [Finite G] in
private theorem evenActor_card {T : Sylow 2 G} {H A : Subgroup G}
    (hAH : A ≤ H) (α : LocalQuotient T H →* Equiv.Perm (Fin 5))
    (hα : Function.Injective α)
    (heven : ∀ a : A, α (localActorMap (T := T) hAH a) ∈ alternatingGroup (Fin 5)) :
    Nat.card (evenActor hAH α heven).range = Nat.card (localImage T H A) := by
  have hk : (evenActor hAH α heven).ker = (localActorMap (T := T) hAH).ker := by
    ext a
    change (⟨α (localActorMap hAH a), heven a⟩ : alternatingGroup (Fin 5)) = 1 ↔ _
    rw [Subtype.ext_iff]
    change α (localActorMap (T := T) hAH a) = 1 ↔ localActorMap (T := T) hAH a = 1
    constructor
    · intro h
      exact hα (h.trans α.map_one.symm)
    · intro h
      rw [h, map_one]
  rw [← index_ker, hk, localActorMap_ker, localImage_card hAH]
  rfl

omit [Finite G] in
/-- The actual image of an elementary actor has rank at most two before
quadraticity is used. Its marking lies in A₅ inside the source S₅ action. -/
theorem localImage_card_le_four {T : Sylow 2 G} {H A : Subgroup G}
    [IsElementaryAbelian 2 A]
    (hAH : A ≤ H) (α : LocalQuotient T H →* Equiv.Perm (Fin 5))
    (hα : Function.Injective α)
    (heven : ∀ a : A, α (localActorMap (T := T) hAH a) ∈ alternatingGroup (Fin 5)) :
    Nat.card (localImage T H A) ≤ 4 := by
  rw [← evenActor_card hAH α hα heven]
  exact FiveQuadraticActors.card_le_four _
    ((IsElementaryAbelian.isPGroup 2 A).of_surjective _
      (evenActor hAH α heven).rangeRestrict_surjective)

omit [Finite G] in
/-- Quadraticity cuts the same quotient image down to order at most two.
The embedding is an actual permutation-core summand of the local span. -/
theorem localImage_card_le_two_of_quadratic {T : Sylow 2 G} {H A : Subgroup G}
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 (localSpan T H)]
    (hAH : A ≤ H) (α : LocalQuotient T H →* Equiv.Perm (Fin 5))
    (hα : Function.Injective α)
    (heven : ∀ a : A, α (localActorMap (T := T) hAH a) ∈ alternatingGroup (Fin 5))
    (j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T H)) (hj : Function.Injective j)
    (he : ∀ (a : A) v, j (coreRepresentation (Fin 5)
      (α (localActorMap (T := T) hAH a)) v) =
        seedRepresentation A (localSpan T H)
          (hAH.trans (normalizes_localSpan T H)) a (j v))
    (hq : Representation.BinaryOffender.IsQuadratic
      (seedRepresentation A (localSpan T H) (hAH.trans (normalizes_localSpan T H))) ⊤) :
    Nat.card (localImage T H A) ≤ 2 := by
  rw [← evenActor_card hAH α hα heven]
  apply FiveQuadraticActors.card_le_two_of_quadratic
  · exact (IsElementaryAbelian.isPGroup 2 A).of_surjective _
      (evenActor hAH α heven).rangeRestrict_surjective
  · apply FiveQuadraticActors.image_quadratic_of_embedding _ _ j hj _ hq
    exact he

/-- The complete local action contradiction in 12.6.23. The global-r argument
first makes the actual local span normalize the chosen conjugate. The five-point
summand reduces its quotient image from rank two to rank one; the eight-point
normalizer action bounds the reverse image, contradicting that same summand.
The local structure, the two markings and r≥4 remain earlier source inputs. -/
theorem local_actor_contradiction {T : Sylow 2 G} {H V A : Subgroup G}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    [IsElementaryAbelian 2 (localSpan T H)]
    (hconj : ∃ g : G, V.map (MulAut.conj g).toMonoidHom = A)
    (hAH : A ≤ H)
    (hcore : H.pCoreIn 2 = H ⊓ centralizer (localSpan T H : Set G))
    (hr : 4 ≤ ChapterE.globalR V)
    (hne : localImage T H A ≠ ⊥)
    (α : LocalQuotient T H →* Equiv.Perm (Fin 5)) (hα : Function.Injective α)
    (heven : ∀ a : A, α (localActorMap (T := T) hAH a) ∈ alternatingGroup (Fin 5))
    (j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T H)) (hj : Function.Injective j)
    (he : ∀ (a : A) v, j (coreRepresentation (Fin 5)
      (α (localActorMap (T := T) hAH a)) v) =
        seedRepresentation A (localSpan T H)
          (hAH.trans (normalizes_localSpan T H)) a (j v))
    (e8 : Additive A ≃ₗ[ZMod 2] core (Fin 8))
    (β : normalizer (A : Set G) →* Equiv.Perm (Fin 8))
    (he8 : ∀ n a, e8 (Representation.elementaryRepresentation (p := 2) A.normalizerMonoidHom n a) =
      coreRepresentation (Fin 8) (β n) (e8 a)) : False := by
  have hk : Representation.BinaryOffender.rank (localImage T H A) ≤ 2 := by
    have hc := Nat.log_mono_right (b := 2) (localImage_card_le_four hAH α hα heven)
    norm_num at hc
    exact hc
  have hnorm : localSpan T H ≤ normalizer (A : Set G) := by
    obtain ⟨g, rfl⟩ := hconj
    exact (conjugate_actor_normalization_of_image_rank hAH hcore hr hk).1
  have hquad : Representation.BinaryOffender.IsQuadratic
      (seedRepresentation A (localSpan T H) (hAH.trans (normalizes_localSpan T H))) ⊤ := by
    obtain ⟨g, rfl⟩ := hconj
    exact conjugate_actor_quadratic hAH hcore hr hk
  have hsmall := localImage_card_le_two_of_quadratic hAH α hα heven j hj he hquad
  rw [localImage_card hAH] at hsmall
  have hreverse := core_centralizer_index_le_two hnorm e8
    (β.comp (inclusion hnorm)) (fun u a => he8 (inclusion hnorm u) a) hsmall
  have hnot : ¬ A ≤ centralizer (localSpan T H : Set G) := by
    intro h
    exact hne ((localImage_eq_bot_iff hAH).mpr h)
  obtain ⟨a, ha, hna⟩ := SetLike.not_le_iff_exists.mp hnot
  let aA : A := ⟨a, ha⟩
  have hmove : evenActor hAH α heven aA ≠ 1 := by
    intro hz
    have hq : localActorMap (T := T) hAH aA = 1 := by
      apply hα
      exact (congrArg Subtype.val hz).trans α.map_one.symm
    have hk : aA ∈ (localActorMap (T := T) hAH).ker := hq
    rw [localActorMap_ker] at hk
    exact hna hk
  have hlo := conjugation_displacement_ge_two
    (hAH.trans (normalizes_localSpan T H)) (evenActor hAH α heven) j hj
    he aA hmove
  have hhi := conjugation_displacement_le_centralizer_corank
    (hAH.trans (normalizes_localSpan T H)) (show A ≤ A from le_rfl) aA ha
  have hlog := Nat.log_mono_right (b := 2) hreverse
  norm_num at hlog
  omega

end CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
