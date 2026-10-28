module

public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionNine.DistanceOneEightConjugationImages

/-!
# The Sylow finish for the ambient elementary-eight centralizer

An elementary eight with two-group ambient centralizer is self-centralizing
under the distance-one local hypotheses and the two local S₄ quotient models.
The local conjugation-image theorem constructs an order-64 two-subgroup inside
the terminal stabilizer image and two distinct S₄ subgroups of the actual
ambient normalizer conjugation range. Elementary-eight recognition makes
that normalizer nonsolvable without assuming self-centralization.

The distance-one local conclusion and global Sylow equality give ambient
Sylow order 128. The conditional nonsolvable-normalizer theorem isolates
the resulting Sylow finish, and the principal theorem supplies its inputs
from the original local hypotheses.

Conjugating an ambient Sylow to the prescribed S0 makes Hypothesis One
applicable to any two-local subgroup containing an ambient Sylow. A Sylow
of the normalizer extending the order-64 subgroup has order 64 or 128;
nonsolvability excludes 128. The normal two-group centralizer therefore lies
in the selected Sylow and the terminal stabilizer image. Injectivity of the
embedding transfers the supplied local self-centralizer equality.

Source: Stellmacher (9.1)(c), Journal of Algebra 190 (1997), p.48, final
paragraph. The argument uses the actual ambient conjugation range throughout;
it does not form the source's mixed ambient/generated-group quotient.
-/

namespace Stellmacher.SectionNine

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open scoped IsMulCommutative

private theorem solvable_of_contains_ambient_sylow
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hyp : HypothesisOne H S0) (N : Subgroup H) (hN : IsTwoLocal N)
    (P : Sylow 2 H) (hPN : (P : Subgroup H) ≤ N) :
    Group.IsSolvable N := by
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq H P S0
  let equiv : H ≃* H := MulAut.conj conjugator
  have hlocal : IsTwoLocal (N.map equiv.toMonoidHom) := by
    obtain ⟨Q, hQne, hQp, rfl⟩ := hN
    refine ⟨Q.map equiv.toMonoidHom, ?_, hQp.map _, ?_⟩
    · intro hbot
      exact hQne (Subgroup.map_injective equiv.injective (by simpa using hbot))
    · exact Subgroup.map_equiv_normalizer_eq Q equiv
  have hS0 : (S0 : Subgroup H) ≤ N.map equiv.toMonoidHom := by
    rw [← hconjugator]
    exact Subgroup.map_mono hPN
  let _ : Group.IsSolvable (N.map equiv.toMonoidHom) :=
    (hyp.local_solvable_characteristicTwo _ hlocal hS0).1
  exact Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective equiv.toMonoidHom equiv.injective).toMonoidHom)
    (N.equivMapOfInjective equiv.toMonoidHom equiv.injective).injective

private theorem sylow_in_nonsolvable_local_of_half_card
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hyp : HypothesisOne H S0) (hS0 : Nat.card S0 = 128)
    (N R : Subgroup H) (hN : IsTwoLocal N) (hnonsolv : ¬ Group.IsSolvable N)
    (hRN : R ≤ N) (hRp : IsPGroup 2 R) (hRcard : Nat.card R = 64) :
    IsSylowTwoIn R N := by
  have hRpN : IsPGroup 2 (R.subgroupOf N) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  obtain ⟨P, hRP⟩ := hRpN.exists_le_sylow
  let image : Subgroup H := (P : Subgroup N).map N.subtype
  have himageN : image ≤ N := Subgroup.map_subtype_le _
  have hRimage : R ≤ image := by
    intro element helement
    exact ⟨⟨element, hRN helement⟩, hRP helement, rfl⟩
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map N.subtype).exists_le_sylow
  have hQcard : Nat.card Q = 128 := by
    rw [Q.card_eq_multiplicity, ← S0.card_eq_multiplicity, hS0]
  have hdiv : Nat.card image ∣ 128 := hQcard ▸ Subgroup.card_dvd_of_le hQ
  have hlower : 64 ≤ Nat.card image := by
    rw [← hRcard]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hRimage)
      (Subgroup.inclusion_injective hRimage)
  have hupper : Nat.card image ≤ 128 := Nat.le_of_dvd (by decide) hdiv
  have hcases : Nat.card image = 64 ∨ Nat.card image = 128 := by
    obtain ⟨factor, hfactor⟩ := hdiv
    have hfactorpos : 0 < factor := by nlinarith
    have hfactorle : factor ≤ 2 := by nlinarith
    interval_cases factor <;> omega
  have hcard : Nat.card image = 64 := by
    rcases hcases with hcard | hcard
    · exact hcard
    · have heq : image = (Q : Subgroup H) :=
        Subgroup.eq_of_le_of_card_ge hQ (by omega)
      exact (hnonsolv (solvable_of_contains_ambient_sylow S0 hyp N hN Q
        (heq ▸ himageN))).elim
  exact ⟨hRN, P, Subgroup.eq_of_le_of_card_ge hRimage (by omega) |>.symm⟩

private theorem centralizer_eq_of_sylow_in_local
    {H : Type*} [Group H] [Finite H] (U D R : Subgroup H)
    (hUC : U ≤ Subgroup.centralizer (U : Set H))
    (hC : IsPGroup 2 (Subgroup.centralizer (U : Set H)))
    (hR : IsSylowTwoIn R (Subgroup.normalizer (U : Set H)))
    (hRD : R ≤ D) (hself : D ⊓ Subgroup.centralizer (U : Set H) = U) :
    Subgroup.centralizer (U : Set H) = U := by
  apply le_antisymm _ hUC
  obtain ⟨_, P, hP⟩ := hR
  have hCN := Subgroup.centralizer_le_normalizer (U : Set H)
  have hCp : IsPGroup 2 ((Subgroup.centralizer (U : Set H)).subgroupOf
      (Subgroup.normalizer (U : Set H))) :=
    hC.of_equiv (Subgroup.subgroupOfEquivOfLe hCN).symm
  have hCP := hCp.le_sylow_of_normal P
  intro element helement
  apply hself.le
  refine ⟨hRD ?_, helement⟩
  rw [← hP]
  exact ⟨⟨element, hCN helement⟩, hCP helement, rfl⟩

universe u

public theorem distance_one_ambient_eight_centralizer_of_nonsolvable_normalizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (hS : S = (S0 : Subgroup H)) (U : Subgroup G)
    (helementary : IsElementaryAbelian 2 U) (hcard : Nat.card U = 8)
    (hself : GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer (U : Set G) = U)
    (hC : IsPGroup 2 (Subgroup.centralizer (U.map embedding : Set H)))
    (hnonsolv : ¬ Group.IsSolvable (Subgroup.normalizer (U.map embedding : Set H)))
    (R : Subgroup H) (hRN : R ≤ Subgroup.normalizer (U.map embedding : Set H))
    (hRD : R ≤ (GAt ctx.Γ ctx.criticalPath.a').map embedding)
    (hRp : IsPGroup 2 R) (hRcard : Nat.card R = 64) :
    Subgroup.centralizer (U.map embedding : Set H) = U.map embedding := by
  have hS0card : Nat.card S0 = 128 := by
    have hTcard := hlocal.2.2.1
    have hScard : Nat.card S = Nat.card T := by
      rw [← ctx.map_S, Subgroup.card_map_of_injective ctx.embedding_injective]
    rw [hS] at hScard
    omega
  let _ : IsElementaryAbelian 2 U := helementary
  have hUmap : IsPGroup 2 (U.map embedding) :=
    (IsElementaryAbelian.isPGroup 2 U).map embedding
  have hmapcard : Nat.card (U.map embedding) = 8 := by
    rw [Subgroup.card_map_of_injective ctx.embedding_injective, hcard]
  have hne : U.map embedding ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hmapcard
    omega
  have hNlocal : IsTwoLocal (Subgroup.normalizer (U.map embedding : Set H)) :=
    ⟨U.map embedding, hne, hUmap, rfl⟩
  have hR := sylow_in_nonsolvable_local_of_half_card S0 ctx.hypothesisTwo.hyp1
    hS0card _ R hNlocal hnonsolv hRN hRp hRcard
  refine centralizer_eq_of_sylow_in_local (U.map embedding)
    ((GAt ctx.Γ ctx.criticalPath.a').map embedding) R ?_ hC hR hRD ?_
  · rintro _ ⟨element, helement, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨member, hmember, rfl⟩
    have hcomm := congrArg (fun member : U => embedding member)
      (mul_comm (⟨member, hmember⟩ : U) ⟨element, helement⟩)
    simpa using hcomm
  · apply le_antisymm
    · rintro element ⟨⟨preimage, hpreimage, rfl⟩, hcentral⟩
      apply Subgroup.mem_map_of_mem
      apply hself.le
      refine ⟨hpreimage, ?_⟩
      change preimage ∈ Subgroup.centralizer (U : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro member hmember
      apply ctx.embedding_injective
      simpa using Subgroup.mem_centralizer_iff.mp hcentral
        (embedding member) (Subgroup.mem_map_of_mem embedding hmember)
    · rintro _ ⟨preimage, hpreimage, rfl⟩
      have hpreimage' := hself.ge hpreimage
      refine ⟨Subgroup.mem_map_of_mem embedding hpreimage'.1, ?_⟩
      change embedding preimage ∈ Subgroup.centralizer (U.map embedding : Set H)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨member, hmember, rfl⟩
      simpa using congrArg embedding
        (Subgroup.mem_centralizer_iff.mp hpreimage'.2 member hmember)

public theorem distance_one_ambient_eight_centralizer_of_isPGroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlen : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (hS : S = (S0 : Subgroup H))
    (U : Subgroup G) (hU : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 8)
    (hZ : ZAt ctx.Γ ctx.criticalPath.a' ≤ U)
    (hNorm : NormalIn U (EAt ctx.Γ ctx.criticalPath.a'))
    (hUa : U ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hUd : U ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hmodela : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hmodeld : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hself : GAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (U : Set G) = U)
    (hC : IsPGroup 2 (Subgroup.centralizer (U.map embedding : Set H))) :
    Subgroup.centralizer (U.map embedding : Set H) = U.map embedding := by
  obtain ⟨R, hRN, hRD, hRp, hRcard, X, Y, hXY, hX, hY⟩ :=
    distance_one_eight_conjugation_images ctx hlen hfaithful hlocal hS U hU
      hElem hUcard hZ hNorm hUa hUd hmodela hmodeld hself hC
  let _ : IsElementaryAbelian 2 U := hElem
  let _ : IsElementaryAbelian 2 (U.map embedding) := IsElementaryAbelian.map embedding
  have hmapcard : Nat.card (U.map embedding) = 8 := by
    rw [Subgroup.card_map_of_injective ctx.embedding_injective, hUcard]
  have hnonsolv := elementaryEight_normalizer_not_isSolvable_of_two_symmetric_four_images
    (U.map embedding) hmapcard X Y hXY hX hY
  exact distance_one_ambient_eight_centralizer_of_nonsolvable_normalizer ctx hlocal hS
    U hElem hUcard hself hC hnonsolv R hRN hRD hRp hRcard

end Stellmacher.SectionNine
