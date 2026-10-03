module

public import FeitThompson.GroupAction.CentralizerCondition
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Ambient centralizers from subnormal core control

Suppose a finite ambient group contains a p-subgroup U normal in E, with E
subnormal in C. Assume C has characteristic p and contains the ambient
centralizer of U. If a subgroup P contains an ambient Sylow p-subgroup,
normalizes C, and has centralizer of U equal to U, then the ambient
centralizer of U is a p-group.

Subnormal p-core monotonicity first places U in O_p(C). Since P contains an
ambient Sylow subgroup and normalizes O_p(C), this core lies in P. Thus U
is self-centralizing in the core. A coprime subgroup centralizing U acts
trivially on the core by the nilpotent coprime centralizer criterion;
characteristic p then rules out every other prime in the centralizer order.

This supplies the ambient p-group step in Stellmacher (9.1), journal p. 48.
The coprime action criterion is Proposition 1.10 in
`FeitThompson/GroupAction/CentralizerCondition.lean`; the core transfer uses
`Theory/GroupTheory/PGroup/SubnormalCore.lean`. No ambient graph action is
assumed. Only the final centralizer theorem is part of the public interface.
-/

namespace Stellmacher

private theorem coprime_centralizer_le_core
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U D : Subgroup G) (hU : U ≤ pCore p G)
    (hcent : pCore p G ⊓ Subgroup.centralizer (U : Set G) ≤ U)
    (hchar : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G)
    (hD : D ≤ Subgroup.centralizer (U : Set G))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card (pCore p G))) :
    D ≤ pCore p G := by
  let R := pCore p G
  let _ : Subgroup.Normalizes D R := ⟨Subgroup.le_normalizer_of_normal⟩
  have hfixed : U.subgroupOf R ≤ fixedPointSubgroup D R := by
    intro member hmember actor
    apply Subtype.ext
    change (actor : G) * (member : G) * (actor : G)⁻¹ = member
    have hcomm := Subgroup.mem_centralizer_iff.mp (hD actor.property)
      member hmember
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfixedcent :
      Subgroup.centralizer (fixedPointSubgroup D R : Set R) ≤
        fixedPointSubgroup D R := by
    intro member hmember
    apply hfixed
    apply hcent
    refine ⟨member.property, ?_⟩
    change (member : G) ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro element helement
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hmember
      ⟨element, hU helement⟩ (hfixed helement))
  have htriv := actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup
    (G := R) (A := D) (pCore_isPGroup (p := p) (G := G)).isNilpotent hcop hfixedcent
  intro actor hactor
  apply hchar
  rw [Subgroup.mem_centralizer_iff]
  intro element helement
  have heq := congrArg Subtype.val (htriv ⟨actor, hactor⟩ ⟨element, helement⟩)
  change actor * element * actor⁻¹ = element at heq
  simpa [mul_assoc] using (congrArg (fun value : G => value * actor) heq).symm

private theorem isPGroup_centralizer_of_core_selfCentralizing
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U : Subgroup G) (hU : U ≤ pCore p G)
    (hcent : pCore p G ⊓ Subgroup.centralizer (U : Set G) ≤ U)
    (hchar : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G) :
    IsPGroup p (Subgroup.centralizer (U : Set G)) := by
  classical
  let C := Subgroup.centralizer (U : Set G)
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
  intro prime hprime
  obtain ⟨hprimeP, hprimeD, _⟩ := Nat.mem_primeFactors.mp hprime
  by_cases heq : prime = p
  · subst prime
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card'
    prime (hp := ⟨hprimeP⟩) hprimeD
  let D := (Subgroup.zpowers element).map C.subtype
  have hDcard : Nat.card D = prime := by
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      Nat.card_zpowers, horder]
  have hDle : D ≤ C := Subgroup.map_subtype_le _
  obtain ⟨power, hpower⟩ := (pCore_isPGroup (G := G) (p := p)).exists_card_eq
  have hcop : Nat.Coprime (Nat.card D) (Nat.card (pCore p G)) := by
    rw [hDcard, hpower]
    exact (hprimeP.coprime_iff_not_dvd.mpr
      (fun hdvd => heq ((Nat.prime_dvd_prime_iff_eq hprimeP Fact.out).mp hdvd))).pow_right power
  have hDcore := coprime_centralizer_le_core U D hU hcent hchar hDle hcop
  have hDdvd : prime ∣ Nat.card (pCore p G) := by
    rw [← hDcard]
    exact Subgroup.card_dvd_of_le hDcore
  rw [hpower] at hDdvd
  exact (heq ((Nat.prime_dvd_prime_iff_eq hprimeP Fact.out).mp
    (hprimeP.dvd_of_dvd_pow hDdvd))).elim


private theorem core_le_core_of_sylow_normalizes
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (C P : Subgroup H) (S : Sylow p H) (hSP : (S : Subgroup H) ≤ P)
    (hPC : P ≤ Subgroup.normalizer (C : Set H)) :
    (pCore p C).map C.subtype ≤ (pCore p P).map P.subtype := by
  let R := (pCore p C).map C.subtype
  have hNcore : Subgroup.normalizer (C : Set H) ≤
      Subgroup.normalizer (R : Set H) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor member hmember
    obtain ⟨inside, hinside, rfl⟩ := hmember
    let aut := Subgroup.normalizerMonoidHom C ⟨actor, hactor⟩
    have hfix : (pCore p C).comap aut.toMonoidHom = pCore p C :=
      (inferInstance : (pCore p C).Characteristic).fixed aut
    have himage : aut inside ∈ pCore p C := by
      change inside ∈ (pCore p C).comap aut.toMonoidHom
      rwa [hfix]
    exact ⟨aut inside, himage, by
      simp [aut, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  have hPR : P ≤ Subgroup.normalizer (R : Set H) := hPC.trans hNcore
  have hRp : IsPGroup p R := (pCore_isPGroup (G := C) (p := p)).map C.subtype
  have hRS : R ≤ (S : Subgroup H) := by
    have heq := S.is_maximal'
      (S.isPGroup'.to_sup_of_normal_right' hRp (hSP.trans hPR)) le_sup_left
    exact le_sup_right.trans heq.le
  have hRP := hRS.trans hSP
  have hnormal : (R.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mpr hPR
  have hRpP : IsPGroup p (R.subgroupOf P) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
  have hcore : R.subgroupOf P ≤ pCore p P := le_sSup ⟨hnormal, hRpP⟩
  have hmap := Subgroup.map_mono (f := P.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hRP] at hmap

private theorem normal_p_subgroup_le_ambient_core
    {H : Type*} [Group H] [Finite H] {p : ℕ}
    (U E C : Subgroup H) (hUE : U ≤ E) (hUnormal : (U.subgroupOf E).Normal)
    (hUp : IsPGroup p U) (hEC : E ≤ C) (hEsub : (E.subgroupOf C).IsSubnormal) :
    U ≤ (pCore p C).map C.subtype := by
  have hUpE : IsPGroup p (U.subgroupOf E) :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUE).symm
  have hcore : U.subgroupOf E ≤ pCore p E := le_sSup ⟨hUnormal, hUpE⟩
  have hmap := Subgroup.map_mono (f := E.subtype) hcore
  rw [Subgroup.map_subgroupOf_eq_of_le hUE] at hmap
  exact hmap.trans (pCoreAmbient_mono_of_isSubnormalIn E C p hEC hEsub)

/-- Subnormal core control and local self-centralization force the ambient centralizer
to be a p-group. -/
public theorem centralizer_isPGroup_of_subnormal_data
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (U E C P : Subgroup H) (S : Sylow p H)
    (hUE : U ≤ E) (hUnormal : (U.subgroupOf E).Normal) (hUp : IsPGroup p U)
    (hEC : E ≤ C) (hEsub : (E.subgroupOf C).IsSubnormal)
    (hSP : (S : Subgroup H) ≤ P) (hPC : P ≤ Subgroup.normalizer (C : Set H))
    (hcentC : Subgroup.centralizer (U : Set H) ≤ C)
    (hself : P ⊓ Subgroup.centralizer (U : Set H) = U)
    (hchar : Subgroup.centralizer (pCore p C : Set C) ≤ pCore p C) :
    IsPGroup p (Subgroup.centralizer (U : Set H)) := by
  have hUC := hUE.trans hEC
  have hUR := normal_p_subgroup_le_ambient_core U E C hUE hUnormal hUp hEC hEsub
  have hRP := (core_le_core_of_sylow_normalizes C P S hSP hPC).trans
    (Subgroup.map_subtype_le _)
  have hUcore : U.subgroupOf C ≤ pCore p C := by
    have hcomap := Subgroup.comap_mono (f := C.subtype) hUR
    rwa [Subgroup.comap_map_eq_self_of_injective C.subtype_injective] at hcomap
  have hcorecent : pCore p C ⊓
      Subgroup.centralizer (U.subgroupOf C : Set C) ≤ U.subgroupOf C := by
    rintro member ⟨hmember, hcentral⟩
    apply hself.le
    refine ⟨hRP ⟨member, hmember, rfl⟩, ?_⟩
    change (member : H) ∈ Subgroup.centralizer (U : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro element helement
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentral
      ⟨element, hUC helement⟩ helement)
  have hinternal := isPGroup_centralizer_of_core_selfCentralizing
    (U.subgroupOf C) hUcore hcorecent hchar
  apply (hinternal.map C.subtype).to_le
  intro member hmember
  refine ⟨⟨member, hcentC hmember⟩, ?_, rfl⟩
  change (⟨member, hcentC hmember⟩ : C) ∈
    Subgroup.centralizer (U.subgroupOf C : Set C)
  rw [Subgroup.mem_centralizer_iff]
  intro element helement
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hmember element helement)

end Stellmacher
