module

public import CFSG.Quasithin.MainConverse.ModelCases
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Excluding the actual two-central PSL₃(4) component

An involution centralizing a full Sylow two-subgroup has a characteristic-two
centralizer in each even-characteristic model. Thus that centralizer has no
ordinary component. The remaining Theorem C alternatives have insufficient
order or derived three-rank to contain the actual rank-two PSL₃(4) cover. The representative quotient transport constructs
this exact input in `RepresentativeBoundSource.central_plane_le_twoCore`.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1136; Theorem C, p.33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeModelSieve
open ChapterA.Section02 ClassificationModels
universe u v

structure Input (S : Type u) [Group S] where
  simple : IsSimpleGroup S
  nonabelian : ¬ IsMulCommutative S
  involution : S
  order : orderOf involution = 2
  sylow : Sylow 2 S
  sylow_le : (sylow : Subgroup S) ≤ centralizer ({involution} : Set S)
  component : Subgroup (centralizer ({involution} : Set S))
  isComponent : IsComponent (centralizer ({involution} : Set S)) component
  card_dvd : 20160 ∣ Nat.card component
  rank : 2 ≤ primeRank 3 component

variable {S : Type u} [Group S] [Finite S] (s : Input S)
include s

private def Input.ofEquiv {T : Type v} [Group T] (e : S ≃* T) : Input T := by
  let : Finite T := Finite.of_equiv S e.toEquiv
  let f := Matrix.SU3.InnerThreeRank.centralizerEquiv e s.involution
  refine {
    simple := by let : IsSimpleGroup S := s.simple; exact e.symm.isSimpleGroup
    nonabelian := fun h => s.nonabelian (by
      refine ⟨⟨fun a b => ?_⟩⟩
      apply e.injective
      simpa only [map_mul] using h.is_comm.comm (e a) (e b))
    involution := e s.involution
    order := (e.orderOf_eq _).trans s.order
    sylow := s.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
    sylow_le := ?_
    component := s.component.map f.toMonoidHom
    isComponent := s.isComponent.map_equiv f
    card_dvd := ?_
    rank := ?_ }
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (s.sylow_le hx))
  · rw [MulEquiv.toMonoidHom_eq_coe,
      ← Nat.card_congr (f.subgroupMap s.component).toEquiv]
    exact s.card_dvd
  · rw [MulEquiv.toMonoidHom_eq_coe,
      ← primeRank_equiv 3 (f.subgroupMap s.component)]
    exact s.rank

omit [Finite S] in
private theorem Input.card_dvd_group : 20160 ∣ Nat.card S :=
  s.card_dvd.trans (s.component.card_subgroup_dvd_card.trans
    (centralizer ({s.involution} : Set S)).card_subgroup_dvd_card)

private theorem Input.rank_group : 2 ≤ primeRank 3 S :=
  s.rank.trans ((primeRank_subgroup_le 3 s.component).trans
    (primeRank_subgroup_le 3 (centralizer ({s.involution} : Set S))))

private theorem Input.rank_derived :
    2 ≤ primeRank 3 (commutator (centralizer ({s.involution} : Set S))) := by
  let : IsQuasisimple s.component := s.isComponent.2
  have hle : s.component ≤ commutator (centralizer ({s.involution} : Set S)) := by
    rw [← s.component.commutator_eq_self]
    exact commutator_mono le_top le_top
  exact s.rank.trans (primeRank_mono 3 hle)

/-- A Sylow-central involution has no ordinary component in an E-model. -/
theorem Input.not_evenCharacteristic : ¬ IsEvenCharacteristic S := by
  intro hE
  have hc := Chapter1.twoLocal_mem_He_of_sylow_le s.sylow (hE s.sylow)
    (isTwoLocal_involution_centralizer s.order) s.sylow_le
  exact not_isComponent_of_twoCore (Chapter1.mem_He_iff.mp hc) s.component s.isComponent


omit [Finite S] in
private theorem Input.perfect : Group.IsPerfect S := by
  let : IsSimpleGroup S := s.simple
  exact ⟨(inferInstance : (commutator S).Normal).eq_bot_or_eq_top.resolve_left
    (fun h => s.nonabelian ((commutator_eq_bot_iff S).mp h))⟩

private theorem Input.not_small (hsmall : Nat.card S ≤ 20160) : False := by
  let : IsSimpleGroup S := s.simple
  let : Group.IsPerfect S := s.perfect
  let C := centralizer ({s.involution} : Set S)
  have hne : C ≠ ⊤ := by
    intro he
    have ht : s.involution ∈ center S := by
      apply mem_center_iff.mpr
      intro x
      exact (mem_centralizer_singleton_iff.mp (show x ∈ C by rw [he]; trivial))
    rw [center_eq_bot_of_simple_perfect, mem_bot] at ht
    have hord := s.order
    rw [ht, orderOf_one] at hord
    omega
  have hlt : Nat.card C < Nat.card S := lt_of_le_of_ne C.card_le_card_group
    (fun hc => hne (C.card_eq_iff_eq_top.mp hc))
  have hle : 20160 ≤ Nat.card C := Nat.le_of_dvd Nat.card_pos
    (s.card_dvd.trans s.component.card_subgroup_dvd_card)
  omega

private theorem Input.not_alternating {n : ℕ} (hn : n ≤ 8)
    (he : Nonempty (S ≃* alternatingGroup (Fin n))) : False := by
  obtain ⟨e⟩ := he
  apply s.not_small
  rw [Nat.card_congr e.toEquiv]
  by_cases h8 : n = 8
  · subst n
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  · have hn7 : n ≤ 7 := by omega
    apply (alternatingGroup (Fin n)).card_le_card_group.trans
    rw [Nat.card_perm, Nat.card_fin]
    interval_cases n <;> norm_num [Nat.factorial]

omit [Finite S] in
private theorem Input.not_j1 (he : Nonempty (S ≃* Janko1.Model)) : False := by
  obtain ⟨e⟩ := he
  have hd := s.card_dvd_group
  rw [Nat.card_congr e.toEquiv, Janko1.card_model] at hd
  norm_num at hd

private theorem Input.not_linear_two {p e : ℕ}
    (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hmodel : ClassicalGroup.IsPSL S 2 (p ^ e)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  have hseven : 7 ∣ Nat.card PSL(2,F) := by
    rw [← Nat.card_congr a.toEquiv]
    exact (by decide : 7 ∣ 20160).trans s.card_dvd_group
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F)
    (hcard ▸ ho.pow)
  have hsevenOrder : 7 ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [← hcard, ← horder]
    exact dvd_mul_of_dvd_left hseven 2
  have hepos : e ≠ 0 := by
    intro hz
    have hlarge := Finite.one_lt_card (α := F)
    rw [hcard, hz, pow_zero] at hlarge
    omega
  by_cases hp3 : p = 3
  · subst p
    have hecases : e = 1 ∨ e = 2 := by omega
    rcases hecases with rfl | rfl <;> norm_num at hsevenOrder
  · have hlarge : 7 ≤ Nat.card F := by
      by_contra! hs
      have hc : Nat.card F = 3 ∨ Nat.card F = 5 := by
        have hodd : Nat.card F % 2 = 1 := Nat.odd_iff.mp (hcard ▸ ho.pow)
        have hgt := Finite.one_lt_card (α := F)
        omega
      rcases hc with hc | hc <;>
        rw [hcard] at hc <;> rw [hc] at hsevenOrder <;> norm_num at hsevenOrder
    let P : Sylow 3 PSL(2,F) := default
    have hP : IsCyclic P := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
      hcard hlarge 3 (by decide)
      (by rw [hcard]; exact ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)).pow_right e) P
    have hr := P.primeRank_le_one_of_isCyclic hP
    rw [← primeRank_equiv 3 a] at hr
    have := s.rank_group
    omega

private theorem Input.not_linear_three {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSL S 3 p) : False := by
  by_cases hp3 : p = 3
  · subst p
    exact s.not_evenCharacteristic
      (MainConverse.psl_three_four_qt_and_evenCharacteristic_of_isPSL (Or.inl rfl) hmodel).2
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let d := s.ofEquiv e
  let : IsSimpleGroup PSL(3,F) := d.simple
  let : Group.IsPerfect PSL(3,F) := d.perfect
  have hr := Matrix.PSL3.OddInvolutionFixed.inner_fixed_derived_three_rank
    (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hp3 hcard
    (MulAut.conj d.involution)
    ((MulAut.conj_orderOf_of_center_eq_bot center_eq_bot_of_simple_perfect _).trans d.order)
    ⟨d.involution, rfl⟩
  rw [MulAut.fixedSubgroup_conj] at hr
  have := d.rank_derived
  omega

private theorem Input.not_unitary_three {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSU S 3 p) : False := by
  obtain ⟨E, hE, hfin, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let d := s.ofEquiv e
  have hr := Matrix.SU3.InnerThreeRank.projective_involution_centralizer_rank
    p ho E J hcard hc d.involution d.order
  have := d.rank_derived
  omega

/-- The complete Theorem C list excludes this actual Sylow-central component. -/
theorem Input.not_theoremCModel (hm : IsTheoremCModel S) : False := by
  let : IsSimpleGroup S := s.simple
  cases hm with
  | alternating n hn e => exact s.not_alternating hn e
  | odd h =>
    cases h with
    | linear_two p e hp ho he iso => exact s.not_linear_two hp ho he iso
    | linear_three p hp ho iso => exact s.not_linear_three hp ho iso
    | unitary_three p hp ho iso => exact s.not_unitary_three hp ho iso
  | bender h =>
    exact s.not_evenCharacteristic
      (MainConverse.quasithin_and_evenCharacteristic_of_isQTKEModel s.nonabelian (.bender h)).2
  | rank_two f h =>
    exact s.not_evenCharacteristic
      (MainConverse.quasithin_and_evenCharacteristic_of_isQTKEModel s.nonabelian
        (.rank_two f h.toRankTwoModel)).2
  | linear_binary n hn h =>
    exact s.not_evenCharacteristic
      (MainConverse.quasithin_and_evenCharacteristic_of_isQTKEModel s.nonabelian
        (.linear_binary n hn h)).2
  | sporadic h =>
    rcases h with ⟨name, _, e⟩ | e
    · exact s.not_evenCharacteristic
        (MainConverse.quasithin_and_evenCharacteristic_of_isQTKEModel s.nonabelian
          (.sporadic ⟨name, e⟩)).2
    · exact s.not_j1 e

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeModelSieve
end
