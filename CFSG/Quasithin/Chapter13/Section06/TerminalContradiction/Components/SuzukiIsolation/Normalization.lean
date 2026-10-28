module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FaithfulAction
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Defs
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Normalization of the remaining Suzuki component

In H/O₂(H), the image of each C-component is its intrinsic two-core
quotient. The normal distinguished component has order divisible by five
in all three actual candidate models. If a Suzuki component moves, it and
its conjugate are distinct simple components, different from the normal
component. The component dichotomy makes the three images commute.

Trivial centers of the two Suzuki factors make their successive products
with the distinguished factor injective. Cauchy's theorem then embeds
C₅ × C₅ × C₅, contradicting five-rank at most two. This argument needs no
simplicity or center calculation for the distinguished candidate. Normality
lifts through the solvable two-core. The final specialization gives exactly
the restricted-T normalizer containment used by `hz_component_obstruction`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the Suzuki
exclusion in 13.6.27, printed p.934 / PDF p.951. The component-orbit rank
argument uses the component calculus underlying A.3.8. The concrete model
facts come from the checked ATLAS J₂ action, the Witt-design M₂₃ order,
the matrix PSL₃(4) order, and Huppert–Blackburn III, XI.3.3 and XI.3.6.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem disjoint_of_centerless {G : Type*} [Group G] (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G)) (hz : center B = ⊥) : Disjoint A B := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have h : (⟨x, hx.2⟩ : B) ∈ center B := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hc hx.1) y y.property)
  rw [hz] at h
  exact congrArg Subtype.val h

private theorem rank_three {G : Type*} [Group G] [Finite G]
    (A B C : Subgroup G)
    (hab : ⁅A, B⁆ = ⊥) (hac : ⁅A, C⁆ = ⊥) (hbc : ⁅B, C⁆ = ⊥)
    (hbz : center B = ⊥) (hcz : center C = ⊥)
    (ha : 5 ∣ Nat.card A) (hb : 5 ∣ Nat.card B) (hc : 5 ∣ Nat.card C) :
    3 ≤ primeRank 5 G := by
  have hAB := commutator_eq_bot_iff_le_centralizer.mp hab
  have hAC := commutator_eq_bot_iff_le_centralizer.mp hac
  have hBC := commutator_eq_bot_iff_le_centralizer.mp hbc
  let f : A × B →* G := A.subtype.noncommCoprod B.subtype
    (fun a b => (hAB a.property b b.property).symm)
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    simpa only [range_subtype] using
      And.intro A.subtype_injective (And.intro B.subtype_injective
        (disjoint_of_centerless A B hAB hbz))
  have hfc : ∀ x : A × B, ∀ c : C, Commute (f x) (c : G) := by
    intro x c
    exact (show Commute (x.1 : G) (c : G) from (hAC x.1.property c c.property).symm).mul_left
      (show Commute (x.2 : G) (c : G) from (hBC x.2.property c c.property).symm)
  let f' : (A × B) × C →* G := f.noncommCoprod C.subtype hfc
  have hf' : Function.Injective f' := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    refine ⟨hf, C.subtype_injective, ?_⟩
    rw [range_subtype]
    apply disjoint_of_centerless f.range C _ hcz
    rintro x ⟨ab, rfl⟩ c hc
    exact (hfc ab ⟨c, hc⟩).symm.eq
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 ha
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hb
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 hc
  let CA := zpowers a
  let CB := zpowers b
  let CC := zpowers c
  let : CommGroup CA := IsCyclic.commGroup
  let : CommGroup CB := IsCyclic.commGroup
  let : CommGroup CC := IsCyclic.commGroup
  have hca : Nat.card CA = 5 := (Nat.card_zpowers a).trans ha
  have hcb : Nat.card CB = 5 := (Nat.card_zpowers b).trans hb
  have hcc : Nat.card CC = 5 := (Nat.card_zpowers c).trans hc
  let j : (CA × CB) × CC →* (A × B) × C :=
    (CA.subtype.prodMap CB.subtype).prodMap CC.subtype
  refine primeRank_ge_of_elementary_embedding (p := 5) (e := 3) ?_ ?_ (f'.comp j) ?_
  · intro x
    apply Prod.ext
    · apply Prod.ext
      · simpa [hca] using pow_card_eq_one' (x := x.1.1)
      · simpa [hcb] using pow_card_eq_one' (x := x.1.2)
    · simpa [hcc] using pow_card_eq_one' (x := x.2)
  · rw [Nat.card_prod, Nat.card_prod, hca, hcb, hcc]
    rfl
  · intro x y hxy
    have h := hf' hxy
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun t : (A × B) × C => t.1.1) h)
      · exact Subtype.ext (congrArg (fun t : (A × B) × C => t.1.2) h)
    · exact Subtype.ext (congrArg (fun t : (A × B) × C => t.2) h)

private theorem ordinary_commutes {G : Type*} [Group G]
    {A B : Subgroup G} (hA : A.IsCComponent) (hB : IsComponent G B) (hne : B ≠ A) :
    ⁅A, B⁆ = ⊥ := by
  rcases hB.subnormal_dichotomy A hA.subnormal with h | h
  · exact (hne (hB.isCComponent.eq_of_le hA h)).elim
  · rwa [commutator_comm]

private theorem centerless_of_simple_component {G : Type*} [Group G]
    {A : Subgroup G} (hA : A.IsCComponent) [IsSimpleGroup A] : center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let := hA.perfect
    let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hA.ne_bot
    exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim

private theorem ordinary_of_simple_component {G : Type*} [Group G]
    {A : Subgroup G} (hA : A.IsCComponent) [IsSimpleGroup A] : IsComponent G A := by
  let := hA.perfect
  have hz := centerless_of_simple_component hA
  refine ⟨hA.subnormal, ?_⟩
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup_congr.mpr inferInstance }

private theorem normal_of_rank {G : Type*} [Group G] [Finite G]
    {K D : Subgroup G} (hK : K.IsCComponent) [K.Normal]
    (hD : D.IsCComponent) [IsSimpleGroup D] (hne : D ≠ K)
    (hk5 : 5 ∣ Nat.card K) (hd5 : 5 ∣ Nat.card D)
    (hr : primeRank 5 G ≤ 2) : D.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hmove
  let E := D.map (MulAut.conj g).toMonoidHom
  have he : E ≠ K := by
    intro he
    have hk := Normal.map_conj_eq K g
    exact hne ((map_injective (MulAut.conj g).injective) (he.trans hk.symm))
  have heD : E ≠ D := hmove
  have hDo := ordinary_of_simple_component hD
  have hEo : IsComponent G E := hDo.map_equiv (MulAut.conj g)
  let eDE : D ≃* E := (MulAut.conj g).subgroupMap D
  let : IsSimpleGroup E := eDE.isSimpleGroup_congr.mp inferInstance
  have hge := rank_three K D E (ordinary_commutes hK hDo hne)
    (ordinary_commutes hK hEo he) (hDo.commutator_eq_bot_of_ne hEo heD.symm)
    (centerless_of_simple_component hD) (centerless_of_simple_component hEo.isCComponent)
    hk5 hd5 (by rw [← Nat.card_congr eDE.toEquiv]; exact hd5)
  omega

private theorem j2_five_dvd : 5 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier := by
  let J := Sporadic.LeechRelated.J2.Carrier
  have horbit : MulAction.orbit J (0 : Fin 100) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    obtain ⟨g, hg⟩ := Sporadic.LeechRelated.J2.ExceptionalParabolics.action_transitive i
    exact ⟨g, hg⟩
  let : MulAction.IsPretransitive J (Fin 100) :=
    (MulAction.isPretransitive_iff_orbit_eq_univ _).mpr horbit
  have hd := (MulAction.stabilizer J (0 : Fin 100)).index_dvd_card
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_fin] at hd
  exact (by decide : 5 ∣ 100).trans hd

private theorem suzuki_five_dvd (m : ℕ) (hm : 0 < m) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : (2 ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
    rw [← pow_mul]
    have h : (2 * m + 1) * 2 = 2 + 4 * m := by omega
    rw [h, pow_add, pow_mul]
    norm_num
  rw [he, Nat.add_mod, Nat.mul_mod]
  have h16 : 16 ^ m % 5 = 1 := by
    change Nat.ModEq 5 (16 ^ m) 1
    simpa using (show Nat.ModEq 5 16 1 by decide).pow m
  rw [h16]

private theorem candidate_five_dvd {H : Type*} [Group H]
    {S K : Subgroup H} (h : Candidate S K) : 5 ∣ Nat.card (K ⧸ pCore 2 K) := by
  rcases h with h | h | ⟨e, _⟩
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact j2_five_dvd
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order]
    decide
  · rw [Nat.card_congr e.toEquiv, Matrix.PSL3Four.card_PSL]
    decide

/-- Every other Suzuki C-component is normal when the actual two-core quotient
has five-rank at most two and the distinguished candidate is normal. -/
theorem suzuki_component_normal {H : Type*} [Group H] [Finite H]
    {S K D : Subgroup H} (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate S K) (hD : D.IsCComponent) (hne : D ≠ K)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hr : primeRank 5 (H ⧸ pCore 2 H) ≤ 2) : D.Normal := by
  let := pCore_isNilpotent (p := 2) (G := H)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kb := K.map q
  let Db := D.map q
  have hKb : Kb.IsCComponent := hK.map_quotient (pCore 2 H)
  have hDb : Db.IsCComponent := hD.map_quotient (pCore 2 H)
  let eD : Db ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
    (cComponentTwoCoreQuotientEquiv hD).symm.trans e
  let : IsSimpleGroup Db := eD.isSimpleGroup_congr.mpr
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  have hn : Db ≠ Kb := fun he => hne (hD.eq_of_map_quotient_eq hK (pCore 2 H) he)
  have hk5 : 5 ∣ Nat.card Kb := by
    rw [← Nat.card_congr (cComponentTwoCoreQuotientEquiv hK).toEquiv]
    exact candidate_five_dvd hc
  have hd5 : 5 ∣ Nat.card Db := by
    rw [Nat.card_congr eD.toEquiv]
    exact suzuki_five_dvd m (by omega)
  exact cComponent_normal_of_quotient_normal hD (pCore 2 H)
    (normal_of_rank hKb hDb hn hk5 hd5 hr)

/-- The precise restricted-Sylow containment required by the H_z Borel
argument, for any actual local overgroup H. -/
theorem restricted_sylow_normalizes_suzuki_component
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    {K D : Subgroup H} (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf H) K)
    (hD : D.IsCComponent) (hne : D ≠ K) {m : ℕ} (hm : 1 ≤ m)
    (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hr : primeRank 5 (H ⧸ pCore 2 H) ≤ 2) :
    (T : Subgroup G).subgroupOf H ≤ normalizer (D : Set H) := by
  let := suzuki_component_normal hK hc hD hne hm e hr
  rw [normalizer_eq_top]
  exact le_top

/-- At H = C_G(z), source SQTK supplies the five-rank bound. This discharges
`hn` in `SuzukiIsolation.hz_component_obstruction`; the component catalogue
and the final 5.2.3 application remain with that theorem's assembly owner. -/
theorem centralizer_sylow_normalizes_suzuki_component
    {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
    (T : Sylow 2 G) (z : G)
    (hsq : IsSQTK 𝒦 (centralizer ({z} : Set G)))
    {K D : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hD : D.IsCComponent) (hne : D ≠ K) {m : ℕ} (hm : 1 ≤ m)
    (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)) ≤
      normalizer (D : Set (centralizer ({z} : Set G))) := by
  apply restricted_sylow_normalizes_suzuki_component T _ hK hc hD hne hm e
  exact (primeRank_quotient_le_of_isTwoGroup 5 (by decide) (pCore 2 _)
    pCore_isPGroup).trans (hsq.stronglyQuasithin 5 (by decide) (by decide))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
