module
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerQuotient
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.CubicSylowInversion
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Specified cubic inversion in Mathieu Sylow overgroups

The M₂₂ point stabilizer supplies an elementary nine, while the order of
M₂₃ has three-part nine. Thus every cyclic three-subgroup of M₂₃ or its
automorphism group has order dividing three.

The center of a Sylow two-subgroup of the native M₂₃ has order two.
Its normalizer therefore centralizes that involution. The actual involution
centralizer maps onto PSL₃(2) with two-group kernel, and the Sylow normalizer
in that quotient is the Sylow itself. This proves self-normalization in M₂₃.

Above any two-group kernel onto M₂₃, a cubic in an index-three Sylow
overgroup cannot normalize the Sylow. Its three-coset action gives an S₃
quotient, and Sylow normalizer lifting supplies an inverter of the specified
cubic inside the specified Sylow. Neither splitting nor an involutory lift
is assumed. The source consumer is the original Cartan intersection in
Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu
open M23Geometry.InvolutionCentralizer

/-- Every full Sylow two-subgroup of the actual M₂₃ carrier is self-normalizing. -/
theorem m23_self_normalizing_sylow (S : Sylow 2 M23) :
    normalizer (S : Set M23) = (S : Subgroup M23) := by
  have hS : Nat.card S = 128 := by
    rw [Sylow.card_eq_multiplicity,m23_order]
    decide +kernel
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hS]; decide)
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  have hZ : Nat.card (center S) = 2 := le_antisymm (m23_sylow_center_card_le_two S)
    (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 (by rw [hZ])
  let t : M23 := z.val.val
  have ht : orderOf t = 2 := by simpa only [t,Subgroup.orderOf_coe] using hz
  have hcenter : (center S).map (S : Subgroup M23).subtype = zpowers t := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem _ z.property)) ?_).symm
    rw [card_map_of_injective Subtype.val_injective,Nat.card_zpowers]
    change Nat.card (center S) ≤ orderOf t
    rw [ht,hZ]
  let C := centralizer ({t} : Set M23)
  have hNC : normalizer (S : Set M23) ≤ C :=
    normalizer_le_centralizer_of_characteristic_involution (S : Subgroup M23) (center S) t ht hcenter
  have hSC : (S : Subgroup M23) ≤ C := (S : Subgroup M23).le_normalizer.trans hNC
  let P := S.subtype hSC
  let e := (centralizer_equiv_representative ht).some
  let f : C →* Matrix.PSL3Two.SL :=
    Matrix.PSL3Two.equiv.symm.toMonoidHom.comp
      (actionEquivPSL.toMonoidHom.comp (extension.rightHom.comp e.toMonoidHom))
  have hf : Function.Surjective f := Matrix.PSL3Two.equiv.symm.surjective.comp
    (actionEquivPSL.surjective.comp (extension.rightHom_surjective.comp e.surjective))
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ Matrix.PSL3Two.equiv.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ actionEquivPSL.injective,
      ←MonoidHom.comap_ker]
    change IsPGroup 2 (action.rangeRestrict.ker.comap e.toMonoidHom)
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_isTwoGroup.comap_of_injective e.toMonoidHom e.injective
  have hn : normalizer (P : Set C) ≤ (P : Subgroup C) := by
    have hh := le_normalizer_map f (H := (P : Subgroup C))
    have he := Matrix.PSL3Two.self_normalizing_sylow (P.mapSurjective hf)
    change normalizer ((P : Subgroup C).map f : Set Matrix.PSL3Two.SL) = (P : Subgroup C).map f at he
    rw [he] at hh
    have hh' := map_le_iff_le_comap.mp hh
    rw [comap_map_eq_self (hk.le_sylow_of_normal P)] at hh'
    exact hh'
  apply le_antisymm _ (S : Subgroup M23).le_normalizer
  intro g hg
  have hg' : (⟨g,hNC hg⟩ : C) ∈ normalizer (P : Set C) := by
    change (⟨g,hNC hg⟩ : C) ∈ normalizer ((S : Subgroup M23).subgroupOf C : Set C)
    rw [←subgroupOf_normalizer_eq hSC]
    exact hg
  exact hn hg'


private theorem m23_cubic_not_normalizes_sylow (S : Sylow 2 (M23))
    (D : Subgroup (M23)) (hD : Nat.card D = 3) :
    ¬ D ≤ normalizer (S : Set (M23)) := by
  rw [m23_self_normalizing_sylow]
  intro hn
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hd : Disjoint D (S : Subgroup _) := hp.disjoint_of_coprime S.isPGroup' (by decide)
  have hb : D = ⊥ := le_bot_iff.mp ((le_inf le_rfl hn).trans hd.le_bot)
  simp [hb] at hD

/-- An order-three subgroup in an index-three Sylow overgroup above M₂₃ is
inverted from the prescribed Sylow. The kernel may be any two-group. -/
theorem m23_cubic_inverted_of_two_kernel {G : Type*} [Group G] [Finite G]
    (f : G →* M23) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 G)
    (J D : Subgroup G) (hSJ : (S : Subgroup G) ≤ J) (hDJ : D ≤ J)
    (hJ : Nat.card J = 3 * Nat.card S) (hD : Nat.card D = 3) :
    ∃ t ∈ (S : Subgroup G), ∀ d ∈ D, t*d*t⁻¹ = d⁻¹ := by
  let SJ := S.subtype hSJ
  have hi : (SJ : Subgroup J).index = 3 := by
    have hh := (SJ : Subgroup J).card_mul_index
    have hc : Nat.card SJ = Nat.card S :=
      Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv
    rw [hc,hJ] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans (Nat.mul_comm _ _))
  have hp : pCore 2 J < (SJ : Subgroup J) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal SJ) ?_
    intro he
    have hn : (SJ : Subgroup J).Normal := he ▸ inferInstance
    have hnorm : D ≤ normalizer (S : Set G) :=
      hDJ.trans ((normal_subgroupOf_iff_le_normalizer hSJ).mp hn)
    let Q := S.mapSurjective hf
    have hDn : D.map f ≤ normalizer (Q : Set (M23)) :=
      (map_mono (f := f) hnorm).trans (le_normalizer_map f)
    have hinj : Function.Injective (f.comp D.subtype) := by
      apply (injective_iff_map_eq_one _).mpr
      intro x hx
      have hd : Disjoint D f.ker := by
        apply disjoint_of_coprime_natCard
        obtain ⟨k,hk⟩ := hk.exists_card_eq
        rw [hD,hk]
        exact (by decide : Nat.Coprime 3 2).pow_right k
      exact Subtype.ext (disjoint_def.mp hd x.property hx)
    have hDc : Nat.card (D.map f) = 3 := by
      rw [←range_subtype D,←MonoidHom.range_comp]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hD
    exact m23_cubic_not_normalizes_sylow Q (D.map f) hDc hDn
  obtain ⟨e⟩ := sylow_index_three_core_quotient SJ hi hp
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨t,ht,hinv⟩ := cubic_inverted_in_sylow_of_two_kernel q hq hqk
    (D.subgroupOf J) (by rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv,hD]) SJ
  exact ⟨t,ht,fun d hd => congrArg Subtype.val (hinv ⟨d,hDJ hd⟩ hd)⟩


/-- The native M₂₂ point stabilizer supplies three-rank at least two. -/
theorem m23_primeRank_three_ge_two : 2 ≤ primeRank 3 M23 := by
  let f : M22 →* M23 := (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
    m23EquivM22PointStabilizer.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp m23EquivM22PointStabilizer.injective
  rw [←m22_primeRank_three]
  exact Theory.GroupTheory.primeRank_le_of_injective 3 f hf

/-- A cyclic three-subgroup of the actual M₂₃ has order dividing three. -/
theorem m23_cyclic_three_card_dvd_three (D : Subgroup M23)
    (hp : IsPGroup 3 D) (hc : IsCyclic D) : Nat.card D ∣ 3 := by
  have hd : Nat.card D ∣ 9 := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    have hcop : Nat.Coprime (Nat.card D) 1133440 := by
      rw [hk]
      exact (by decide : Nat.Coprime 3 1133440).pow_left k
    have h := D.card_subgroup_dvd_card
    rw [m23_order,show 10200960 = 9 * 1133440 from rfl] at h
    exact hcop.dvd_of_dvd_mul_right h
  have hnum : ∀ n ∈ (9 : ℕ).divisors, n ∣ 3 ∨ n = 9 := by decide +kernel
  rcases hnum _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) with h | h
  · exact h
  · let P : Sylow 3 M23 := Sylow.ofCard D (by rw [h,m23_order]; decide +kernel)
    have hr := P.primeRank_le_one_of_isCyclic hc
    have hl := m23_primeRank_three_ge_two
    omega

/-- Innerness gives the same bound for cyclic three-subgroups of Aut(M₂₃). -/
theorem m23_cyclic_three_aut_card_dvd_three (D : Subgroup (MulAut M23))
    (hp : IsPGroup 3 D) (hc : IsCyclic D) : Nat.card D ∣ 3 := by
  let e : M23 ≃* MulAut M23 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot M23Geometry.m23_center_eq_bot,m23_conj_surjective⟩
  let E := D.map e.symm.toMonoidHom
  let := hc
  have h := m23_cyclic_three_card_dvd_three E (hp.map e.symm.toMonoidHom)
    (isCyclic_of_surjective (e.symm.toMonoidHom.subgroupMap D)
      (e.symm.toMonoidHom.subgroupMap_surjective D))
  rwa [card_map_of_injective e.symm.injective] at h

end Sporadic.Mathieu
