module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupMovement
public import Theory.Representation.BinaryConjugationSection.FullMovement
public import Theory.Representation.CyclicFixedRank

/-!
# The Cartan acts without fixed vectors on the generated quotient

Every nonidentity subgroup of the odd split Cartan acts without fixed
vectors on the natural two-dimensional module. Coprime action makes its
commutators generate that module. Centrality modulo the local two-core
carries this movement to the whole H₁-span modulo Z₁. Applying this to
each cyclic Cartan subgroup proves fixed-point freeness on the literal
binary conjugation section U/Z₁.

This uses natural-seed generation, which is stronger than merely
[U,A]Z₁ = U. The next displacement module uses the resulting free orbits
to bound every nonzero displacement space. The global TI and F.8 setup
remain with qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith 5.1.17, printed pp.640–641 (refs/quasithin.pdf).
-/

open scoped MatrixGroups IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
/-- Every nontrivial Cartan subgroup has trivial fixed group on the natural module. -/
theorem natural_cartan_subgroup_fixed_eq_bot {V : Subgroup G}
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L V n)
    (C : Subgroup G) (hCA : C ≤ A) (hC : C ≠ ⊥) :
    V ⊓ centralizer (C : Set G) = ⊥ := by
  have ho : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hdis : Disjoint A (L.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := hnat
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let l : L := ⟨a,hAL (hCA a.property)⟩
  have hqne : q l ≠ 1 := by
    intro he
    have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he)
    have hg : (a : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hl
    exact ha (Subtype.ext (Subgroup.disjoint_def.mp hdis (hCA a.property) hg))
  have hpow : q l ^ Nat.card A = 1 := by
    rw [← map_pow]
    have hlpow : l ^ Nat.card A = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G)) (pow_card_eq_one' (x := (⟨a,hCA a.property⟩ : A)))
    rw [hlpow,map_one]
  apply _root_.eq_bot_iff.mpr
  intro v hv
  have hfixed : (q l).val.mulVec (f ⟨v,hv.1⟩).toAdd = (f ⟨v,hv.1⟩).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hh := hf l ⟨v,hv.1⟩
    change (f.symm (Multiplicative.ofAdd ((q l).val.mulVec (f ⟨v,hv.1⟩).toAdd)) : G) = _ at hh
    rw [hh]
    change (a : G) * v * (a : G)⁻¹ = (f.symm (f ⟨v,hv.1⟩) : G)
    rw [f.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 a a.property)
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (q l) (Nat.card A) ho hpow hqne _ hfixed
  exact mem_bot.mpr (congrArg (fun z : V => (z : G))
    (f.injective (hz.trans f.map_one.symm)))

/-- Each nontrivial Cartan subgroup generates the natural seed by commutators. -/
theorem fundamental_cartan_subgroup_commutator
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (C : Subgroup G) (hCA : C ≤ A) (hC : C ≠ ⊥) :
    ⁅D.moduleSubgroup,C⁆ = D.moduleSubgroup := by
  let := D.module_elementary
  have hnorm : C ≤ normalizer (D.moduleSubgroup : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact (hCA.trans (c.left_le.trans inf_le_left)).trans hm.normalizes
  have ho : Odd (Nat.card C) := by
    have hh := OddHall.odd_hall_odd c.left_hall
    rw [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
    exact hh.of_dvd_nat (card_dvd_of_le hCA)
  have hcop : Nat.Coprime (Nat.card C) (Nat.card D.moduleSubgroup) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 D.moduleSubgroup).exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have he := eq_commutator_sup_centralizer_of_solvable_coprime D.moduleSubgroup C
    hnorm inferInstance hcop
  simpa only [natural_cartan_subgroup_fixed_eq_bot c hnat C hCA hC,
    sup_bot_eq] using he.symm

/-- The same subgroup moves the entire conjugate span modulo the literal point. -/
theorem fundamental_span_cartan_subgroup_moved
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hf : (setup T L D.moduleSubgroup H A).Hypothesis)
    (C : Subgroup G) (hCA : C ≤ A) (hC : C ≠ ⊥)
    (hc : (A.subgroupOf (H ⊔ A)).map
        (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G))) :
    ⁅(setup T L D.moduleSubgroup H A).U,C⁆ ⊔
        (setup T L D.moduleSubgroup H A).V₁ =
      (setup T L D.moduleSubgroup H A).U := by
  let E := setup T L D.moduleSubgroup H A
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := ((C.subgroupOf J).map q).comap q
  have hCJ : C ≤ J := hCA.trans le_sup_right
  have hcC : (C.subgroupOf J).map q ≤ center (J ⧸ pCore 2 J) :=
    (map_mono (comap_mono hCA)).trans hc
  let : ((C.subgroupOf J).map q).Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hcC hx) g, mul_inv_cancel_right]
    exact hx⟩
  let : N.Normal := inferInstance
  have hN : N.map J.subtype = C ⊔ J.pCoreIn 2 := by
    rw [show N = C.subgroupOf J ⊔ pCore 2 J from by
      change ((C.subgroupOf J).map q).comap q = _
      rw [comap_map_eq,QuotientGroup.ker_mk'],Subgroup.map_sup,
      map_subgroupOf_eq_of_le hCJ]
    rfl
  have hJN : J ≤ normalizer ((C ⊔ J.pCoreIn 2 : Subgroup G) : Set G) := by
    have hh := le_normalizer_map (H := N) J.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hN] at hh
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans hf.local_le
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype hTJ)).trans
      (map_subgroupOf_eq_of_le hTJ).le
  have hUQ : ⁅E.U,E.QH⁆ ≤ E.V₁ :=
    (le_core_iff_commutator_le hf E.QH (pCoreIn_le 2 J)).mp le_rfl
  exact commutator_span_sup_of_normal_modulo D.moduleSubgroup J C (J.pCoreIn 2)
    E.V₁ hCJ (pCoreIn_le 2 J) hJN
    (hQT.trans D.sylow_normalizes_module)
    (fundamental_cartan_subgroup_commutator D c hnat C hCA hC)
    (point_le_span hf) hUQ hf.H_le

set_option backward.isDefEq.respectTransparency false in
/-- No nonidentity Cartan element fixes a nonzero vector of the literal quotient. -/
theorem fundamental_cartan_fixedFree
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hf : (setup T L D.moduleSubgroup H A).Hypothesis)
    (hc : (A.subgroupOf (H ⊔ A)).map
        (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)))
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2)
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X)
    (d : BinaryConjugationSection (H ⊔ A) (setup T L D.moduleSubgroup H A).U
      (setup T L D.moduleSubgroup H A).V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))))
    (a : A) (ha : a ≠ 1) (v : X)
    (hv : ρ (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
      ⟨a,mem_sup_right a.property⟩) v = v) : v = 0 := by
  let C := zpowers (a : G)
  have hCA : C ≤ A := zpowers_le.mpr a.property
  have hC : C ≠ ⊥ := by
    intro he
    apply ha
    have hm : (a : G) ∈ C := mem_zpowers (a : G)
    rw [he,mem_bot] at hm
    exact Subtype.ext hm
  have hm := fundamental_span_cartan_subgroup_moved D c hnat hf C hCA hC hc
  rw [commutator_comm] at hm
  have hl := d.subspaceCommutator_eq_top_of_movement C (hCA.trans le_sup_right) hm.symm
  have he : C.subgroupOf (H ⊔ A) =
      zpowers (⟨a,mem_sup_right a.property⟩ : ↥(H ⊔ A : Subgroup G)) := by
    apply map_injective (H ⊔ A : Subgroup G).subtype_injective
    rw [map_subgroupOf_eq_of_le (hCA.trans le_sup_right),MonoidHom.map_zpowers]
    rfl
  rw [he] at hl
  exact CyclicFixedRank.fixedFree_of_commutator_eq_top _ _ hl v hv
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
