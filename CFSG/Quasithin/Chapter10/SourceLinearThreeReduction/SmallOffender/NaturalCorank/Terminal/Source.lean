module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Terminal.Diagonal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Source

/-!
# Selecting and applying the terminal natural TI pair

Four literal conjugators select a noncommuting pair while preserving the
attained full-module offender. The pair theorem constructs its mutual
normalizers and intrinsic two-core escape. A common nonzero T-fixed point of
V and the aligned conjugate full module supplies the remaining diagonal data
and hence the exact TerminalWitness consumed by the centralizer-core argument.

Constructing that common point, the earlier diagonal-core theorem, and model
recognition remain obligations of qt-d-10-nona5-small-offender. This module
neither asserts TerminalConstructionAt nor completes the small-offender theorem.
Source: Aschbacher--Smith, 10.2.12, last paragraph on printed p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

omit [Finite G] in
private theorem terminal_map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a*b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
  Subgroup.conjBy_mul H a b

/-- Right multiplication by an element of M preserves the full attained-offender configuration. -/
theorem configuration_right_mul (c : Configuration T D g)
    {a : G} (ha : a ∈ D.maximalLocal) : Configuration T D (g * a) := by
  have haV : D.fullModule.map (MulAut.conj a).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ha)
  have hV : D.fullModule.map (MulAut.conj (g*a)).toMonoidHom =
      D.fullModule.map (MulAut.conj g).toMonoidHom := by
    rw [terminal_map_conj_mul,haV]
  refine ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
    fun hh => c.outside ((D.maximalLocal.mul_mem_cancel_right ha).mp hh),?_,?_,?_⟩
  · simpa only [hV] using c.noncommuting
  · simpa only [hV] using c.attained
  · simpa only [hV] using c.small

/-- One of the four literal factor pairs is noncommuting. Left alignment lies in M and right multiplication selects a factor. -/
theorem exists_active_alignment
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ a ∈ D.maximalLocal, ∃ x : G,
      (x = a*g ∨ x = (a*g)*t) ∧ Configuration T D x ∧
      ¬ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ≤
        centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let V := D.fullModule
  have htM := le_normalizer_componentOrbit L T ht
  have hgen : V = W ⊔ W.map (MulAut.conj t).toMonoidHom :=
    source_nonnormal_fullModule_eq_moved_pair D c.nonnormal ht (m.crossed t ht htn)
  have hsplit (x : G) : V.map (MulAut.conj x).toMonoidHom =
      W.map (MulAut.conj x).toMonoidHom ⊔ W.map (MulAut.conj (x*t)).toMonoidHom := by
    rw [hgen,Subgroup.map_sup,terminal_map_conj_mul]
  by_cases h₁ : W.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set G)
  · by_cases h₂ : W.map (MulAut.conj (g*t)).toMonoidHom ≤ centralizer (W : Set G)
    · let c' := configuration_left_mul c (D.maximalLocal.inv_mem htM)
      by_cases h₃ : W.map (MulAut.conj (t⁻¹*g)).toMonoidHom ≤ centralizer (W : Set G)
      · by_cases h₄ : W.map (MulAut.conj ((t⁻¹*g)*t)).toMonoidHom ≤ centralizer (W : Set G)
        · have hfirst : V.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set G) := by
            rw [hsplit]
            exact sup_le h₁ h₂
          have hsecond : V.map (MulAut.conj (t⁻¹*g)).toMonoidHom ≤ centralizer (W : Set G) := by
            rw [hsplit]
            exact sup_le h₃ h₄
          have hmap := map_mono (f := (MulAut.conj t).toMonoidHom) hsecond
          rw [←terminal_map_conj_mul,mul_inv_cancel_left,
            Theory.Quasithin.map_centralizer] at hmap
          exact (c.noncommuting (commutator_eq_bot_iff_le_centralizer.mpr
            (hgen.le.trans (sup_le (le_centralizer_iff.mp hfirst)
              (le_centralizer_iff.mp hmap))))).elim
        · exact ⟨t⁻¹,D.maximalLocal.inv_mem htM,(t⁻¹*g)*t,Or.inr rfl,
            configuration_right_mul c' htM,h₄⟩
      · exact ⟨t⁻¹,D.maximalLocal.inv_mem htM,t⁻¹*g,Or.inl rfl,c',h₃⟩
    · exact ⟨1,D.maximalLocal.one_mem,g*t,Or.inr (by simp),
        configuration_right_mul c htM,h₂⟩
  · exact ⟨1,D.maximalLocal.one_mem,g,Or.inl (by simp),c,h₁⟩

/-- Construct the actual noncommuting TI pair, its four-element mutual normalizers, and its escape from the intrinsic two-core. -/
theorem exists_active_aligned_pair
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ a ∈ D.maximalLocal, ∃ x : G,
      (x = a*g ∨ x = (a*g)*t) ∧ Configuration T D x ∧
      (let W := ⁅D.fullModule,L⁆
       let P := W.map (MulAut.conj x).toMonoidHom
       let A := P ⊓ D.maximalLocal
       ¬ P ≤ centralizer (W : Set G) ∧
       A = P ⊓ normalizer (W : Set G) ∧ Nat.card A = 4 ∧
       Nat.card (W ⊓ normalizer (P : Set G) : Subgroup G) = 4 ∧
       ¬ W ≤ (W ⊔ P).pCoreIn 2) := by
  obtain ⟨a,ha,x,hx,cx,hactive⟩ := exists_active_alignment c m ht htn
  have he := cx.attained.symm.trans c.attained
  have hcor : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) =
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
    exact_mod_cast he
  have hxs : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 1 := by
    rw [hcor]
    exact hsmall
  obtain ⟨_,hA,hAc,hUc⟩ := natural_active_pair_normalizers cx m hxs hz hti hactive
  exact ⟨a,ha,x,hx,cx,hactive,hA,hAc,hUc,
    natural_active_pair_core_escape cx m hxs hz hti hactive⟩

/-- The TI-pair argument supplies the terminal witness's core-escape field from the actual diagonal data. -/
theorem terminalWitness_of_active_pair_and_diagonal
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (a t u v x : G) (ha : a ∈ D.maximalLocal)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hu : u ∈ ⁅D.fullModule,L⁆)
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huf : u ∈ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G))
    (hvf : v ∈ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G))
    (hcentral : u*v ∈ centerIn (T : Subgroup G)) (horder : orderOf (u*v) = 2)
    (hconj : D.fullModule.map (MulAut.conj (a*g)).toMonoidHom ≤
      centralizer ({u*v} : Set G))
    (hx : x = a*g ∨ x = (a*g)*t)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    Nonempty (TerminalWitness T D g) := by
  have cx : Configuration T D x := by
    rcases hx with rfl | rfl
    · exact configuration_left_mul c ha
    · exact configuration_right_mul (configuration_left_mul c ha)
        (le_normalizer_componentOrbit L T ht)
  have he := cx.attained.symm.trans c.attained
  have hcor : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) =
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
    exact_mod_cast he
  exact ⟨⟨a,ha,t,ht,htn,u,v,hu,hv,hu1,hv1,huf,hvf,hcentral,horder,hconj,x,hx,
    natural_active_pair_core_escape cx m (by rw [hcor]; exact hsmall) hz hti hactive⟩⟩

/-- A nonzero common T-fixed point completes the literal terminal witness, including its diagonal coordinates and two-core escape. -/
theorem terminalWitness_of_common_central_point
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (a t x z : G) (ha : a ∈ D.maximalLocal)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hx : x = a*g ∨ x = (a*g)*t)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hzcommon : z ∈ D.fullModule ⊓ D.fullModule.map (MulAut.conj (a*g)).toMonoidHom)
    (hzT : z ∈ centralizer ((T : Subgroup G) : Set G)) (hz1 : z ≠ 1) :
    Nonempty (TerminalWitness T D g) := by
  obtain ⟨u,v,hu,hv,hu1,hv1,huf,hvf,huv⟩ := natural_diagonal_of_central_point
    m c.nonnormal ht htn hz z hzcommon.1 hzT hz1
  let : IsElementaryAbelian 2 D.fullModule := m.full_eq_local.symm ▸ D.module_elementary
  let : IsElementaryAbelian 2 (D.fullModule.map (MulAut.conj (a*g)).toMonoidHom) :=
    IsElementaryAbelian.map _
  apply terminalWitness_of_active_pair_and_diagonal c m hsmall hz hti
    a t u v x ha ht htn hu hv hu1 hv1 huf hvf _ _ _ hx hactive
  · rw [huv]
    exact ⟨D.module_le_sylow (m.full_eq_local ▸ hzcommon.1),hzT⟩
  · rw [huv]
    exact orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzcommon.1,hz1⟩
  · rw [huv]
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hw hzcommon.2)

/-- Apply the constructed witness to the actual terminal centralizer-core
contradiction. The remaining source premise is the common T-fixed point. -/
theorem false_of_active_pair_common_point
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆) (hcore : DiagonalCoreAt T)
    (hcommon : ∃ a ∈ D.maximalLocal, ∃ t ∈ (T : Subgroup G),
      t ∉ normalizer (L : Set G) ∧ ∃ x : G,
        (x = a*g ∨ x = (a*g)*t) ∧
        ¬ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ≤
          centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
        ∃ z : G, z ∈ D.fullModule ⊓ D.fullModule.map (MulAut.conj (a*g)).toMonoidHom ∧
          z ∈ centralizer ((T : Subgroup G) : Set G) ∧ z ≠ 1) : False := by
  obtain ⟨a,ha,t,ht,htn,x,hx,hactive,z,hzcommon,hzT,hz1⟩ := hcommon
  obtain ⟨w⟩ := terminalWitness_of_common_central_point c m hsmall hz hti
    a t x z ha ht htn hx hactive hzcommon hzT hz1
  exact w.false_of_diagonal_core c m hcore hz hti

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
