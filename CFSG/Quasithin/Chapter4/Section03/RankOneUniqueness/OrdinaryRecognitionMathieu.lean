module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionSymplectic
public import Theory.Mathieu.M22.Properties.LocalA5Placement
public import Theory.Mathieu.M22.Properties.LocalA5Shape
public import Theory.Mathieu.M22.Properties.MarkedA5Fixer
public import Theory.Mathieu.M22.Properties.InvolutionFixedOrders
public import Theory.Mathieu.M23.Properties.A5Fixer
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.PSL2Cardinality

/-!
# Mathieu exclusions for the original ordinary configuration

The image of the original L in any central-quotient model of K retains its
quotient by O₂: the kernel is contained in Z(K) = O₂(K). Its order is therefore
divisible by the order of the given PSL₂(2ⁿ). The actual R₀ action supplies an
involutory automorphism fixing this same image pointwise.

For M₂₃ every such automorphism is inner and its fixed subgroup has order 2688,
which excludes all n > 1. In M₂₂ the order first restricts n to 2 or 3. The n = 3
case is excluded by the absence of a factor 9 in an involution's fixed subgroup.
For n = 2 the original full Sylow normalizes the original local image; its local
component and quotient data give the natural E₁₆:A₅ placement. The marked fixer
theorem then excludes the actual R₀ involution. No block placement, full-module
equality, or model-action hypothesis is added to the source configuration.

These are the Mathieu exclusions used in Aschbacher--Smith 4.3.6, printed p.614,
following the local-pair alternatives of C.3.1, printed pp.149--151. Exhaustion
by those alternatives and final construction of OrdinarySymplecticMarking remain
with qt-d-1222-rankone-ordinary-symplectic-marking.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace SourceConfiguration

/-- Passing to the actual central-quotient model preserves the quotient of the
original local subgroup by its two-core. -/
theorem ordinary_model_local_quotient_equiv (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {S : Type*} [Group S] [Finite S]
    (e : (c.K ⧸ center c.K) ≃* S) :
    let B := c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))
    Nonempty ((L ⧸ pCore 2 L) ≃* (B ⧸ pCore 2 B)) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let k : L ≃* c.ordinaryLocal := c.ordinaryLocalEquiv.symm
  let f := (q.subgroupMap c.ordinaryLocal).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective c.ordinaryLocal).comp k.surjective
  have hqker : q.ker = center c.K := by
    ext x
    change e (QuotientGroup.mk' (center c.K) x) = 1 ↔ x ∈ center c.K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 q.ker := by
    rw [hqker,c.ordinary_center_eq_twoCore ho]
    exact pCore_isPGroup
  have hker : f.ker = q.ker.comap (c.ordinaryLocal.subtype.comp k.toMonoidHom) := by
    ext x
    exact Subtype.ext_iff
  have hfp : IsPGroup 2 f.ker := by
    rw [hker]
    exact hp.comap_of_injective _ (c.ordinaryLocal.subtype_injective.comp k.injective)
  exact ⟨f.pCoreQuotientEquiv hf hfp⟩

/-- The original rank-one quotient forces its order to divide the order of the
literal local image in every central-quotient model. -/
theorem ordinary_model_local_order_dvd (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {S : Type*} [Group S] [Finite S]
    (e : (c.K ⧸ center c.K) ≃* S) {n : ℕ}
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card
      (c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))) := by
  let B := c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv ho e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hcard : Nat.card (B ⧸ pCore 2 B) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr b.toEquiv,←Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
  rw [←hcard]
  exact card_quotient_dvd_card (pCore 2 B)

private theorem binary_order_not_dvd_2688 {n : ℕ} (hn : 1 < n)
    (hd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 2688) : False := by
  have hd2 : 2 ^ n ∣ 2688 := (dvd_mul_right _ _).trans hd
  have hb : n < 8 := by
    by_contra! hn8
    have hh := (Nat.pow_dvd_pow 2 hn8).trans hd2
    norm_num at hh
  interval_cases n <;> norm_num at hd

/-- The actual R₀ involution excludes every M₂₃ central quotient of the ordinary
component, using the original local image and rank-one field size. -/
theorem ordinary_no_m23 (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Sporadic.Mathieu.M23) : False := by
  let B := c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))
  obtain ⟨a,ha,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
  have hB : B ≤ a.fixedSubgroup := fun b hb => (MulAut.mem_fixedSubgroup a b).mpr (hfix b hb)
  obtain ⟨g,hg⟩ := Sporadic.Mathieu.m23_conj_surjective a
  obtain ⟨b⟩ := Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.fixedSubgroup_equiv_representative_of_inner
    a ha ⟨g,hg.symm⟩
  have hc : Nat.card a.fixedSubgroup = 2688 :=
    (Nat.card_congr b.toEquiv).trans
      Sporadic.Mathieu.M23Geometry.involutionRepresentative_centralizer_card
  exact binary_order_not_dvd_2688 hn
    (hc ▸ (c.ordinary_model_local_order_dvd ho e hpsl).trans (card_dvd_of_le hB))

private theorem binary_degree_of_dvd_m22 {n : ℕ} (hn : 1 < n)
    (hd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 443520) : n = 2 ∨ n = 3 := by
  have hd2 : 2 ^ n ∣ 443520 := (dvd_mul_right _ _).trans hd
  have hb : n < 8 := by
    by_contra! hn8
    have hh := (Nat.pow_dvd_pow 2 hn8).trans hd2
    norm_num at hh
  interval_cases n <;> first | exact Or.inl rfl | exact Or.inr rfl | norm_num at hd

/-- The original full-Sylow local data and actual R₀ action exclude every M₂₂
central quotient of the ordinary component. The natural A₅ placement is derived
inside this proof, including the original field-size-four case. -/
theorem ordinary_no_m22 (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Sporadic.Mathieu.M22) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  have hd := c.ordinary_model_local_order_dvd ho e hpsl
  have hdn : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 443520 := by
    rw [←Sporadic.Mathieu.m22_order]
    exact hd.trans B.card_subgroup_dvd_card
  rcases binary_degree_of_dvd_m22 hn hdn with hn2 | hn3
  · obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv ho e
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
    have hF4 : Nat.card F = 4 := by
      norm_num [hn2] at hF
      exact hF
    obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
    let eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5) := b.trans d
    obtain ⟨P,hP,hlocal,_⟩ := c.ordinary_model_local_data D ho e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center c.K)))
    have hnorm : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans (c.ordinaryLocal.le_normalizer_map f)
      rw [hP]
      exact c.ordinary_component_sylow_normalizes_local D
    obtain ⟨hE,h16⟩ := Sporadic.Mathieu.M22LocalA5Shape.core_shape_of_normalized S B hnorm eB
    let := c.ordinaryLocal_perfect
    let : Group.IsPerfect B := Group.IsPerfect.map f
    obtain ⟨v,hv⟩ := Sporadic.Mathieu.M22LocalA5Placement.exists_marking S B hlocal.subnormal hE h16 eB
    let e' := e.trans v
    have he' : c.ordinaryLocal.map (e'.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
        B.map v.toMonoidHom := by
      rw [map_map]
      rfl
    obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e'
    rw [he'] at hfix
    have hh := Sporadic.Mathieu.m22_marked_involutory_fixer_eq_one (B.map v.toMonoidHom)
      hv r (hr ▸ pow_orderOf_eq_one r) hfix
    simp only [hh,orderOf_one] at hr
    omega
  · obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
    have hB : B ≤ r.fixedSubgroup := fun b hb => (MulAut.mem_fixedSubgroup r b).mpr (hfix b hb)
    have hd9 : 9 ∣ Nat.card B := (by norm_num [hn3] : 9 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1)).trans hd
    exact Sporadic.Mathieu.m22_involution_not_nine_dvd_fixed_card r hr
      (hd9.trans (card_dvd_of_le hB))

end SourceConfiguration
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
