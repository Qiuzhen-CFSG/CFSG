module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Recognition
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.SpecificGroups.SL2.FieldCardinality
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Quotient
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
/-!
# The original rank-one quotient and its field degree

The original L maps onto its literal image in K/O₂(K) with two-group kernel.
Taking two-core quotients therefore identifies L/O₂(L) with that image's
core quotient. The concrete SL₃ and Sp₄ parabolic markings identify the latter
with SL₂ over the same field. Its order then recovers the original field degree.

These statements use only the quotient marking and the genuine configuration;
no natural-module recognition is assumed. They supply the parameter comparison
in the C.4.1 block-row assembly, owned by the rank-one block-exclusion task.
Source: Aschbacher–Smith C.4.1(2–3), C.4.7, pp.151–153, and 4.3.7, pp.615–616.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
omit [Finite G] in
theorem SourceConfiguration.originalLocal_le (c : SourceConfiguration T L) : L.subgroupOf c.H ≤ c.K := by
  intro x hx
  obtain ⟨k,hk,he⟩ := c.le_component hx
  exact (Subtype.ext he : k = x) ▸ hk

@[expose] noncomputable def SourceConfiguration.originalLocalEquiv
    (c : SourceConfiguration T L) : ((L.subgroupOf c.H).subgroupOf c.K) ≃* L :=
  (subgroupOfEquivOfLe c.originalLocal_le).trans
    (subgroupOfEquivOfLe (c.le_I.trans c.I_le_H))

@[expose] noncomputable def SourceConfiguration.originalLocalProjection
    (c : SourceConfiguration T L) : L →* c.componentQuotientL :=
  ((QuotientGroup.mk' (pCore 2 c.K)).subgroupMap
    ((L.subgroupOf c.H).subgroupOf c.K)).comp c.originalLocalEquiv.symm.toMonoidHom

omit [Finite G] in
theorem SourceConfiguration.originalLocalProjection_surjective
    (c : SourceConfiguration T L) : Function.Surjective c.originalLocalProjection :=
  ((QuotientGroup.mk' (pCore 2 c.K)).subgroupMap_surjective _).comp
    c.originalLocalEquiv.symm.surjective

omit [Finite G] in
theorem SourceConfiguration.originalLocalProjection_kernel_two
    (c : SourceConfiguration T L) : IsPGroup 2 c.originalLocalProjection.ker := by
  let f := ((L.subgroupOf c.H).subgroupOf c.K).subtype.comp
    c.originalLocalEquiv.symm.toMonoidHom
  have hf : Function.Injective f :=
    ((L.subgroupOf c.H).subgroupOf c.K).subtype_injective.comp
      c.originalLocalEquiv.symm.injective
  have hk : c.originalLocalProjection.ker = (pCore 2 c.K).comap f := by
    ext x
    change c.originalLocalProjection x = 1 ↔ f x ∈ pCore 2 c.K
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (f x)
  rw [hk]
  exact pCore_isPGroup.comap_of_injective f hf

@[expose] noncomputable def SourceConfiguration.originalLocalCoreEquiv
    (c : SourceConfiguration T L) :
    (L ⧸ pCore 2 L) ≃* (c.componentQuotientL ⧸ pCore 2 c.componentQuotientL) :=
  c.originalLocalProjection.pCoreQuotientEquiv c.originalLocalProjection_surjective
    c.originalLocalProjection_kernel_two

@[simp] theorem SourceConfiguration.originalLocalCoreEquiv_mk
    (c : SourceConfiguration T L) (l : L) :
    c.originalLocalCoreEquiv (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 c.componentQuotientL) (c.originalLocalProjection l) := rfl

/-- Transport to the two-core quotient of a marked local image. -/
@[expose] noncomputable def SourceConfiguration.originalLocalModelCoreEquiv
    (c : SourceConfiguration T L) {A : Type*} [Group A]
    (e : (c.K ⧸ pCore 2 c.K) ≃* A) (B : Subgroup A)
    (he : c.componentQuotientL.map e.toMonoidHom = B) :
    (L ⧸ pCore 2 L) ≃* (B ⧸ pCore 2 B) := by
  let a := (e.subgroupMap c.componentQuotientL).trans (MulEquiv.subgroupCongr he)
  exact c.originalLocalCoreEquiv.trans (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))

/-- The original L core quotient in either SL₃ parabolic marking. -/
theorem SourceConfiguration.originalLocal_sl2_of_linearThree
    (c : SourceConfiguration T L) {m : ℕ} (hm : 1 < m)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ChapterC.IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2^m)
    (e : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F)) := by
  obtain ⟨a,ha | ha⟩ := c.block_linearThree_local_frame hm hf hb hF e
  · exact ⟨(c.originalLocalModelCoreEquiv _ _ ha).trans
      (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F)⟩
  · exact ⟨(c.originalLocalModelCoreEquiv _ _ ha).trans
      (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F)⟩

/-- The original L core quotient in either Sp₄ parabolic marking. -/
theorem SourceConfiguration.originalLocal_sl2_of_symplectic
    (c : SourceConfiguration T L) {m : ℕ} (hm : 1 < m)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ChapterC.IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2^m)
    (e : (c.K ⧸ pCore 2 c.K) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F)) := by
  obtain ⟨a,ha | ha⟩ := c.block_symplectic_local_conjugate hm hf hb hF e
  · exact ⟨(c.originalLocalModelCoreEquiv _ _ ha).trans
      (Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hm)⟩
  · exact ⟨(c.originalLocalModelCoreEquiv _ _ ha).trans
      (Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hm)⟩
omit [Finite G] in
/-- Comparing the actual original quotient with a local SL₂ model determines
its field cardinality. -/
theorem original_local_field_card {n : ℕ}
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {F : Type*} [Field F] [Finite F]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : Nat.card F = 2 ^ n := by
  obtain ⟨E, _, _, hE, ⟨a⟩⟩ := hpsl
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hE)
  exact (Matrix.SL2.field_card_eq_of_equiv
    (e.symm.trans (a.trans (Theory.PSL2.sl2QuotientEquiv E).symm))).trans hE

/-- The SL₃ marking has the original source degree, not an unrelated binary
field parameter from the star catalogue. -/
theorem SourceConfiguration.original_degree_of_linearThree
    (c : SourceConfiguration T L) {n m : ℕ} (hm : 1 < m)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ChapterC.IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ m)
    (e : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F)) : m = n := by
  obtain ⟨a⟩ := c.originalLocal_sl2_of_linearThree hm hf hb hF e
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    (hF.symm.trans (original_local_field_card hpsl a))

/-- The symplectic marking recovers the same original degree through either
parabolic residual. No natural-module or field-four conclusion is assumed. -/
theorem SourceConfiguration.original_degree_of_symplectic
    (c : SourceConfiguration T L) {n m : ℕ} (hm : 1 < m)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ChapterC.IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ m)
    (e : (c.K ⧸ pCore 2 c.K) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : m = n := by
  obtain ⟨a⟩ := c.originalLocal_sl2_of_symplectic hm hf hb hF e
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    (hF.symm.trans (original_local_field_card hpsl a))

/-- The actual original core quotient is a section of the full component core quotient. -/
theorem SourceConfiguration.original_core_card_dvd
    (c : SourceConfiguration T L) :
    Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (c.K ⧸ pCore 2 c.K) := by
  rw [Nat.card_congr c.originalLocalCoreEquiv.toEquiv]
  exact (pCore 2 c.componentQuotientL).card_quotient_dvd_card.trans
    c.componentQuotientL.card_subgroup_dvd_card

omit [Finite G] in
/-- The original rank-one quotient has its defining SL₂ order. -/
theorem original_core_card {n : ℕ}
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Nat.card (L ⧸ pCore 2 L) = 2 ^ n * ((2 ^ n)^2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr (a.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]

/-- The SL₃(2) quotient cannot contain the original rank-one section. -/
theorem SourceConfiguration.block_quotient_not_card168
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hc : Nat.card (c.K ⧸ pCore 2 c.K) = 168) : False := by
  have hd := c.original_core_card_dvd
  rw [original_core_card hpsl,hc] at hd
  by_cases hn2 : n = 2
  · norm_num [hn2] at hd
  have hn3 : 3 ≤ n := by omega
  have hq : 8 ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn3
  have hq2 : 64 ≤ (2 ^ n)^2 := by nlinarith
  have he := Nat.le_of_dvd (by decide : 0 < 168) hd
  have hm := Nat.mul_le_mul hq (Nat.sub_le_sub_right hq2 1)
  norm_num at hm
  omega

/-- Even before recognizing the module, the SL₃ row has degree greater than one. -/
theorem SourceConfiguration.linearThree_degree_gt_one
    (c : SourceConfiguration T L) {n m : ℕ} (hn : 1 < n) (hm : 0 < m)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2 ^ m)
    (e : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F)) : 1 < m := by
  by_contra hh
  have hm1 : m = 1 := by omega
  apply c.block_quotient_not_card168 hn hpsl
  rw [Nat.card_congr e.toEquiv,
    Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF,hm1]
  norm_num

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
