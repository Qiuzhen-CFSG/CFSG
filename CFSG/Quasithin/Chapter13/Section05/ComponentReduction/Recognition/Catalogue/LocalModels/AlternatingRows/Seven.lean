module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.AlternatingRows.Residual
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue
public import Theory.SpecificGroups.AlternatingSeven.ConjugatePairs
public import Theory.SpecificGroups.AlternatingSeven.TranspositionCore

/-!
# Excluding the A₇ rows in the original 13.5.21 configuration

Condition (iv) forces the original actor to induce a transposition: actual
component conjugates otherwise produce elements of orders five or seven.
The resulting permutation equivalence extends the supplied K̂ ≃ A₇ and
preserves conjugation. This step uses no local-core hypothesis.

In these coordinates the actor centralizer is S₅ × C₂. Its O₂,₃, defined as
the preimage of O₃ modulo O₂, is exactly the original V̂. Condition (ii) would
therefore place the nontrivial, two-perfect image of L₁ in a two-group.
The final applications exclude the symmetric degree-seven, exceptional A₇,
and Table B.4.5 A₇ constructors through their actual group comparisons.

The original Selected D K, quotient X/C_X(K*), Prefix and both source
conditions are retained. Configuration and faithful-chief comparisons remain
explicit inputs from their existing producers; no extra marking or core
calculation is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.5.21,
printed pp.923–924 (PDF pp.940–941).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
open Configuration
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- Condition (iv) forces the original order-two actor to be a transposition,
with the original component coordinates and its original conjugation action. -/
theorem source_seven_marked_extension (Y : Subgroup G) (p : Prefix s h Y)
    (hiv : PairCondition s h) (e : Khat s h ≃* alternatingGroup (Fin 7)) :
    ∃ v : Xhat s h, zpowers v = Vhat s h ∧ orderOf v = 2 ∧
      ∃ q : Xhat s h ≃* Equiv.Perm (Fin 7), (q v).IsSwap ∧
        (∀ x : Khat s h, q x = (e x : Equiv.Perm (Fin 7))) ∧
        ∀ (g : Xhat s h) (x : Khat s h)
          (hx : g * (x : Xhat s h) * g⁻¹ ∈ Khat s h),
          (e ⟨g * (x : Xhat s h) * g⁻¹, hx⟩ : Equiv.Perm (Fin 7)) =
            q g * (e x : Equiv.Perm (Fin 7)) * (q g)⁻¹ := by
  let : (Khat s h).Normal := by rw [← p.khat_fitting]; infer_instance
  let : IsCyclic (Vhat s h) := isCyclic_of_prime_card p.actor_card
  obtain ⟨w,hw⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (Vhat s h))
  have ho : orderOf w = 2 := (orderOf_eq_card_of_zpowers_eq_top hw).trans p.actor_card
  let v : Xhat s h := w
  have hv : orderOf v = 2 := (Subgroup.orderOf_coe w).trans ho
  have hz : zpowers v = Vhat s h := eq_of_le_of_card_ge (zpowers_le.mpr w.property) (by
    rw [Nat.card_zpowers, hv, p.actor_card])
  obtain ⟨q,hq,hk,ha⟩ := AlternatingSeven.ConjugatePairs.exists_marked_equiv
    (Khat s h) e (source_centralizer_eq_bot s h Y p) v hv (by
      intro x
      rw [hz]
      exact hiv (x : Xhat s h))
  exact ⟨v,hz,hv,q,hq,hk,fun g x _ => ha g x⟩

/-- The original actor centralizer is C₂ × S₅ in the forced marking. -/
theorem source_seven_centralizer_equiv (Y : Subgroup G) (p : Prefix s h Y)
    (hiv : PairCondition s h) (e : Khat s h ≃* alternatingGroup (Fin 7)) :
    Nonempty (centralizer (Vhat s h : Set (Xhat s h)) ≃*
      (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 5))) := by
  obtain ⟨v,hz,_,q,hq,_,_⟩ := source_seven_marked_extension s h Y p hiv e
  have hC : centralizer (Vhat s h : Set (Xhat s h)) = centralizer ({v} : Set (Xhat s h)) := by
    rw [← hz, zpowers_eq_closure, centralizer_closure]
  obtain ⟨f⟩ := AlternatingSeven.TranspositionCore.transposition_centralizer_equiv q v hq
  exact ⟨(MulEquiv.subgroupCongr hC).trans (f.trans MulEquiv.prodComm)⟩

/-- The literal O₂,₃ of the original actor centralizer is precisely V̂. -/
theorem source_seven_twoThreeCore (Y : Subgroup G) (p : Prefix s h Y)
    (hiv : PairCondition s h) (e : Khat s h ≃* alternatingGroup (Fin 7)) :
    twoThreeCore (centralizer (Vhat s h : Set (Xhat s h))) = Vhat s h := by
  obtain ⟨v,hz,_,q,hq,_,_⟩ := source_seven_marked_extension s h Y p hiv e
  have hC : centralizer (Vhat s h : Set (Xhat s h)) = centralizer ({v} : Set (Xhat s h)) := by
    rw [← hz, zpowers_eq_closure, centralizer_closure]
  rw [hC]
  exact (AlternatingSeven.TranspositionCore.transposition_twoThreeCore q v hq).trans hz

/-- The A₇ branch contradicts condition (ii): a nontrivial two-perfect L̂₁
cannot lie in the two-group O₂,₃ of this centralizer. -/
theorem source_not_seven (Y : Subgroup G) (p : Prefix s h Y)
    (hc : LocalCoreCondition s h) (hiv : PairCondition s h)
    (e : Khat s h ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨hn,hp,_⟩ := source_condition_ii_residual s h Y p hc
  have hl : L1hat s h ≤ Vhat s h := by
    have he := source_seven_twoThreeCore s h Y p hiv e
    exact hc.trans_eq he
  have hv : IsPGroup 2 (Vhat s h) := IsPGroup.of_card (n := 1) (by simpa using p.actor_card)
  have hf := hp.hom_eq_one_of_isPGroup hv (inclusion hl)
  apply hn
  apply le_bot_iff.mp
  intro x hx
  exact congrArg (fun f : L1hat s h →* Vhat s h => (f ⟨x,hx⟩ : Xhat s h)) hf

/-- Apply the exclusion to the exact original pre-B.4 source configuration. -/
theorem source_not_seven_of_configuration
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    (e : Khat s h ≃* alternatingGroup (Fin 7)) : False :=
  source_not_seven s h Y c.proved_prefix c.condition_ii_O23 c.condition_iv e

/-- A comparison with the chief component's central quotient suffices. The row's
actual A₇ isomorphism proves its center trivial, so no identification of a
quasisimple cover with its central quotient is assumed. -/
theorem source_not_seven_chief_quotient
    {F : Type*} [Group F] (L : Subgroup F)
    (comparison : Khat s h ≃* (L ⧸ center L))
    (row : L ≃* alternatingGroup (Fin 7))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) : False := by
  have hZ : center L = ⊥ := by
    apply bot_unique
    intro z hz
    have hr : row z ∈ center (alternatingGroup (Fin 7)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨b,rfl⟩ := row.surjective a
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) b]
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hr
    exact row.injective (hr.trans row.map_one.symm)
  let e : (L ⧸ center L) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans row)
  exact source_not_seven_of_configuration s h Y hY c (comparison.trans e)

open ChapterB.QuasisimpleSource

/-- The symmetric degree-seven constructor supplies its actual marked component equivalence. -/
theorem source_not_symmetricSeven_row
    {F W : Type*} [Group F] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F W) (L H : Subgroup F)
    (comparison : Khat s h ≃* (L ⧸ center L))
    (row : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 7))
      (alternatingGroup (Fin 7)))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) : False :=
  source_not_seven_chief_quotient s h L comparison row.subgroupEquiv Y hY c

/-- The exceptional four-dimensional alternating-seven constructor is excluded
using its actual component isomorphism. -/
theorem source_not_alternatingSeven_row
    {F : Type*} [Group F] (L : Subgroup F)
    (comparison : Khat s h ≃* (L ⧸ center L)) (row : L ≃* alternatingGroup (Fin 7))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) : False :=
  source_not_seven_chief_quotient s h L comparison row Y hY c

/-- Table B.4.5's alternating-seven natural-module row uses its supplied
intertwiner, whose group comparison identifies the same chief component. -/
theorem source_not_tableB45_alternatingSeven_row
    {F W : Type*} [Group F] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F W) (L : Subgroup F)
    (comparison : Khat s h ≃* (L ⧸ center L))
    (row : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) : False :=
  source_not_seven_chief_quotient s h L comparison row.groupEquiv Y hY c

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
