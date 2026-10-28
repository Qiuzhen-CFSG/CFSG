module
public import Theory.SpecificGroups.PSL3Even.ThompsonProduct
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoModelNormality
/-! # Original Chapter 2 inner Thompson action
The model's odd rank proves normality of the original component. Its actual
root plane then excludes maximum elementary outer actors, giving inner action
of the literal J(S). The later component containment in the displaced-core
normalizer remains a separate source obligation.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
noncomputable def quotientOfLinear (F:Type*) [Field F]
    (e:L≃*PSL(3,F)) : L ⧸ center L ≃* PSL(3,F) := by
  have hc : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  have hl : center L=⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center PSL(3,F) := by
      change (centerCongr e ⟨x,hx⟩ : PSL(3,F)) ∈ center PSL(3,F)
      exact (centerCongr e ⟨x,hx⟩).property
    rw [hc, mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  exact ((QuotientGroup.quotientMulEquivOfEq hl).trans QuotientGroup.quotientBot).trans e

theorem MathieuSourceSetup.linear_simple_thompson_inner
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    let _ := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
      (quotientOfLinear F e)
    (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)).map
      (Matrix.PSL3Even.ThompsonInner.action (L.subgroupOf H)
        ((subgroupOfEquivOfLe c.component_le).trans e))≤MulAut.innerSubgroup PSL(3,F) := by
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  exact Matrix.PSL3Even.ThompsonInner.thompson_action_inner (L.subgroupOf H)
    ((subgroupOfEquivOfLe c.component_le).trans e) hn hF S

/-- The original Thompson product, with the literal source two-core. -/
theorem MathieuSourceSetup.linear_simple_thompson_product
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)=
      ((S:Subgroup H)⊓L.subgroupOf H) ⊔
        (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H) := by
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  have he := Matrix.PSL3Even.ThompsonInner.thompson_eq_sylow_component_sup_centralizer
    (L.subgroupOf H) ((subgroupOfEquivOfLe c.component_le).trans e) hn hF S
  have hg : L.subgroupOf H⊔(S:Subgroup H)=⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  have ho : componentOrbit (L.subgroupOf H) (S:Subgroup H)=L.subgroupOf H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (by rw [normalizer_eq_top]; exact le_top)) (le_componentOrbit _ _)
  have hc := c.component.sylow_centralizer_orbit_eq_pCore S hg
  rw [ho] at hc
  have hJS : Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)≤(S:Subgroup H) :=
    sSup_le fun _ hA => hA.1
  have hi : Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓
      centralizer (L.subgroupOf H:Set H)=
      Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H := by
    rw [←hc,←inf_assoc,inf_eq_left.mpr hJS]
  rwa [hi] at he
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
