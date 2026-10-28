module
public import Theory.SpecificGroups.SymplecticFour.ThompsonProduct
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoModelNormality
/-! # Original symplectic Thompson product in Chapter 2
Odd component rank gives normality from the original quasithin source tuple.
The literal symplectic action then proves the Thompson product; the component
orbit centralizer identifies its second factor with the original two-core.
The derived-carrier wrapper uses the proved derived-to-whole equivalence for
n>1. No normality, inner Thompson action or component-Sylow containment is added.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
/-- The original Thompson product, with the literal source two-core. -/
theorem MathieuSourceSetup.symplectic_thompson_product
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*Theory.SpecificGroups.SymplecticFour.Sp F) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)=
      ((S:Subgroup H)⊓L.subgroupOf H) ⊔
        (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let := MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF
    (centerQuotientCongr e)
  have he := Theory.SpecificGroups.SymplecticFour.ThompsonInner.thompson_eq_sylow_component_sup_centralizer
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
/-- The literal derived carrier in the original model dispatch. -/
theorem MathieuSourceSetup.derived_symplectic_thompson_product
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)=
      ((S:Subgroup H)⊓L.subgroupOf H) ⊔
        (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact MathieuSourceSetup.symplectic_thompson_product c hG sourceC hempty hgen F hn hF
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
