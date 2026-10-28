module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Components
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The ordinary-component obstruction and relative centralizers

In a group with trivial odd core, every source C-component is either an
ordinary component or has generalized Fitting subgroup equal to its two-core.
Indeed, otherwise its own generalized Fitting subgroup supplies an ordinary
component; minimality of the original C-component identifies the two.

The centralizer of a C-component is handled separately. Intersecting a
subnormal chain with C_I(z) proves relative subnormality of C_K(z). Thus
characteristic two passes from C_I(z) to C_K(z), without asserting that K is
ordinary or normal in I. In the application C_I(z) = I ∩ M_c, so 1.1.5(1)
supplies the required characteristic-two input directly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.33(3), printed p.1134; A.3.1--3, pp.41--43, and 1.1.5, pp.501--503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The literal centralizer of z in K, where K is a subgroup of I. -/
def centralizerIn {I : Subgroup G} (K : Subgroup I) (z : G) : Subgroup K :=
  (centralizer ({z} : Set G)).comap (I.subtype.comp K.subtype)

private theorem fstar_eq_twoCore_of_selfCentralizing
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    generalizedFitting G = pCore 2 G := by
  apply le_antisymm
  · apply sup_le
    · exact (Fitting_eq_pcore G 2
        (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)).le
    · apply sSup_le
      intro L hL
      rcases hL.normal_dichotomy (pCore 2 G) with h | h
      · exact h
      · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans hc
  · exact (pCore_le_fitting G 2).trans (fitting_le_generalizedFitting G)

/-- The precise residual obstruction to treating a source C-component as an
ordinary one. Trivial odd core alone leaves the characteristic-two branch. -/
theorem cComponent_ordinary_or_characteristicTwo {K : Subgroup G}
    (hK : K.IsCComponent) (hodd : pPrimeCore 2 G = ⊥) :
    IsComponent G K ∨ generalizedFitting K = pCore 2 K := by
  by_cases hF : generalizedFitting K = pCore 2 K
  · exact Or.inr hF
  obtain ⟨L, hL⟩ := exists_ordinary_component_of_fstar_ne_twoCore
    (cComponent_oddCore_eq_bot hK hodd) hF
  have he : L = ⊤ := hK.eq_top_of_isCComponent (component_isCComponent hL)
  let := hL.2
  have hq : IsQuasisimple K := IsQuasisimple.of_mulEquiv
    ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv)
  exact Or.inl ⟨hK.subnormal, hq⟩

omit [Finite G] in
/-- Centralizers are subnormal in the ambient centralizer, via restriction of
the subnormal chain; the groups need not be normal in I. -/
theorem centralizer_subnormal {I : Subgroup G} {K : Subgroup I}
    (hK : K.IsSubnormal) (z : G) :
    (K.subgroupOf ((centralizer ({z} : Set G)).comap I.subtype)).IsSubnormal :=
  hK.subgroupOf

/-- Characteristic two passes to C_K(z) for every subnormal K in I. -/
theorem centralizerIn_characteristicTwo {I : Subgroup G} {K : Subgroup I}
    (hK : K.IsSubnormal) (z : G)
    (hc : centralizer (pCore 2 ((centralizer ({z} : Set G)).comap I.subtype) :
        Set ((centralizer ({z} : Set G)).comap I.subtype)) ≤
      pCore 2 ((centralizer ({z} : Set G)).comap I.subtype)) :
    generalizedFitting (centralizerIn K z) = pCore 2 (centralizerIn K z) := by
  let C := (centralizer ({z} : Set G)).comap I.subtype
  let e : K.subgroupOf C ≃* centralizerIn K z :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  apply fstar_eq_twoCore_of_selfCentralizing
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    (subnormal_core_selfCentralizing hc (K.subgroupOf C) (centralizer_subnormal hK z))

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
