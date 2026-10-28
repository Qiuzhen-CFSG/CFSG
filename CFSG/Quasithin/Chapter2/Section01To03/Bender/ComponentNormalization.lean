module

public import Theory.GroupTheory.StronglyClosedComponentNormalization
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionLocalControl
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The Bender strongly closed subgroup acts on every component

Restrict the selected U to the actual Sylow S of H contained in T.
Ambient strong closure restricts to H, and U remains abelian. Once the
preceding source argument has proved O(H)=1, the generic component theorem
forces U to normalize every component of H. The final application uses the
literal centralizer C_G(u) and its selected Sylow embedding.

This discharges the component-permutation part of the inspection on
printed p.520. Selecting the Bender model and proving that the full U-action
is inner remain separate source obligations.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- After the source odd-core elimination, U normalizes every component
of the actual local subgroup, with the selected Sylow maps unchanged. -/
theorem LocalControlWitness.normalizes_component_of_oddCore_eq_bot
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥) (L : Subgroup G) (hL : IsComponentIn L H) :
    w.U ≤ normalizer (L : Set G) := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let V := w.U.subgroupOf H
  let : IsMulCommutative V := w.U.comap_injective_isMulCommutative H.subtype_injective
  have hUH : w.U ≤ H := hUS.trans (map_subtype_le _)
  have hV : IsStronglyClosedSet (V : Set H) (S : Subgroup H) ⊤ := by
    constructor
    · intro x hx
      obtain ⟨y, hy, he⟩ := hUS hx
      exact (Subtype.ext he : y = x) ▸ hy
    · intro x hx g _ hg
      exact w.strongly_closed.2 x hx g (mem_top _) (hST (mem_map_of_mem H.subtype hg))
  have hN := hL.2.normalized_by_abelian_stronglyClosed_of_pPrimeCore_eq_bot
    S V (L.subgroupOf H) hV hcore
  intro a ha
  have hNa := (L.subgroupOf H).le_normalizer_map H.subtype
    (mem_map_of_mem H.subtype (hN (show (⟨a, hUH ha⟩ : H) ∈ V from ha)))
  simpa only [map_subgroupOf_eq_of_le hL.1, Subgroup.subtype_apply] using hNa

/-- Application to the literal bad-centralizer subgroup in Proposition 2.2.2.
The source owner still supplies its Sylow placement and preceding O(H)=1 proof. -/
theorem LocalControlWitness.normalizes_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G))) :
    w.U ≤ normalizer (L : Set G) :=
  w.normalizes_component_of_oddCore_eq_bot (centralizer ({u} : Set G)) S hUS hST hcore L hL

end CFSG.Quasithin.Chapter2.BenderFusion
