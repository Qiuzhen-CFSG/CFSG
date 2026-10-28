module

public import Theory.Frattini.CentralElementarySupplement
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.Commutator.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The common fixed subgroup in DGS 9.10(4)

Write `D = C_{Q_(alpha-1)}(K_(alpha-1))`, `R = Q_(alpha')`,
`Q = C_R(K)` and `H = Q_(alpha+2) ∩ Q_(alpha'+1)`. The two Cartan
factors generate `K`. Normalization places `[D ∩ H,K_(alpha')]` in `D`,
whereas (1) places it in `V_(alpha')`. The fixed-point-free action in
5.1 makes these two subgroups disjoint, so `D ∩ H = Q`. The splitting
from (2) then gives `D = Z_(alpha-1) × Q`; the order comparison in (4)
gives `H = Q × V_(alpha')`.

The action, order and Frattini inputs are explicit. In particular the
centralizer of `K_(alpha')` in `H` is not assumed to equal `Q`:
the argument uses both Cartan factors and the original ambient core.
Source: DGS, *Groups and Graphs* (1985), 9.10(4), printed pp.148--149.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

variable {G : Type*} [Group G]

/-- The normalized intersection centralizes the second Cartan factor,
and therefore equals the common fixed subgroup of the two factors. -/
theorem cartan_fixed_intersection
    (D R H V T K : Subgroup G)
    (hDT : D ≤ centralizer (T : Set G))
    (hDR : D ⊓ H ≤ R)
    (hfixed : R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G) ≤ D ⊓ H)
    (hn : K ≤ normalizer ((D ⊓ H : Subgroup G) : Set G))
    (hm : ⁅H,K⁆ ≤ V)
    (hd : Disjoint D V) :
    D ⊓ H = R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G) := by
  have hc : ⁅D ⊓ H,K⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf
      ((le_normalizer_iff_commutator_le_left.mp hn).trans inf_le_left)
      ((commutator_mono inf_le_right le_rfl).trans hm)).trans hd.le_bot
  apply le_antisymm ?_ hfixed
  refine le_inf hDR ?_
  apply le_centralizer_iff.mpr
  apply sup_le
  · exact le_centralizer_iff.mp (inf_le_left.trans hDT)
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The common fixed part in (4), using the literal source split through
`R = Q_(alpha')`. The last inequality is precisely the order comparison,
not a premise asserting the second direct-product equality. -/
theorem cartan_fixed_decomposition
    (D Z R H V T K : Subgroup G) [Finite H]
    (hDT : D ≤ centralizer (T : Set G))
    (hDR : D ⊓ H ≤ R)
    (hfixed : R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G) ≤ D ⊓ H)
    (hn : K ≤ normalizer ((D ⊓ H : Subgroup G) : Set G))
    (hm : ⁅H,K⁆ ≤ V)
    (hd : Disjoint D V)
    (hDsplit : D = Z ⊔ (D ⊓ R))
    (hDdis : Disjoint Z (D ⊓ R))
    (hDZ : ⁅Z,D ⊓ R⁆ = ⊥)
    (hDRH : D ⊓ R ≤ H)
    (hVH : V ≤ H)
    (hQV : ⁅R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G),V⁆ = ⊥)
    (hcard : Nat.card H ≤
      Nat.card (R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G) : Subgroup G) * Nat.card V) :
    let Q := R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G)
    D ⊓ H = Q ∧ D ⊓ R = Q ∧
      D = Z ⊔ Q ∧ Disjoint Z Q ∧ ⁅Z,Q⁆ = ⊥ ∧
      H = Q ⊔ V ∧ Disjoint Q V ∧ ⁅Q,V⁆ = ⊥ := by
  let Q := R ⊓ centralizer ((T ⊔ K : Subgroup G) : Set G)
  have hDH : D ⊓ H = Q := cartan_fixed_intersection D R H V T K hDT hDR hfixed hn hm hd
  have hQDH : Q ≤ D ⊓ H := hfixed
  have hDQ : D ⊓ R = Q := le_antisymm
    ((le_inf inf_le_left hDRH).trans hDH.le)
    (le_inf (hQDH.trans inf_le_left) inf_le_left)
  have hdis : Disjoint Q V := hd.mono_left (hQDH.trans inf_le_left)
  have hgen : H = Q ⊔ V := by
    apply (eq_of_le_of_card_ge (sup_le (hQDH.trans inf_le_right) hVH) ?_).symm
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQV)).trans
        (centralizer_le_normalizer _)) hdis]
    exact hcard
  refine ⟨hDH,hDQ,?_,?_,?_,hgen,hdis,hQV⟩
  · simpa only [hDQ] using hDsplit
  · simpa only [hDQ] using hDdis
  · simpa only [hDQ] using hDZ

/-- The elementary central factor in the second direct product contributes
nothing to the ambient Frattini subgroup. -/
theorem cartan_fixed_frattini_comparison
    (H Q V : Subgroup G) [Finite H]
    (hp : IsPGroup 2 H) (he : IsElementaryAbelian 2 V)
    (hc : ⁅Q,V⁆ = ⊥) (hH : H = Q ⊔ V) :
    (frattini H).map H.subtype = (frattini Q).map Q.subtype := by
  have hQH : Q ≤ H := hH ▸ le_sup_left
  have hVH : V ≤ H := hH ▸ le_sup_right
  let : IsElementaryAbelian 2 V := he
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  have hcentral : V ≤ centralizer (H : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hH]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hc) (le_centralizer V)
  have hh := frattini_map_eq_of_central_elementary_supplement
    (⊤ : Subgroup H) (Q.subgroupOf H) (V.subgroupOf H)
    (hp.to_subgroup ⊤) inferInstance
    (by intro v hv a _; exact Subtype.ext (hcentral hv a a.property))
    (by rw [←subgroupOf_sup hVH hQH,sup_comm,←hH,subgroupOf_self])
  have ht := frattini_image_map (⊤ : Subgroup H) H.subtype H.subtype_injective
  rw [←MonoidHom.range_eq_map,range_subtype] at ht
  have hQ := frattini_image_map (Q.subgroupOf H) H.subtype H.subtype_injective
  rw [map_subgroupOf_eq_of_le hQH] at hQ
  exact ht.trans ((congrArg (Subgroup.map H.subtype) hh).trans hQ.symm)

/-- The Frattini end of (4), separated from the preceding fixed-subgroup
and order argument. -/
theorem cartan_fixed_elementary (Q : Subgroup G) [Finite Q]
    (hp : IsPGroup 2 Q) (hphi : frattini Q = ⊥) : IsElementaryAbelian 2 Q := by
  let : Fact (IsPGroup 2 Q) := ⟨hp⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (R := Q) (p := 2)).mp hphi

/-- Formal end of source 9.10(5), after the common fixed subgroup is placed
in the central line. -/
theorem cartan_fixed_Q_eq_bot
    (Q Z : Subgroup G) (hQZ : Q ≤ Z) (hdis : Disjoint Q Z) : Q = ⊥ :=
  disjoint_self.mp (hdis.mono_right hQZ)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
