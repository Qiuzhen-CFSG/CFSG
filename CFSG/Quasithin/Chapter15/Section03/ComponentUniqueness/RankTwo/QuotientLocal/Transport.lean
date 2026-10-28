module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Reductions
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.CentralizerPrimeKernel
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group


/-!
# Transport into the local component quotient

These results work in the actual I/C_I(L). The kernel is a two-group:
its intersection with L is Z(L), while its image in I/L is a two-group.
Consequently the quotients modulo O₂, and then modulo O_{2,Φ}, are unchanged.
This transports the full rank-two shadow, along with the Sylow subgroup,
containments, relative normality and the theta normalizer.

Maximality among subgroups with F*=O₂ follows by pulling a competitor back
to I, lifting characteristic two through the two-group kernel, and applying
15.3.25 to that actual outside overgroup. The nontrivial two-core comes from
O₂(I)≤S; it is not an additional assumption on the competitor.

The actual central-quotient equivalences also transport upstream model
identifications to L⁺. The source model alternatives must still be supplied.
The two-local property and characteristic two of M_I⁺ are separate remaining
arguments; this module does not assert LocalConfiguration.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11, 15.3.25, 15.3.36 and 15.3.41, printed pp.1123, 1130, 1135, 1138.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Transport through an actual surjection with two-group kernel. -/
noncomputable def twoFrattiniQuotientEquiv {H : Type*} [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    G ⧸ twoFrattiniCore G ≃* H ⧸ twoFrattiniCore H :=
  QuotientGroup.equivOfSurjectiveComap f hf _ _
    (f.comap_frattini_pCore_of_pKernel hf hk)

theorem rankTwoShadow_map {H : Type*} [Group H] [Finite G] [Finite H]
    (f : G →* H) (hk : IsPGroup 2 f.ker) {Y S : Subgroup G}
    (h : RankTwoShadow Y S) : RankTwoShadow (Y.map f) (S.map f) := by
  obtain ⟨e⟩ := h
  have hker : IsPGroup 2 (f.subgroupMap (Y ⊔ S)).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let a := MulEquiv.subgroupCongr (Subgroup.map_sup Y S f)
  let b := twoFrattiniQuotientEquiv a.toMonoidHom a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)
  exact ⟨b.symm.trans ((twoFrattiniQuotientEquiv _
    (f.subgroupMap_surjective _) hker).symm.trans e)⟩

theorem rankTwoShadow_subgroupOf [Finite G] {Y S I : Subgroup G}
    (hY : Y ≤ I) (hS : S ≤ I) (h : RankTwoShadow Y S) :
    RankTwoShadow (Y.subgroupOf I) (S.subgroupOf I) := by
  have he : (Y ⊔ S).subgroupOf I = Y.subgroupOf I ⊔ S.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (sup_le hY hS), Subgroup.map_sup,
      map_subgroupOf_eq_of_le hY, map_subgroupOf_eq_of_le hS]
  let e := (MulEquiv.subgroupCongr he.symm).trans (subgroupOfEquivOfLe (sup_le hY hS))
  have hker : IsPGroup 2 e.toMonoidHom.ker := IsPGroup.ker_isPGroup_of_injective e.injective
  have hi := (twoFrattiniQuotientEquiv e.toMonoidHom e.surjective hker)
  exact ⟨hi.trans h.some⟩

/-- 15.3.11(1) gives the Sylow subgroup in the actual component quotient. -/
theorem componentImage_sylow [Finite G] (I L S : Subgroup G)
    [(L.subgroupOf I).Normal]
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S) :
    ∃ Q : Sylow 2 (ComponentQuotient I L), (Q : Subgroup _) = componentImage I L S := by
  have hPS : (P : Subgroup I) = S.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (hP ▸ map_subtype_le _)]
  exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, hPS]; rfl⟩

/-- Containment and normality in the local component intersection are
transported from the actual normalizer conclusion 15.3.11(4). -/
theorem componentImage_normal_in_intersection
    (I L M Y : Subgroup G) [(L.subgroupOf I).Normal]
    (hYL : Y ≤ L) (hYI : Y ≤ I)
    (hN : I ⊓ normalizer (Y : Set G) = M ⊓ I)
    (hYM : Y ≤ M) :
    componentImage I L Y ≤ componentImage I L M ⊓ componentImage I L L ∧
      ((componentImage I L Y).subgroupOf
        (componentImage I L M ⊓ componentImage I L L)).Normal := by
  have hn : M.subgroupOf I ≤ normalizer (Y.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hYI]
    intro x hx
    exact (hN.ge ⟨hx, x.property⟩).2
  refine ⟨le_inf (map_mono (comap_mono hYM)) (map_mono (comap_mono hYL)), ?_⟩
  apply normal_subgroupOf_of_le_normalizer
  exact inf_le_left.trans ((map_mono hn).trans (Subgroup.le_normalizer_map _))
end CFSG.Quasithin.Chapter15.Section03.RankTwo

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem join_subgroupOf_eq_top {I L S : Subgroup G}
    (hLI : L ≤ I) (hI : I = L ⊔ S) : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
  apply Subgroup.map_injective I.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI,
    map_subgroupOf_eq_of_le (hI ▸ le_sup_right)]
  simpa only [← MonoidHom.range_eq_map, range_subtype] using hI.symm

omit [Finite G] in
/-- The actual relative centralizer denominator is a two-group. -/
theorem component_kernel_isTwoGroup {I L S : Subgroup G} [(L.subgroupOf I).Normal]
    (hLI : L ≤ I) (hI : I = L ⊔ S) (hS : IsPGroup 2 S)
    (hZ : IsPGroup 2 (center L)) :
    IsPGroup 2 (centralizerQuotientMap (L.subgroupOf I)).ker := by
  rw [centralizerQuotientMap, QuotientGroup.ker_mk']
  exact isPGroup_centralizer_of_quotient _
    (isPGroup_quotient_of_sup_eq_top _ _ hS.comap_subtype
      (join_subgroupOf_eq_top hLI hI)) (hZ.of_injective
      (centerCongr (subgroupOfEquivOfLe hLI)).toMonoidHom
      (centerCongr (subgroupOfEquivOfLe hLI)).injective)

/-- The full rank-two quotient of 15.3.36 survives the component quotient. -/
theorem componentImage_rankTwoShadow {I L S Y : Subgroup G} [(L.subgroupOf I).Normal]
    (hLI : L ≤ I) (hI : I = L ⊔ S) (hS : IsPGroup 2 S)
    (hZ : IsPGroup 2 (center L)) (hYL : Y ≤ L) (h : RankTwoShadow Y S) :
    RankTwoShadow (componentImage I L Y) (componentImage I L S) :=
  rankTwoShadow_map _ (component_kernel_isTwoGroup hLI hI hS hZ)
    (rankTwoShadow_subgroupOf (hYL.trans hLI) (hI ▸ le_sup_right) h)

omit [Finite G] in
/-- The normalizer equality is in I/C_I(L), with theta transported from M∩I. -/
theorem componentImage_normalizer (I L M Y : Subgroup G) [(L.subgroupOf I).Normal]
    (hLI : L ≤ I) (hYL : Y ≤ L)
    (hθ : theta (M ⊓ I) = Y)
    (hN : I ⊓ normalizer (Y : Set G) = M ⊓ I) :
    normalizer (componentImage I L Y : Set (ComponentQuotient I L)) =
      componentImage I L M := by
  have hYI := hYL.trans hLI
  have hθI : theta (M.subgroupOf I) = Y.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [theta_map_of_injective I.subtype I.subtype_injective,
      subgroupOf_map_subtype, hθ, map_subgroupOf_eq_of_le hYI]
  have hNI : normalizer (Y.subgroupOf I : Set I) = M.subgroupOf I := by
    rw [← subgroupOf_normalizer_eq hYI]
    ext x
    exact ⟨fun hx => (hN.le ⟨x.property, hx⟩).1,
      fun hx => (hN.ge ⟨hx, x.property⟩).2⟩
  exact normalizer_component_image _ _ _ (comap_mono hYL) hθI hNI

omit [Finite G] in
/-- Sylow containment is preserved by the actual component map. -/
theorem componentImage_sylow_le {I L M S : Subgroup G} [(L.subgroupOf I).Normal]
    (hSM : S ≤ M) : componentImage I L S ≤ componentImage I L M :=
  map_mono (comap_mono hSM)
end CFSG.Quasithin.Chapter15.Section03.RankTwo

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Maximality in 15.3.41(2), by applying 15.3.25 to the actual preimage
of each competing subgroup. Characteristic two lifts through the two-kernel. -/
theorem componentImage_maximal
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (hLI : L ≤ I) (hIeq : I = L ⊔ S) (hZ : IsPGroup 2 (center L))
    (hI : I ∈ outsideFamily Y S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYM : Y ≤ M) (hSM : S ≤ M)
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A)
    (J : Subgroup (ComponentQuotient I L)) (hMJ : componentImage I L M ≤ J)
    (hJ : generalizedFitting J = pCore 2 J) : J = componentImage I L M := by
  let q := centralizerQuotientMap (L.subgroupOf I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hk : IsPGroup 2 q.ker := component_kernel_isTwoGroup hLI hIeq hS hZ
  have hr : q.range = ⊤ := q.range_eq_top_of_surjective hq
  let : q.range.Normal := hr ▸ inferInstance
  let X : Subgroup I := J.comap q
  let A : Subgroup G := X.map I.subtype
  have hMX : M.subgroupOf I ≤ X := by
    intro x hx
    exact hMJ (mem_map_of_mem q hx)
  have hAI : A ≤ I := map_subtype_le _
  have hYA : Y ⊔ S ≤ A := by
    intro x hx
    have hxI : x ∈ I := hI.1.2 hx
    have hxM : x ∈ M := (sup_le hYM hSM) hx
    exact ⟨⟨x, hxI⟩, hMX hxM, rfl⟩
  have hcore : I.pCoreIn 2 ≤ A.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    · exact (hP ▸ pCoreIn_le_sylow I P).trans (le_sup_right.trans hYA)
    · exact hAI.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hAcore : A.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hI.1.1 (le_bot_iff.mp (hcore.trans he.le))
  have hCJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    rw [← hJ]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hCX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    q.centralizer_pCore_comap_of_normal_range hk J hCJ
  have hCA : centralizer (pCore 2 A : Set A) ≤ pCore 2 A :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2
      (Subgroup.equivMapOfInjective X I.subtype I.subtype_injective)).mp hCX
  have hFA : generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hCA
  have hAM : A ≤ M := by
    by_contra hn
    exact h25 A ⟨⟨hAcore, hYA⟩, hn⟩ hFA
  apply le_antisymm _ hMJ
  have hXM : X ≤ M.subgroupOf I := fun x hx => hAM ⟨x, hx, rfl⟩
  calc
    J = X.map q := (map_comap_eq_self_of_surjective hq J).symm
    _ ≤ componentImage I L M := map_mono hXM
end CFSG.Quasithin.Chapter15.Section03.RankTwo

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An actual isomorphism from the original component's central quotient,
retaining its identity across the relative-subgroup construction. -/
noncomputable def componentImageCenterEquiv (I L : Subgroup G)
    [(L.subgroupOf I).Normal] (hLI : L ≤ I) :
    L ⧸ center L ≃* componentImage I L L := by
  let e := subgroupOfEquivOfLe hLI
  have hc : (center L).comap e.toMonoidHom = center (L.subgroupOf I) := by
    ext x
    constructor
    · intro hx
      have h := (centerCongr e.symm ⟨e x, hx⟩).property
      change e.symm (e x) ∈ center (L.subgroupOf I) at h
      simpa only [MulEquiv.symm_apply_apply] using h
    · intro hx
      exact (centerCongr e ⟨x, hx⟩).property
  exact (QuotientGroup.equivOfSurjectiveComap e.toMonoidHom e.surjective _ _ hc).symm.trans
    (centralizerQuotientComponentEquiv (L.subgroupOf I))

/-- Carry any actual central-quotient model supplied by 15.3.33 to L⁺.
This transports model equivalences; it makes no new model-selection claim. -/
noncomputable def componentImageModelEquiv (I L : Subgroup G)
    [(L.subgroupOf I).Normal] (hLI : L ≤ I)
    {A : Type*} [Group A] (e : L ⧸ center L ≃* A) : componentImage I L L ≃* A :=
  (componentImageCenterEquiv I L hLI).symm.trans e
end CFSG.Quasithin.Chapter15.Section03.RankTwo

end
