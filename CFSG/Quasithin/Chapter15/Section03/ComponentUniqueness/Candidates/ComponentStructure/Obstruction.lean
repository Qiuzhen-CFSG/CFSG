module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Core
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Solvability

/-!
# Locating the remaining nonordinary C-components

An ordinary component commutes with any distinct C-component: containment
would identify them by minimality. Consequently, the normal closure of a
nonordinary C-component has no ordinary components. If the ambient odd core
is trivial, that normal closure has characteristic two.

For I in the outside family, 15.3.33(1) therefore puts every nonordinary
C-component inside M. Conversely, an ordinary component cannot lie in M,
since M ∩ I has characteristic two. Thus the missing comparison of component
conventions is exactly the exclusion of C-components of I contained in M.
The normal closure here is taken inside I, not in the ambient simple group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.1--3,
printed pp.41--43, and the local conclusions used in 15.3.33, p.1134.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem component_commutes_cComponent {K L : Subgroup G}
    (hK : K.IsCComponent) (hn : ¬ IsComponent G K) (hL : IsComponent G L) :
    ⁅L, K⁆ = ⊥ := by
  rcases hL.subnormal_dichotomy K hK.subnormal with h | h
  · have he := (component_isCComponent hL).eq_of_le hK h
    exact (hn (he ▸ hL)).elim
  · exact h

omit [Finite G] in
private theorem no_components_normalClosure {K : Subgroup G}
    (hK : K.IsCComponent) (hn : ¬ IsComponent G K) :
    ∀ L : Subgroup (normalClosure (K : Set G)),
      ¬ IsComponent (normalClosure (K : Set G)) L := by
  intro L hL
  let N := normalClosure (K : Set G)
  let D := L.map N.subtype
  let := hL.2
  have hD : IsComponent G D :=
    ⟨hL.1.trans' (inferInstance : N.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (L.equivMapOfInjective N.subtype N.subtype_injective)⟩
  have hND : N ≤ centralizer (D : Set G) := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨k, hk, hx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    have hKg : ¬ IsComponent G (K.map (MulAut.conj g).toMonoidHom) := by
      rwa [isComponent_map_equiv_iff]
    have hc := component_commutes_cComponent (hK.map_equiv (MulAut.conj g)) hKg hD
    rw [commutator_comm] at hc
    exact (commutator_eq_bot_iff_le_centralizer.mp hc) (mem_map.mpr ⟨k, hk, rfl⟩)
  have hcomm : ⁅D, D⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr ((map_subtype_le L).trans hND)
  let := hD.2
  rw [commutator_eq_self] at hcomm
  exact (component_isCComponent hD).ne_bot hcomm

private theorem normalClosure_oddCore_eq_bot (K : Subgroup G)
    (hodd : pPrimeCore 2 G = ⊥) :
    pPrimeCore 2 (normalClosure (K : Set G)) = ⊥ := by
  let N := normalClosure (K : Set G)
  apply ((pPrimeCore 2 N).map_eq_bot_iff_of_injective N.subtype_injective).mp
  exact le_bot_iff.mp ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N).trans hodd.le)

/-- The entire intrinsic normal closure of a nonordinary C-component has
generalized Fitting subgroup equal to its two-core. -/
theorem cComponent_normalClosure_characteristicTwo {K : Subgroup G}
    (hK : K.IsCComponent) (hn : ¬ IsComponent G K) (hodd : pPrimeCore 2 G = ⊥) :
    generalizedFitting (normalClosure (K : Set G)) =
      pCore 2 (normalClosure (K : Set G)) := by
  let N := normalClosure (K : Set G)
  have he : componentLayer N = ⊥ := by
    apply sSup_eq_bot.mpr
    intro L hL
    exact (no_components_normalClosure hK hn L hL).elim
  change generalizedFitting N = pCore 2 N
  rw [generalizedFitting, he, sup_bot_eq,
    Fitting_eq_pcore N 2 (normalClosure_oddCore_eq_bot K hodd)]

/-- The local extension argument of 15.3.33(1) places every remaining
nonordinary C-component inside M. All solvability inputs are discharged
from the actual three-group quotient of Y₊. -/
theorem nonordinary_cComponent_le_M {Yplus S M I : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    {K : Subgroup I} (hK : K.IsCComponent) (hn : ¬ IsComponent I K) :
    K.map I.subtype ≤ M := by
  let N := normalClosure (K : Set I)
  let D := N.map I.subtype
  let e : N ≃* D := N.equivMapOfInjective I.subtype I.subtype_injective
  have hoD : pPrimeCore 2 D = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e, normalClosure_oddCore_eq_bot K (hodd I hI),
      Subgroup.map_bot]
  have heD : componentLayer D = ⊥ := by
    apply sSup_eq_bot.mpr
    intro L hL
    exact (no_components_normalClosure hK hn _ (hL.map_equiv e.symm)).elim
  have hFD : generalizedFitting D = pCore 2 D := by
    rw [generalizedFitting, heD, sup_bot_eq, Fitting_eq_pcore D 2 hoD]
  have hIN : I ≤ normalizer (D : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using N.le_normalizer_map I.subtype
  have hDM := lemma_15_3_33_1_of_threeGroup_quotient hI hSylow h25 hodd hSM hMI hY
    (map_subtype_le N) (hI.1.2.trans hIN) hFD
  exact (map_mono (f := I.subtype) (show K ≤ N from le_normalClosure)).trans
    (hDM.trans inf_le_left)

/-- Under the genuine local extension hypotheses, the unresolved source
C-components are exactly those contained in M. -/
theorem cComponent_ordinary_iff_outside {Yplus S M I : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    {K : Subgroup I} (hK : K.IsCComponent) :
    IsComponent I K ↔ ¬ K.map I.subtype ≤ M := by
  constructor
  · intro h hKM
    exact component_not_le_characteristicTwo h hFMI (map_le_iff_le_comap.mp hKM)
  · intro h
    by_contra hn
    exact h (nonordinary_cComponent_le_M hI hSylow h25 hodd hSM hMI hY hK hn)

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
