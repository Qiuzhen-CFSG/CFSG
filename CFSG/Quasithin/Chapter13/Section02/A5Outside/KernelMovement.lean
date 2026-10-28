module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.CoreKernel
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import Theory.GroupTheory.SolvableThreePartCore
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The nontrivial outside kernel residual moves the A₅ component quotient

A nontrivial normal solvable subgroup of a characteristic-two local group
has nontrivial two-core. If L normalized it, that two-core would be normalized
by LT and H; uniqueness over LT would force H≤N(L), contrary to its source
choice. A commutator bound modulo O₂(L) would normalize a two-perfect X:
X is the two-residual of XO₂(L), since O₂(L)≤T normalizes X.

This proves the noncentral branch in the original 13.2.9 argument before the
subsequent R=O₂(XT) construction.
Source: Aschbacher–Smith 13.2.9, printed pp. 880–881.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- Outside H cannot have a nontrivial normal subgroup normalized by the original L. -/
theorem outside_normal_not_normalized_by_component
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H X : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hXH : X ≤ H) (hnX : H ≤ normalizer (X : Set G))
    (hne : X ≠ ⊥) : ¬ L ≤ normalizer (X : Set G) := by
  intro hLX
  let := hs
  let N := X.subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer hnX
  have hNne : N ≠ ⊥ := by
    intro he
    apply hne
    rw [← map_subgroupOf_eq_of_le hXH]
    exact (congrArg (map H.subtype) he).trans (Subgroup.map_bot _)
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (d.hypothesis.qtke.evenCharacteristic T) hH.1.1)
  have hcore := pCore_ne_bot_of_solvable_normal_of_characteristic 2 hchar N hNne
  have hXcore : pCore 2 X ≠ ⊥ := by
    intro he
    let e : N ≃* X := subgroupOfEquivOfLe hXH
    have hh := pCore_map_iso 2 e
    rw [he] at hh
    exact hcore ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  let Q := X.pCoreIn 2
  have hQne : Q ≠ ⊥ := fun he => hXcore
    ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp he)
  have hNQ : normalizer (X : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hbound : normalizer (Q : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      (pCore_isPGroup.map X.subtype) hQne
      (sup_le (hLX.trans hNQ) ((hH.1.1.2.trans hnX).trans hNQ))
  exact hH.1.2 ((hnX.trans hNQ).trans hbound)

/-- A source normal two-perfect subgroup cannot centralize L/O₂(L). -/
theorem outside_twoPerfect_commutator_not_le_component_core
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H X : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hXH : X ≤ H) (hnX : H ≤ normalizer (X : Set G))
    (hne : X ≠ ⊥) (hpX : IsPPerfect 2 X) : ¬ ⁅L,X⁆ ≤ L.pCoreIn 2 := by
  intro hcomm
  let Q := L.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer d.normalizes_L)).trans
      ((d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left)
  have hLQ : L ≤ normalizer (Q : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hn : L ≤ normalizer ((X ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    have hX : X.map (MulAut.conj l).toMonoidHom ≤ X ⊔ Q := by
      rintro _ ⟨x,hx,rfl⟩
      have hc : ⁅l,x⁆ ∈ Q := hcomm (commutator_mem_commutator hl hx)
      have hh := (X ⊔ Q).mul_mem (mem_sup_right hc) (mem_sup_left hx)
      change l*x*l⁻¹ ∈ X ⊔ Q
      simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
    have hQ : Q.map (MulAut.conj l).toMonoidHom ≤ Q := by
      rintro _ ⟨q,hq,rfl⟩
      exact le_normalizer_iff.mp hLQ l hl q hq
    have hmap : (X ⊔ Q).map (MulAut.conj l).toMonoidHom ≤ X ⊔ Q := by
      rw [Subgroup.map_sup]
      exact sup_le hX (hQ.trans le_sup_right)
    exact hmap (mem_map_of_mem _ hx)
  have hLX : L ≤ normalizer (X : Set G) := by
    rw [← embedded_pResidual_join_pGroup X Q hpX (pCore_isPGroup.map L.subtype)
      (hQT.trans (hH.1.1.2.trans hnX))]
    exact hn.trans (normalizer_le_normalizer_characteristic_image (X ⊔ Q)
      (pResidual 2 (X ⊔ Q : Subgroup G)))
  exact outside_normal_not_normalized_by_component d hH hs hXH hnX hne hLX

/-- Failure of the desired two-core equality constructs the literal noncentral residual. -/
theorem source_kernel_residual_moves_component
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    X ≤ H ∧ X ≤ normalizer (L : Set G) ∧ H ≤ normalizer (X : Set G) ∧
      X ≠ ⊥ ∧ IsPPerfect 2 X ∧ ¬ ⁅L,X⁆ ≤ L.pCoreIn 2 := by
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let C := centralizer (U : Set H)
  let N := (pResidual 2 C).map C.subtype
  let X := N.map H.subtype
  have hres : pResidual 2 C ≠ ⊥ := by
    intro he
    have hc : IsPGroup 2 C := (isPGroup_quotient_pResidual (G := C) 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot)
    have hle : C ≤ pCore 2 H := le_sSup ⟨inferInstance,hc⟩
    exact hne (le_antisymm hle (le_centralizer_iff.mp hU.le_centralizer_pCore))
  have hXne : X ≠ ⊥ := by
    intro he
    have hn : N = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
    exact hres ((map_eq_bot_iff_of_injective _ C.subtype_injective).mp hn)
  have hXH : X ≤ H := map_subtype_le _
  have hXM : X ≤ normalizer (L : Set G) :=
    (map_mono (map_subtype_le (pResidual 2 C))).trans
      (source_omega_centralizer_le_local d hH hB hZ hs)
  have hnN : N.Normal := inferInstance
  have hHN : H ≤ normalizer (X : Set G) := by
    have h := N.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using h
  have hpN : IsPPerfect 2 N := (isPPerfect_pResidual (G := C) 2).of_surjective
    (C.subtype.subgroupMap (pResidual 2 C)) (C.subtype.subgroupMap_surjective _)
  have hpX : IsPPerfect 2 X := hpN.of_surjective
    (H.subtype.subgroupMap N) (H.subtype.subgroupMap_surjective _)
  exact ⟨hXH,hXM,hHN,hXne,hpX,
    outside_twoPerfect_commutator_not_le_component_core d hH hs hXH hHN hXne hpX⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
