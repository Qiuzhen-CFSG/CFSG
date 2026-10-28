module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameElementaryCore
public import Theory.GroupTheory.PGroup.PerfectActionDetection
public import Theory.Representation.BinaryConjugationSection.ElementaryQuotient

/-!
# A large critical quotient in the original linear-four component core

The component centralizes every invariant abelian subgroup of its original
two-core: apply the checked elementary result to its first omega and use
the p-group restriction kernel. The cubic parity argument also rules out
nontrivial component action on any elementary core section of binary
degree at most twelve, allowing nonabelian numerators.

Choose a characteristic critical subgroup of the actual component core.
Its center is fixed by the component. Characteristic two and the critical
restriction kernel ensure that the component acts nontrivially on its
central quotient. The small-section result and cubic parity force this
quotient to have at least fourteen binary dimensions. The source application
selects the cubic internally and retains the original core and conjugation
actions throughout.

This isolates a remaining large nonabelian section; it does not exclude
its representation or prove the terminal contradiction. That exclusion,
strict secondary-core enlargement and the original MS construction remain
with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith, conclusion of original 4.3.2, pp.618--619;
Thompson's critical-subgroup theorem for the characteristic section.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
namespace RootCoordinates
variable (m : RootCoordinates d)
  (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
include m D hX hXK hXr hfix hcomm e

theorem abelian_core_centralizes_component
    (A : Subgroup G) [IsMulCommutative A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hN : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G)) :
    s.component.map (rootNormalizer c).subtype ≤ centralizer (A : Set G) := by
  let M := s.component.map (rootNormalizer c).subtype
  let O := (omega A (p := 2) 1).map A.subtype
  let : (omega A (p := 2) 1).Characteristic := omega_characteristic A 1
  let : IsElementaryAbelian 2 (omega A (p := 2) 1) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.map_subtype
  have hO := m.elementary_core_centralizes_component s D X hX hXK hXr hfix hcomm e O
    ((map_subtype_le _).trans hA)
    (hN.trans (normalizer_le_normalizer_characteristic_image A _))
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let : Group.IsPerfect M := Group.IsPerfect.ofSurjective
    (f := (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).toMonoidHom)
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).surjective
  have hp : IsPGroup 2 A :=
    ((pCore_isPGroup (p := 2) (G := s.component)).map s.component.subtype |>.map
      (rootNormalizer c).subtype).to_le hA
  exact OmegaAction.perfect_centralizes_of_centralizes_omega_one M A hp
    (le_sup_left.trans hN) hO
end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
namespace RootCoordinates
variable (m : RootCoordinates d)
  (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
omit [Finite G] in
include hXr in
private theorem component_extension_normal :
    ((s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X)).Normal := by
  let := s.normal
  apply normal_subgroupOf_of_le_normalizer
  have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
  have hn : rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact (sup_le (map_subtype_le _) hXr).trans hn

include m D hX hXK hXr hfix hcomm e

/-- A source core section of binary degree at most twelve has trivial component action when irreducible. -/
theorem small_core_section_component_kernel
    (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ)
    [ρ.IsIrreducible] (hbound : Nat.card W ≤ 2^12) :
    (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let : H.Normal := component_extension_normal s X hXr
  let : Finite W := Finite.of_surjective (fun x => (a.coordinates x).toAdd) a.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  let f : H ≃* s.component := (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).symm
  let eq : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  by_contra hnt
  have hd := hbound
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hd
  have hdim : Module.finrank (ZMod 2) W ≤ 12 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hd
  have h9 := Representation.PSL3Four.normal_core_simple_degree H eq ρ hdim hnt
  apply m.component_section_not_odd_degree s D X hX hXK hfix hcomm A B hA
    a.kernel_le a.normalized a.kernel_normalized (show Odd 9 by decide)
  rw [a.relIndex_eq_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h9]


/-- The component fixes every source section of binary degree at most twelve, including sections of nonabelian subgroups. -/
theorem small_core_action_component_kernel
    (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ) (hbound : Nat.card W ≤ 2^12) :
    (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let : Finite W := Finite.of_surjective (fun x => (a.coordinates x).toAdd) a.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  by_contra hn
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let f : H ≃* s.component := (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).symm
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := f.symm.toMonoidHom) f.symm.surjective
  obtain ⟨P,N,hi,hnt⟩ :=
    Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect (ρ := ρ) H hn
  let aa := a.invariantSection P
  let bb := aa.quotientSection N
  let : N.quotientRepresentation.IsIrreducible := hi
  exact hnt (m.small_core_section_component_kernel s D X hX hXK hXr hfix hcomm e
    _ _ ((a.invariantPreimage_le P).trans hA) N.quotientRepresentation bb
      ((Nat.card_le_card_of_surjective N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective).trans
        ((Nat.card_le_card_of_injective (fun x : P.toSubmodule => (x : W))
          Subtype.val_injective).trans hbound)))


include m D hX hXK hXr hfix hcomm e

/-- Every characteristic critical subgroup of the original component core
has a component-fixed center and a moved central quotient of binary degree
at least fourteen. The actions are the original conjugation restrictions. -/
theorem critical_core_structure
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (C : Subgroup (pCore 2 (s.component.map (rootNormalizer c).subtype)))
    (hC : IsCriticalPSubgroup 2 C) :
    let M := s.component.map (rootNormalizer c).subtype
    letI := hC.characteristic
    let f : M →* MulAut (pCore 2 M) := MulAut.conjNormal
    (∀ (g : M) (z : center C), MulAut.characteristic C (f g) z = z) ∧
      (quotientAut (center C)).comp ((MulAut.characteristic C).comp f) ≠ 1 ∧
      2^14 ≤ Nat.card (C ⧸ center C) := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let P := pCore 2 M
  let : C.Characteristic := hC.characteristic
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let eM := s.component.equivMapOfInjective (rootNormalizer c).subtype
    (rootNormalizer c).subtype_injective
  let : Group.IsPerfect M := Group.IsPerfect.ofSurjective (f := eM.toMonoidHom) eM.surjective
  let j : P →* G := M.subtype.comp P.subtype
  have hj : Function.Injective j := M.subtype_injective.comp P.subtype_injective
  let A := C.map j
  let eA : C ≃* A := C.equivMapOfInjective j hj
  have heA (x : C) : (eA x : G) = j x := C.coe_equivMapOfInjective_apply j hj x
  let B := (center A).map A.subtype
  have hcore : M.pCoreIn 2 = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  have hAP : A ≤ M.pCoreIn 2 := by
    rintro _ ⟨x,_,rfl⟩
    exact mem_map_of_mem M.subtype x.property
  have hNM : E ≤ normalizer (M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show M ≤ E from le_sup_left)).mp
      (component_extension_normal s X hXr)
  have hNA : E ≤ normalizer (A : Set G) := by
    have hh := hNM.trans
      (normalizer_le_normalizer_characteristic_image M (C.map P.subtype))
    simpa only [map_map] using hh
  have hNB : E ≤ normalizer (B : Set G) :=
    hNA.trans (normalizer_le_normalizer_characteristic_image A (center A))
  have hAB : B ≤ A := map_subtype_le _
  have hCB : M ≤ centralizer (B : Set G) :=
    m.abelian_core_centralizes_component s D X hX hXK hXr hfix hcomm e B
      (hAB.trans (hAP.trans hcore.le)) hNB
  let f : M →* MulAut P := MulAut.conjNormal
  have hf : f ≠ 1 := by
    intro hf
    have hself := SourceEndgame.unitaryFive_component_core_selfCentralizing s D h
    have hp : P = ⊤ := by
      apply top_unique
      intro g _
      apply hself
      intro q hq
      have he := congrArg (fun b : M →* MulAut P => (b g ⟨q,hq⟩ : M)) hf
      change g * q * g⁻¹ = q at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hPM : IsPGroup 2 M := by
      have hh := pCore_isPGroup (p := 2) (G := M)
      rw [show pCore 2 M = ⊤ from hp] at hh
      exact hh.of_surjective (topEquiv (G := M)).toMonoidHom (topEquiv (G := M)).surjective
    let : Group.IsNilpotent M := hPM.isNilpotent
    have hsol : Group.IsSolvable s.component := Group.isSolvable_of_isSolvable_injective (f := eM.toMonoidHom) eM.injective
    exact s.isComponent.not_isSolvable hsol
  have hZ : ∀ (g : M) (z : center C), MulAut.characteristic C (f g) z = z := by
    intro g z
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hz : eA z ∈ center A := by
      rw [←center_map_equiv eA]
      exact mem_map_of_mem _ z.property
    have hc := hCB g.property _ (mem_map_of_mem A.subtype hz)
    change (eA (z : C) : G) * (g : G) = (g : G) * (eA (z : C) : G) at hc
    rw [heA] at hc
    change (g : G) * (j (z : C)) * (g : G)⁻¹ = j (z : C)
    rw [←hc,mul_inv_cancel_right]
  have hne := hC.central_quotient_action_ne_one
    (pCore_isPGroup (p := 2) (G := M)) f hf hZ
  refine ⟨hZ,hne,?_⟩
  let qE := QuotientGroup.congr _ _ eA (center_map_equiv eA)
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  let : IsElementaryAbelian 2 (A ⧸ center A) := IsElementaryAbelian.of_surjective
    qE.toMonoidHom qE.surjective
  have hB : B.subgroupOf A = center A :=
    comap_map_eq_self_of_injective A.subtype_injective _
  let : (B.subgroupOf A).Normal := hB.symm ▸ inferInstance
  let eB := QuotientGroup.quotientMulEquivOfEq hB
  let : IsElementaryAbelian 2 (A ⧸ B.subgroupOf A) :=
    IsElementaryAbelian.of_surjective eB.symm.toMonoidHom eB.symm.surjective
  obtain ⟨ρ,⟨a⟩⟩ := Representation.BinaryConjugationSection.exists_elementary_quotient_coordinates
    E A B (hAP.trans ((map_subtype_le _).trans le_sup_left)) hNA hAB hNB
  have hind : B.relIndex A = Nat.card (C ⧸ center C) := by
    change (B.subgroupOf A).index = _
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (eB.trans qE.symm).toEquiv
  have h13 : Nat.card (C ⧸ center C) ≠ 2^13 := by
    rw [←hind]
    exact m.component_section_not_odd_degree s D X hX hXK hfix hcomm
      A B (hAP.trans hcore.le) hAB hNA hNB (show Odd 13 by decide)
  by_contra! hb
  have hb12 : Nat.card (C ⧸ center C) ≤ 2^12 := by
    obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 (C ⧸ center C)).exists_card_eq
    have hr14 : r < 14 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (hr ▸ hb)
    have hr13 : r ≠ 13 := fun he => h13 (hr.trans (congrArg (fun n : ℕ => 2^n) he))
    rw [hr]
    exact Nat.pow_le_pow_right (by decide) (by omega : r ≤ 12)
  have hbound : Nat.card (Additive (A ⧸ B.subgroupOf A)) ≤ 2^12 := by
    change Nat.card (A ⧸ B.subgroupOf A) ≤ 2^12
    rw [Nat.card_congr eB.toEquiv,←Nat.card_congr qE.toEquiv]
    exact hb12
  have hk := m.small_core_action_component_kernel s D X hX hXK hXr hfix hcomm e
    A B (hAP.trans hcore.le) ρ a hbound
  apply hne
  apply MonoidHom.ext
  intro g
  apply MulEquiv.ext
  intro x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center C) x
  rw [MonoidHom.comp_apply,quotientAut_apply_mk]
  change QuotientGroup.mk' (center C) (MulAut.characteristic C (f g) x) =
    QuotientGroup.mk' (center C) x
  apply QuotientGroup.eq_iff_div_mem.mpr
  have hh := (a.action_mem_ker_iff (⟨g,mem_sup_left g.property⟩ : E)).mp
    (hk g.property) (eA x) (eA x).property
  have he : eA (MulAut.characteristic C (f g) x / x) ∈ center A := by
    apply (mem_map_iff_mem A.subtype_injective).mp
    change (eA (MulAut.characteristic C (f g) x / x) : G) ∈ B
    change (g : G) * j x * (g : G)⁻¹ / j x ∈ B
    simpa only [div_eq_mul_inv,commutatorElement_def,heA] using hh
  rw [←center_map_equiv eA] at he
  exact (mem_map_iff_mem eA.injective).mp he

end RootCoordinates

/-- Select the actual characteristic critical subgroup of the original core.
Its center is fixed by the component, but its central quotient is moved and
has at least fourteen binary dimensions. MS and secondary construction
remain the enclosing source owner's obligations. -/
theorem MSData.linearFour_critical_core (d : MSData c 2) (m : RootCoordinates d)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    let M := s.component.map (rootNormalizer c).subtype
    ∃ C : Subgroup (pCore 2 M), ∃ hC : IsCriticalPSubgroup 2 C,
      letI := hC.characteristic
      let f : M →* MulAut (pCore 2 M) := MulAut.conjNormal
      (∀ (g : M) (z : center C), MulAut.characteristic C (f g) z = z) ∧
      (quotientAut (center C)).comp ((MulAut.characteristic C).comp f) ≠ 1 ∧
      2^14 ≤ Nat.card (C ⧸ center C) := by
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  obtain ⟨C,hC⟩ := (pCore_isPGroup (p := 2)
    (G := s.component.map (rootNormalizer c).subtype)).exists_criticalPSubgroup
  exact ⟨C,hC,m.critical_core_structure s D X hX hXK hr hfix hcomm e h C hC⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
