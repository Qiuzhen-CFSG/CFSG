module

public import CFSG.Quasithin.Chapter10.SourceA5PointMovedCubics
public import CFSG.Quasithin.Chapter10.SourceA5PointSelectedModels
public import CFSG.Quasithin.Chapter10.SourceA5PointActionSeed
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import CFSG.Quasithin.Chapter10.SourceA5PointMovedCubics.G2
public import CFSG.Quasithin.Chapter10.SourceA5PointActionTorus.Literal
public import CFSG.Quasithin.Chapter4.Section01.Maximality

/-!
# Exclusion of the four scalar point-action models

The original fixed seed is nonfixed by the component and fixed by its full
Sylow two-subgroup. Transporting the smaller local section to the offender
component preserves its alternating-five quotient. Each of the natural SL3,
repeated SL3, symplectic Sp4 and G2 models supplies a cubic that centralizes
that section and moves the seed. The canonical component equivalence returns
it to the original action quotient, where the literal cubic lift contradicts
movement. Both original and offender actions are retained throughout.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter10
open ChapterB.QuasisimpleSource

theorem source_a5_point_sectionCentralizer_map_equiv_le
    {C A : Type*} [Group C] [Group A]
    (E : C ≃* A) (B : Subgroup C) :
    (Chapter4.sectionCentralizer B).map E.toMonoidHom ≤
      Chapter4.sectionCentralizer (B.map E.toMonoidHom) := by
  apply (Chapter4.le_sectionCentralizer_iff _ _).mpr
  have hsc := (Chapter4.le_sectionCentralizer_iff
    (Chapter4.sectionCentralizer B) B).mp le_rfl
  constructor
  · exact ((map_mono hsc.1).trans
      (le_normalizer_map E.toMonoidHom))
  · have h := Subgroup.map_mono (f := E.toMonoidHom) hsc.2
    have hcore : (B.pCoreIn 2).map E.toMonoidHom =
        (B.map E.toMonoidHom).pCoreIn 2 :=
      Subgroup.map_pCoreIn_of_injective (G := C) (A := A) 2 B E.toMonoidHom E.injective
    rw [map_commutator, hcore] at h
    exact h

theorem source_a5_point_mem_sectionCentralizer_map_equiv
    {C A : Type*} [Group C] [Group A]
    (E : C ≃* A) (B : Subgroup C) {x : C}
    (hx : x ∈ Chapter4.sectionCentralizer B) :
    E x ∈ Chapter4.sectionCentralizer (B.map E.toMonoidHom) := by
  apply source_a5_point_sectionCentralizer_map_equiv_le E B
  exact mem_map_of_mem E.toMonoidHom hx


/-- The four natural scalar models appearing in the point-action sieve. -/
inductive SourceA5PointScalarModel
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {C : Subgroup G}
    (s : MovedSection ρ C) : Prop
  | linear (F : BinaryField)
      (e : ActionEquiv (s.central.quotientRepresentation.comp C.subtype)
        (linearNatural F 3))
  | repeated (F : BinaryField)
      (e : ActionEquiv (s.space.toRepresentation.comp C.subtype)
        (ChapterB.QuasisimpleSource.repeated (linearNatural F 3) 2))
  | symplectic (F : BinaryField) (hlarge : 1 < F.degree)
      (e : ActionEquiv (s.central.quotientRepresentation.comp C.subtype)
        (binarySymplectic F))
  | g2 (F : BinaryField) (hlarge : 1 < F.degree)
      (e : ActionEquiv (s.central.quotientRepresentation.comp C.subtype)
        (binaryG2 F))

private theorem scalar_model_moving_cubic
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {C : Subgroup G}
    (s : MovedSection ρ C) (hm : moved ρ C = ⊤)
    (hmodel : SourceA5PointScalarModel s)
    (R : Sylow 2 C) (B : Subgroup C) (hB : B ∈ ChapterA.Section03.localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (z : V) (hz : z ∉ fixedSpace ρ C)
    (hfix : ∀ r ∈ (R : Subgroup C), ρ (r : G) z = z) :
    ∃ x : C, orderOf x = 3 ∧ x ∈ Chapter4.sectionCentralizer B ∧ ρ (x : G) z ≠ z := by
  cases hmodel with
  | linear F e =>
    exact source_a5_point_linear_section_moving_cubic s hm e R B hB hp eB z hz
  | repeated F e =>
    exact source_a5_point_repeated_section_moving_cubic s hm e R B hB hp eB z hz
  | symplectic F hlarge e =>
    exact source_a5_point_symplectic_section_moving_cubic s hm hlarge e R B hB hp eB z hz hfix
  | g2 F hlarge e =>
    exact source_a5_point_g2_section_moving_cubic s hm hlarge e R B hB hp eB z hz hfix

open Theory.GroupTheory Stellmacher
open Chapter3.Section02 ChapterB.InternalThompsonAction
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- All four scalar branches are impossible for the literal point action.
The source local-image bundle supplies the explicit full Sylow and marking. -/
theorem source_a5_point_no_scalar_model
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ P
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
    letI := hr.normal
    letI := hr.elementary
    let K := I.subgroupOf H
    let q := actionMk U
    let A := K.map q
    let N := offenderSubgroup (action U)
    let C := A.subgroupOf N
    let B := ((L.subgroupOf H).map q).subgroupOf A
    ∀ (_hAN : A ≤ N), moved (action U) A = ⊤ → B ≠ ⊤ →
      ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) →
      ∀ R : Sylow 2 K,
      (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K →
      B ∈ ChapterA.Section03.localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) →
      ∀ s : MovedSection ((action U).comp N.subtype) C,
        ¬ SourceA5PointScalarModel s := by
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
  let := hr.normal
  let := hr.elementary
  let K := I.subgroupOf H
  let q := actionMk U
  let A := K.map q
  let N := offenderSubgroup (action U)
  let C := A.subgroupOf N
  let B := ((L.subgroupOf H).map q).subgroupOf A
  dsimp only
  intro hAN hfull hp eB R hR hlocal s hmodel
  let E : C ≃* A := subgroupOfEquivOfLe hAN
  let a : A ≃* C := E.symm
  let R0 : Sylow 2 A := R.mapSurjective (q.subgroupMap_surjective K)
  let R1 := R0.mapSurjective (f := a.toMonoidHom) a.surjective
  let B1 := B.map a.toMonoidHom
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    apply Group.isSolvable_of_top_eq_bot
    ext x
    simp only [mem_top,mem_bot,true_iff]
    exact Subtype.ext (mem_bot.mp x.property)
  have hlocal1 : B1 ∈ ChapterA.Section03.localCComponents R1 :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal a.toMonoidHom
  have hp1 : B1 ≠ ⊤ := by
    intro he
    apply hp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_top_of_surjective a.toMonoidHom a.surjective]
    exact he
  let b : B ≃* B1 := B.equivMapOfInjective a.toMonoidHom a.injective
  let e1 : (B1 ⧸ pCore 2 B1) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB
  have hfullC : moved ((action U).comp N.subtype) C = ⊤ := by
    rw [moved_comp_map, map_subgroupOf_eq_of_le hAN]
    exact hfull
  obtain ⟨z,hzW,hzP,hzA⟩ := source_a5_point_action_fixed_seed D I hLI hspan hr
  have hzC : z ∉ fixedSpace ((action U).comp N.subtype) C := by
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hAN]
    exact hzA
  have hfix : ∀ r ∈ (R1 : Subgroup C),
      ((action U).comp N.subtype) (r : N) z = z := by
    intro r hrr
    change r ∈ (R0 : Subgroup A).map a.toMonoidHom at hrr
    rcases hrr with ⟨rA, hrA, rfl⟩
    change rA ∈ (R : Subgroup K).map (q.subgroupMap K) at hrA
    rcases hrA with ⟨i, hi, rfl⟩
    have hiT : ((i : H) : G) ∈ (T : Subgroup G) := by
      rw [hR] at hi
      exact hi
    have hiP : (i : H) ∈ P.subgroupOf H := ⟨hiT,hIX i.property⟩
    exact hzP ⟨q (i : H),mem_map_of_mem q hiP⟩
  obtain ⟨x,hx3,hxc,hmove⟩ := scalar_model_moving_cubic s hfullC hmodel
    R1 B1 hlocal1 hp1 e1 z hzC hfix
  have hmap : B1.map E.toMonoidHom = B := by
    ext y
    constructor
    · rintro ⟨x,⟨u,hu,rfl⟩,rfl⟩
      change E (E.symm u) ∈ B
      rw [E.apply_symm_apply]
      exact hu
    · intro hy
      exact ⟨a y,⟨y,hy,rfl⟩, E.apply_symm_apply y⟩
  have hxB : E x ∈ Chapter4.sectionCentralizer B := by
    rw [← hmap]
    exact source_a5_point_mem_sectionCentralizer_map_equiv E B1 hxc
  have hm : action U ((E x : A) : ActionQuotient U) z ≠ z := by
    exact hmove
  exact source_a5_point_no_moving_action_cubic D e hn ht htn hcross hsep hNL
    I hLI hIX hI hout hCW hspan hr (E x) ((E.orderOf_eq x).trans hx3) hxB
    z.toMul hzW hm

end CFSG.Quasithin.Chapter10
