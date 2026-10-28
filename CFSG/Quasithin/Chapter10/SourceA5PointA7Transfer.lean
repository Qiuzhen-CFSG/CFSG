module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.AlternatingSevenQuotient
public import CFSG.Quasithin.Chapter10.SourceA5PointActionModels

/-!
# The quasisimple head of the original A₇ point actor

The literal reduced-module action kills the original component two-core.
The marked A₇ actor and the SQTK point centralizer therefore give a
quasisimple original head. This retains a possible central cubic kernel;
no equality of the action centralizer and the two-core is asserted.
Source: Aschbacher--Smith10.2.9, printed pp.751--752.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual reduced A₇ action supplies the quasisimple head needed by C.1.24. -/
theorem source_a5_point_a7_head_quasisimple
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {v : G} (hv : orderOf v = 2)
    (I : Subgroup G) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))))
    (e : let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf H
      letI := hr.normal
      ((I.subgroupOf H).map (actionMk U)) ≃* alternatingGroup (Fin 7)) :
    IsQuasisimple (I ⧸ pCore 2 I) := by
  let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf H
  let := hr.normal
  let K := I.subgroupOf H
  let q := actionMk U
  have hHX : H ≤ centralizer ({v} : Set G) := sup_le hIX inf_le_right
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left hHX
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.subgroupOf (show K ≤ K from le_rfl)
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHX)).mp
      ((D.simpleQTKE.involution_centralizer_sqtk hv).subgroup _)
  let f := e.toMonoidHom.comp (q.subgroupMap K)
  have hf : Function.Surjective f := e.surjective.comp (q.subgroupMap_surjective K)
  have hk : pCore 2 K ≤ f.ker := by
    intro k hk
    have hcore : (k : H) ∈ pCore 2 H :=
      pCoreIn_le_of_subnormal 2 hK.subnormal (mem_map_of_mem K.subtype hk)
    have hc : (k : H) ∈ centralizer (U : Set H) :=
      le_centralizer_iff.mp hr.le_centralizer_pCore hcore
    have hz : q.subgroupMap K k = 1 := Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hc)
    change e (q.subgroupMap K k) = 1
    rw [hz, map_one]
  let := ChapterA.Section03.NoncentralFitting.quasisimple_twoCore_of_alternating_seven_quotient
    (hH.subgroup K) htop f hf hk
  let d : K ≃* I := subgroupOfEquivOfLe le_sup_left
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ d (pCore_map_iso 2 d))
end CFSG.Quasithin.Chapter10
