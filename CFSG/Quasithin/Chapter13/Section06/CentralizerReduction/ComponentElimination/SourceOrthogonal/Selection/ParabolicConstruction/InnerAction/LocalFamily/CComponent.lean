module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Lift
public import Theory.GroupTheory.CComponent.SeedAction
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Local component structure of the lifted parabolic residual

The original plus kernel is solvable: its intersection with the local
C-component is proper, and the remaining quotient is a two-group. Lift the
geometric residual's C-component structure through this solvable kernel.
Restricting to the residual joined with Tᵥ gives the required relative
C-component. The original local two-core survives in this Sylow overgroup.

Source: Aschbacher–Smith, proof of 13.6.23, printed p.933/PDF p.950,
using A.3.3 and Definition 1.2.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- Only solvability, not the two-group property, is asserted for the full kernel. -/
theorem plusMk_ker_solvable
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G)) :
    Group.IsSolvable (plusMk K L T z v hL hz).ker := by
  have hr : solvableResidual (plusActor K L T v) = K.subgroupOf (plusActor K L T v) := by
    rw [plusActor_eq_sup K L T v hLK hK]
    let A := K ⊔ Tv T v
    let N := K.subgroupOf A
    let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hK)
    let : Group.IsPerfect N := hY.1.2.1.perfect
    exact (residuals_of_perfect_normal_sup_twoGroup N ((Tv T v).subgroupOf A)
      (Chapter1.isSylowIn_iff.mp hY.1.2.2.1).1.comap_subtype
      (codisjoint_subgroupOf_sup K (Tv T v)).eq_top).2
  have hc : (solvableResidual (plusActor K L T v)).IsCComponent := by
    rw [hr, plusActor_eq_sup K L T v hLK hK]
    exact hY.1.2.1
  apply isSolvable_of_normal_not_containing_ccomponent_residual _ hc
  rw [hr]
  intro hk
  exact plusImage_ne_bot_of_mem_Yz K L T z v hL hz hY
    ((Subgroup.map_eq_bot_iff _).mpr hk)

private theorem geometricResidual_isCComponent
    {A : Type*} [Group A] [Finite A] (P : Subgroup A)
    (eP : ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) :
    (solvableResidual P).IsCComponent := by
  let R := (solvableResidual P).map P.subtype
  let : IsQuasisimple SL(3, ZMod 2) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv eP.symm
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  have hp : IsPPerfect 2 R := by
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) pCore_isPGroup hp
  have he := ht.map_equiv
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).symm
  rw [map_top_of_surjective _ (MulEquiv.surjective _)] at he
  simpa only [← MonoidHom.range_eq_map, range_subtype] using
    he.map_subtype (inferInstance : (solvableResidual P).Normal).isSubnormal

/-- The residual is a C-component of the full lifted parabolic. -/
theorem liftedParabolic_residual_isCComponent
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (P : Subgroup (Gplus K L T z v hL hz))
    (eP : ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) :
    (solvableResidual (liftedParabolic K L T z v hL hz P)).IsCComponent := by
  let A := plusActor K L T v
  let f := plusMk K L T z v hL hz
  let E := P.comap f
  let e : E ≃* liftedParabolic K L T z v hL hz P :=
    E.equivMapOfInjective A.subtype A.subtype_injective
  let g := f.subgroupComap P
  let : Group.IsSolvable f.ker := plusMk_ker_solvable K L T z v hL hz hY hLK hK
  let j : g.ker →* f.ker :=
    (E.subtype.comp g.ker.subtype).codRestrict f.ker (by
      intro x
      exact congrArg Subtype.val x.property)
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : f.ker => (x : A)) he))
  let : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective hj
  have hc := residual_isCComponent_of_surjective g
    (f.subgroupComap_surjective_of_surjective P (plusMk_surjective K L T z v hL hz))
    (geometricResidual_isCComponent P eP)
  have hm := hc.map_equiv e
  rwa [map_solvableResidual_eq e.toMonoidHom e.surjective] at hm

/-- The literal residual belongs to the local family relative to D Tᵥ. -/
theorem liftedResidual_mem_LIn
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hinner : plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (P : Subgroup (Gplus K L T z v hL hz))
    (hP : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P)
    (eP : ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) :
    liftedResidual K L T z v hL hz P ∈ Chapter1.LIn (Gv v) (Tv T v) := by
  let D := liftedResidual K L T z v hL hz P
  let H := liftedParabolic K L T z v hL hz P
  have hDK : D ≤ K := liftedResidual_le_component K L T z v hL hz P hY.1 hLK hK
  have hDH : D ≤ H := map_subtype_le _
  have hTP : plusImage K L T z v hL hz (Tv T v) ≤ P := by
    rw [plusTv_eq_intersection K L T z v hL hz hY.1 hinner]
    exact (map_mono (comap_mono (show Tv T v ⊓ K ≤ sourceParabolic K L T v from le_sup_right))).trans hP
  have hTH : Tv T v ≤ H := le_liftedParabolic K L T z v hL hz P _ le_sup_right hTP
  have hC : (D.subgroupOf H).IsCComponent := by
    change (((solvableResidual H).map H.subtype).comap H.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact liftedParabolic_residual_isCComponent K L T z v hL hz hY hLK hK P eP
  have hcore : (K ⊔ Tv T v).pCoreIn 2 ≤ (D ⊔ Tv T v).pCoreIn 2 := by
    obtain ⟨S, hS⟩ := hY.1.2.2.1
    have hcT : (K ⊔ Tv T v).pCoreIn 2 ≤ Tv T v :=
      (pCoreIn_le_sylow _ S).trans_eq hS
    exact (le_inf (hcT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (sup_le_sup hDK le_rfl))
  exact ⟨hDK.trans hY.1.1,
    hC.subgroupOf_of_le le_sup_left (sup_le hDH hTH),
    liftedResidual_sylow K L T z v hL hz P hY.1 hLK hK,
    fun he => hY.1.2.2.2 (bot_unique (hcore.trans he.le))⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
