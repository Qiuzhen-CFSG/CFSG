module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitAction
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# The original inputs to the paired Baumann argument

Once the cubic residual lies in the moving component orbit, the plus actor
is the original component-Sylow join, so its action kernel is a two-group.
The actual W_K inside that actor is reduced. Its Sylow Thompson subgroup
moves W_K, because its quotient commutator generates the nontrivial component
orbit. These are the source inputs to the paired natural Baumann theorem;
the finite-field model and residual containment have separate producers.

Source: Aschbacher--Smith, proof of 13.6.14, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Residual placement identifies the full action kernel with the already
proved two-group kernel on the component-Sylow join. -/
theorem plusMk_ker_isTwoGroup_of_noninvariant_source
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLv : Lv L v ≤ Kminus K T v) : IsPGroup 2 (plusMk K L T z v hL hz).ker := by
  let H := K ⊔ Tv T v
  let A := plusActor K L T v
  have hKH : K ≤ H := le_sup_left
  have hTH : Tv T v ≤ H := le_sup_right
  have hKmH : Kminus K T v ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have hAH : A ≤ H := sup_le (sup_le hKmH (hLv.trans hKmH)) hTH
  let f : (plusMk K L T z v hL hz).ker →*
      (joinPlusMap K L T z v hL hz).ker :=
    { toFun := fun x => ⟨⟨x.val, hAH x.val.property⟩, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (joinPlusMap_ker_isTwoGroup_source K L T z v hlocal hL hz hK hn).of_injective f
    (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h)))

/-- Full reducedness for the literal internal W_K used by Baumann's theorem. -/
theorem internalWK_reduced_source (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    IsPReduced 2 ((WK K L T z v).subgroupOf (plusActor K L T v)) := by
  obtain ⟨hWA, he, hN, hred⟩ := WK_mem_reducedFamily_source K L T z v hK hL hz hSylow hzOmega hf
  let := he
  exact ⟨hN, IsElementaryAbelian.subgroupOf hWA, hred⟩

omit [Finite G] in
/-- The actual Sylow Thompson subgroup acts nontrivially on internal W_K. -/
theorem internalWK_thompson_moves_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hK : K ∈ Yz L T z v)
    (P : Sylow 2 (plusActor K L T v))
    (hP : (P : Subgroup (plusActor K L T v)).map (plusActor K L T v).subtype = Tv T v) :
    ¬ elementaryAbelianMaxJ (P : Subgroup (plusActor K L T v)) ≤
      centralizer ((WK K L T z v).subgroupOf (plusActor K L T v) : Set (plusActor K L T v)) := by
  let A := plusActor K L T v
  have hWA : WK K L T z v ≤ A := conjugateSpanBy_le
    (zpowers_le.mpr ((show Tv T v ≤ A from le_sup_right) hzT))
    ((show Kminus K T v ⊔ Lv L v ≤ A from le_sup_left).trans A.le_normalizer)
  intro hc
  have hJmap : elementaryAbelianMaxJ (Tv T v) =
      (elementaryAbelianMaxJ (P : Subgroup A)).map A.subtype := by
    rw [← hP, elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective]
  have hJzero : plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) = ⊥ := by
    rw [hJmap]
    change (((elementaryAbelianMaxJ (P : Subgroup A)).map A.subtype).comap A.subtype).map
      (plusMk K L T z v hL hz) = ⊥
    rw [comap_map_eq_self_of_injective A.subtype_injective]
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    rw [plusMk_ker]
    intro w hw
    exact congrArg Subtype.val (hc hx ⟨w,hWA hw⟩ hw)
  have hzero := orbit_plus_commutator_source K L T z v hL hz hK
  rw [hJzero, commutator_bot_right] at hzero
  apply plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK
  exact bot_unique ((map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans hzero.symm.le)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
