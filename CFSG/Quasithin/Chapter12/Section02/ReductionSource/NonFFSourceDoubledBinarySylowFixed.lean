module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylowFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryInnerAction

/-!
# The inner component action and its Sylow fixed subgroup on one marked plane

The richer intersection theorem retains the original S₃ action along with
its Sylow-placed paired plane. Thus the same moving subgroup A=[W,L₀]
acts faithfully by inner automorphisms on every component and has at least
four elements centralized by the original T₀=C_T(U). Its image in K/Z(K)
is the literal inner action and has rank four.

Restriction along the component's subnormal chain identifies its actual
Sylow subgroup. The fixed actors project into the center of a Sylow subgroup
of K/Z(K), forcing that center to be noncyclic. The original seed axes,
conjugator, local base and relative two-core remain part of the result.
The subsequent root-group and Cartan exclusion are still needed for 7.7.6
and remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed pp.705–706, refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryInnerAction DoubledBinarySylowFixed
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- On the original doubled orbit, the order-sixteen residual moving subgroup
acts faithfully by inner automorphisms on every ordinary component of a
paired-plane overgroup. Its actual projective embedding gives two-rank at
least four, and its common fixed subgroup forces a noncyclic component
Sylow center in K/Z(K). The original conjugator and both seed axes are retained. -/
theorem sourceOrbit_binary_pairedPlane_sylowFixed_with_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          DoubledBinaryOmega.HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U A ∧ Nat.card A = 16 ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃*
            Equiv.Perm (Fin 3)) ∧
          S₀ ≤ normalizer (A : Set G) ∧
          ((centralizer (D.sourceOrbit : Set G)).subgroupOf S₀).index ≤ 2 ∧
          4 ≤ Nat.card ((centralizer (S₀ : Set G)).subgroupOf A) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K A) = 16 ∧
                (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                ∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,_,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_intersections_with_action_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := localResidual L U
  let A := ⁅D.sourceOrbit,R⁆
  let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hWQ := (D.sourceOrbit_core_normalizer h).1
  have hQB : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B := hcore ▸ pCoreIn_le 2 B
  have hRW : R ≤ normalizer (D.sourceOrbit : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes)
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp hRW
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  have hn : S₀ ≤ normalizer (A : Set G) := localSylow_normalizes_movement
    D.sourceOrbit L (T : Subgroup G) U D.sylow_normalizes_component
    D.sourceOrbit_weakClosure_setup.normalizes
  have hi := centralizer_index_le_two D.sourceOrbit U S₀
    (inf_le_left.trans D.sourceOrbit_weakClosure_setup.normalizes) inf_le_right
    (T.isPGroup'.to_le inf_le_left) hquot
  have hfixed := four_le_fixed_card D.sourceOrbit A S₀ hAW hn hcard hi
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,?_⟩
  intro H hBH hHC K hK
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le
    (ambientPlane_le_orbit D.sourceOrbit E v f)
  have hU : U ≠ ⊥ := by
    intro he
    have hh := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hh
    rw [he,Subgroup.card_bot] at hh
    omega
  have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
    ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
  obtain ⟨hfix,hAN,hker,horder⟩ := hcomp H hBH hHC K hK
  obtain ⟨hAN',hi⟩ := component_movement_inner H D.sourceOrbit R K hSQ hK
    (hWQ.trans (hQB.trans hBH)) (le_sup_left.trans hBH)
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G))) hRW
  obtain ⟨j,hj,hjact⟩ := faithful_inner_centralQuotient K A hAN' hker hi
  obtain ⟨SC,hSC⟩ := hS
  have hS₀H : S₀ ≤ H := (show S₀ ≤ B from le_sup_right).trans hBH
  obtain ⟨PH,hPH⟩ := DoubledBinarySylow.sylow_between hHC SC (hSC.trans_le hS₀H)
  obtain ⟨PK,hPK⟩ := PH.exists_subgroupOf_eq_of_subnormal (K.subgroupOf H) hK.2.1
  let e := subgroupOfEquivOfLe hK.1
  let P := PK.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPS : (P : Subgroup K).map K.subtype ≤ S₀ := by
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hk
    have hxP : (x.val : H) ∈ (PH : Subgroup H) := by
      rw [hPK] at hx
      exact hx
    have hh := mem_map_of_mem H.subtype hxP
    rw [hPH,hSC] at hh
    exact hh
  exact ⟨hfix,hAN',hker,horder,hi,⟨j,hj,hjact⟩,
    four_le_rank_centralQuotient K A hcard j hj,
    centralQuotient_sylow_center_not_cyclic K A S₀ hAN' P hPS hfixed j hj hjact⟩

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_sylowFixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U A ∧ Nat.card A = 16 ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃*
            Equiv.Perm (Fin 3)) ∧
          S₀ ≤ normalizer (A : Set G) ∧
          ((centralizer (D.sourceOrbit : Set G)).subgroupOf S₀).index ≤ 2 ∧
          4 ≤ Nat.card ((centralizer (S₀ : Set G)).subgroupOf A) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K A) = 16 ∧
                (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                ∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_sylowFixed_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
