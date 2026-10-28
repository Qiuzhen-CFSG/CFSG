module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryComponentModels

/-!
# The projected moving sixteen inside the component Sylow subgroup

On the same original paired plane, the faithful inner image of [W,L₀]
is an elementary subgroup of order sixteen inside a Sylow subgroup of
K/Z(K). Its centralizer in that Sylow subgroup has index at most two.
The proof restricts the original ambient Sylow along the component's
subnormal chain and transports the whole-orbit action kernel through
the actual inner conjugation map.

This is the precise Sylow input to the root-group argument in 7.7.6.
The nonbinary model, both seed axes, local base and relative two-core
remain attached to the same plane. Root-group and Cartan exclusion
remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed p.706, refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryInnerAction DoubledBinarySylowFixed DoubledBinaryComponentModels
open DoubledBinaryComponentSylow
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The faithful inner moving sixteen lies in the canonical central-quotient
image of an original component Sylow contained in C_T(U), with centralizer
index at most two. Its nonbinary Lie model and marked plane are retained. -/
theorem sourceOrbit_binary_pairedPlane_componentSylow_with_marking
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
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (Q : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (Q : Subgroup _)).index ≤ 2) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                (∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) ∧
                NonbinaryLieModel (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_componentModels_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := localResidual L U
  let A := ⁅D.sourceOrbit,R⁆
  let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hRW : R ≤ normalizer (D.sourceOrbit : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes)
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp hRW
  have hAS : A ≤ S₀ := le_inf (hAW.trans D.sourceOrbit_weakClosure_setup.le_sylow)
    (hAW.trans (D.sourceOrbit.le_centralizer.trans
      (centralizer_le (ambientPlane_le_orbit D.sourceOrbit E v f))))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  have hindex : ((centralizer (A : Set G)).subgroupOf S₀).index ≤ 2 := by
    apply le_trans _ hi
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
      (index_dvd_of_le (comap_mono (centralizer_le hAW)))
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,?_⟩
  intro H hBH hHC K hK
  obtain ⟨hfix,hAN,hker,horder,hinner,⟨j,hj,hjact⟩,hr,hcenter,hm⟩ := hcomp H hBH hHC K hK
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
  have hjcard : Nat.card j.range = 16 :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hcard
  have hje : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective
    j.rangeRestrict j.rangeRestrict_surjective
  exact ⟨hfix,hAN,hker,horder,hinner,⟨j,hj,hjact,hjcard,hje,
    ⟨P,hPS,projected_sylow K A S₀ hAS (T.isPGroup'.to_le inf_le_left)
      hAN P hPS hindex j hjact⟩⟩,
    hr,hcenter,hm⟩

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_componentSylow
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
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (Q : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (Q : Subgroup _)).index ≤ 2) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                (∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) ∧
                NonbinaryLieModel (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_componentSylow_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
