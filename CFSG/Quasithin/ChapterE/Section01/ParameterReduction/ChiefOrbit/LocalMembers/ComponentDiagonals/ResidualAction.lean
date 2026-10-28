module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Orbit
public import Theory.GroupTheory.Commutator.PerfectSolvableKernel

/-!
# Full residual action in the component diagonal branch

The component alternative first gives full action on the layer of P/O∞(P).
Local tau centralizes the actor in this quotient. Thus the commutator
contains every tau conjugate of the chosen component, including when the
actor permutes components. Perfectness lifts this identity through O∞(P).

Ambient tau centralizes A when O₂(G)=1. The same orbit argument therefore
gives P_A=[P_A,A], and the exact embedded residual identity identifies this
with O²(K_A)=[O²(K_A),A]. This discharges the action premise of E.1.10(8);
it does not construct diagonal quotient members or prove their cover.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- In the component branch, the residual maps onto the entire quotient layer. -/
theorem ECaseComponent.residual_image_eq_layer {T A K : Subgroup G}
    (h : ECaseComponent T A K) :
    (pResidual 2 K).map (QuotientGroup.mk' (solvableRadical K)) =
      componentLayer (K ⧸ solvableRadical K) := by
  obtain ⟨_, ⟨hEn, hEq⟩, hres, L, hL, horbit, _⟩ := h
  let := hEn
  let : Group.IsPerfect (componentLayer (K ⧸ solvableRadical K)) := by
    rw [horbit]
    exact hL.orbit_isPerfect _
  apply le_antisymm
  · rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
    exact sInf_le ⟨hEn, hEq⟩
  · rw [hres, map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _)]
    exact le_solvableResidual_of_isPerfect _

/-- Both component-action alternatives generate the residual by commutators. -/
theorem ECaseComponent.residual_eq_commutator {T A K : Subgroup G}
    (h : ECaseComponent T A K) : pResidual 2 K = ⁅pResidual 2 K, A.subgroupOf K⁆ := by
  let q := QuotientGroup.mk' (solvableRadical K)
  let a := (A.subgroupOf K).map q
  let d := (tau (T.subgroupOf K) (A.subgroupOf K)).map q
  let E := componentLayer (K ⧸ solvableRadical K)
  have hr : (pResidual 2 K).map q = E := h.residual_image_eq_layer
  obtain ⟨_, ⟨hEn, _⟩, hres, L, hL, horbit, halt⟩ := h
  let := hEn
  have hcore : pCore 2 K ≤ solvableRadical K :=
    le_solvableRadical _ inferInstance
      (@IsNilpotent.to_isSolvable _ _ (pCore_isPGroup (p := 2) (G := K)).isNilpotent)
  have hzero : ⁅a, d⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    apply commutator_le.mpr
    intro x hx y hy
    exact hcore ((mem_centralizerModulo_iff.mp hy).2 x hx)
  have hd : d ≤ normalizer (a : Set (K ⧸ solvableRadical K)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (Subgroup.centralizer_le_normalizer _)
  let C := ⁅E, a⁆
  have hdC : d ≤ normalizer (C : Set (K ⧸ solvableRadical K)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (show x ∈ normalizer (E : Set _) by
        rw [normalizer_eq_top]; trivial),
      mem_normalizer_iff_map_conj_eq.mp (hd hx)]
  have hLE : L ≤ E := le_sSup hL
  have hLC : L ≤ C := by
    rcases halt with he | ⟨hm, _⟩
    · exact he.le.trans (commutator_mono hLE le_rfl)
    · rcases hL.commutator_dichotomy a with hz | he
      · exact (hm (le_normalizer_iff_commutator_le_left.mpr (by rw [hz]; exact bot_le))).elim
      · exact (le_componentOrbit L a).trans (he.ge.trans (commutator_mono hLE le_rfl))
  have hEC : E ≤ C := by
    change componentLayer _ ≤ C
    rw [horbit]
    apply iSup_le
    intro x
    exact (map_mono hLC).trans
      (mem_normalizer_iff_map_conj_eq.mp (hdC x.property)).le
  let : Group.IsPerfect (pResidual 2 K) := by rw [hres]; infer_instance
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (solvableRadical K)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  apply le_antisymm _ (commutator_le_left _ _)
  apply le_of_map_le_of_perfect_solvable_kernel q (pResidual 2 K)
    ⁅pResidual 2 K, A.subgroupOf K⁆ (commutator_le_left _ _)
    (normalizer_commutator_ge_left _ _)
  simpa only [map_commutator, hr] using hEC

end CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]
open scoped commutatorElement

/-- Full residual action persists across the actual ambient tau orbit. -/
theorem memberResidualOrbit_eq_commutator_of_componentCase
    (T : Sylow 2 G) (J A : Subgroup G) [IsElementaryAbelian 2 A]
    (hcore : pCore 2 G = ⊥) (hAT : A ≤ (T : Subgroup G))
    {P : Subgroup (localGroup T J)}
    (hc : ECaseComponent ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    memberResidualOrbit T J A P = ⁅memberResidualOrbit T J A P, A⁆ := by
  let E := localMemberResidual T J P
  let N := memberResidualOrbit T J A P
  let D := tau (T : Subgroup G) A
  have hAD : A ≤ D := le_sup_left.trans (sup_pCore_le_tau T A hAT)
  have hDN : D ≤ normalizer (N : Set G) := le_normalizer_componentOrbit E D
  have hDA : D ≤ normalizer (A : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro d hd
    apply mem_centralizer_iff.mpr
    intro a ha
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (mem_bot.mp (hcore ▸ (mem_centralizerModulo_iff.mp hd).2 a ha))
  let C := ⁅N, A⁆
  have hDC : D ≤ normalizer (C : Set G) := by
    intro d hd
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hDN hd),
      mem_normalizer_iff_map_conj_eq.mp (hDA hd)]
  have hEN : E ≤ N := le_componentOrbit E D
  have hEC : E ≤ C := by
    let f := (localGroup T J).subtype.comp P.subtype
    have he := congrArg (Subgroup.map f) hc.residual_eq_commutator
    rw [map_commutator] at he
    change ((pResidual 2 P).map P.subtype).map (localGroup T J).subtype ≤ C
    rw [map_map]
    change (pResidual 2 P).map f ≤ C
    rw [he]
    apply commutator_mono (by simpa only [E, localMemberResidual, map_map] using hEN)
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  apply le_antisymm
  · apply iSup_le
    intro d
    exact (map_mono hEC).trans (mem_normalizer_iff_map_conj_eq.mp (hDC d.property)).le
  · exact le_normalizer_iff_commutator_le_left.mp (hAD.trans hDN)

/-- The literal intrinsic residual-action input to E.1.10(8) for K_A. -/
theorem memberOrbitGroup_residual_action_of_componentCase
    (T : Sylow 2 G) (J A : Subgroup G) [IsElementaryAbelian 2 A]
    (hcore : pCore 2 G = ⊥) (hAT : A ≤ (T : Subgroup G))
    {P : Subgroup (localGroup T J)}
    (hc : ECaseComponent ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    pResidual 2 (memberOrbitGroup T J A P) =
      ⁅pResidual 2 (memberOrbitGroup T J A P), A.subgroupOf (memberOrbitGroup T J A P)⁆ := by
  have hAK : A ≤ memberOrbitGroup T J A P :=
    (le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans (tau_le_memberOrbitGroup T J A P)
  apply map_injective (memberOrbitGroup T J A P).subtype_injective
  rw [map_commutator, memberOrbitGroup_residual, map_subgroupOf_eq_of_le hAK]
  exact memberResidualOrbit_eq_commutator_of_componentCase T J A hcore hAT hc

/-- The orbit group's two-residual is its solvable residual in this branch. -/
theorem memberOrbitGroup_residual_eq_solvableResidual_of_componentCase
    (T : Sylow 2 G) (J A : Subgroup G) {P : Subgroup (localGroup T J)}
    (hc : ECaseComponent ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    pResidual 2 (memberOrbitGroup T J A P) =
      solvableResidual (memberOrbitGroup T J A P) := by
  let K := memberOrbitGroup T J A P
  let e := (pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective
  let _ : Group.IsPerfect ((pResidual 2 K).map K.subtype) := by
    rw [memberOrbitGroup_residual]
    exact memberResidualOrbit_isPerfect_of_componentCase T J A hc
  let _ : Group.IsPerfect (pResidual 2 K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let _ : Group.IsNilpotent (K ⧸ pResidual 2 K) :=
    (isPGroup_quotient_pResidual (G := K) 2).isNilpotent
  exact le_antisymm (le_solvableResidual_of_isPerfect _)
    (solvableResidual_le_of_solvable_quotient _)

end CFSG.Quasithin.ChapterE.ChiefOrbit
