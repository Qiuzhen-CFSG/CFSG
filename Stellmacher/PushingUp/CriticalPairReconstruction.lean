module

public import Stellmacher.PushingUp.CriticalPairSL2TwoData
public import Theory.GroupTheory.PCoreOddIndex

/-!
# Unbarred reconstruction for a critical pair

This module proves the final reconstruction step in Stellmacher, *Pushing
up*, Arch. Math. 46 (1986), Lemma (2.2), journal p.11.  The finite-module
argument has already produced a Sylow subgroup `Sbar` of the faithful local
action quotient, identified it with the image of `Z_{a'}`, and supplied the
fixed-space decomposition.  We lift those facts back to the vertex
stabilizer.

For the Sylow assertion, extend `Z_{a'} O₂(G_a)` to a Sylow subgroup `R` of
`G_a`.  Its quotient image contains and hence equals `Sbar`.  Thus `R` lies
in `Z_{a'} C_{G_a}(Z_a)`; the intersection of `R` with that centralizer lies
in `O₂(G_a)` because the latter has odd index.  This forces
`R = Z_{a'} O₂(G_a)`.

For the omega-center assertion, first identify
`Omega₁(Z(Z_{a'} O₂(G_a)))` with `Z_a ∩ O₂(G_{a'})`.  The forward
inclusion uses the definition of `Z_a` as the join of all local Sylow omega
centers and the odd centralizer at `a'`; the reverse uses the endpoint
omega-core inclusions.  Mapping the supplied fixed-space decomposition then
gives exactly the source's commutator and central-intersection formula.

The action-centralizer comparison and all subgroup/subtype bookkeeping are
private.  The public theorem returns only the two source clauses consumed by
the thin (2.2) assembly.  Its `hV` argument only fixes the elementary-abelian
instance used by the package types and named quotient action.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

private theorem isSylowSubgroupIn_of_quotient_image
    {G : Type u} [Group G] [Finite G]
    (C A : Subgroup G) [C.Normal]
    (hQC : pCore 2 G ≤ C)
    (hodd : ¬ 2 ∣ ((pCore 2 G).subgroupOf C).index)
    (hA2 : IsPGroup 2 A)
    (Sbar : Sylow 2 (G ⧸ C))
    (hAmap : A.map (QuotientGroup.mk' C) = (Sbar : Subgroup (G ⧸ C))) :
    ∃ R : Sylow 2 G,
      (R : Subgroup G) = A ⊔ pCore 2 G := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := pCore 2 G
  let H : Subgroup G := A ⊔ Q
  have hQnormal : Q.Normal := pCore_normal
  let _ : Q.Normal := hQnormal
  have hH2 : IsPGroup 2 H :=
    hA2.to_sup_of_normal_right (pCore_isPGroup (p := 2) (G := G))
  obtain ⟨R, hHR⟩ := hH2.exists_le_sylow
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let Rbar : Sylow 2 (G ⧸ C) :=
    R.mapSurjective (QuotientGroup.mk'_surjective C)
  have hSbarRbar : (Sbar : Subgroup (G ⧸ C)) ≤ Rbar := by
    rw [← hAmap, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono (le_sup_left.trans hHR)
  have hRbar : (Rbar : Subgroup (G ⧸ C)) = Sbar :=
    Sbar.is_maximal' Rbar.isPGroup' hSbarRbar
  have hRmap : (R : Subgroup G).map q = A.map q := by
    change (Rbar : Subgroup (G ⧸ C)) = A.map q
    exact hRbar.trans hAmap.symm
  have hRC : (R : Subgroup G) ⊓ C ≤ Q := by
    exact R.isPGroup'.to_inf_left.le_pCore_of_le_oddIndexOverCore
      hQC hodd inf_le_right
  have hRH : (R : Subgroup G) ≤ H := by
    intro r hr
    have hrAC : r ∈ A ⊔ C := by
      have hrmap : q r ∈ A.map q := by
        rw [← hRmap]
        exact Subgroup.mem_map_of_mem q hr
      have : r ∈ (A.map q).comap q := hrmap
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    obtain ⟨a, ha, c, hc, hac⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hrAC
    have haR : a ∈ (R : Subgroup G) :=
      hHR ((show A ≤ H from le_sup_left) ha)
    have hcR : c ∈ (R : Subgroup G) := by
      have hcar : a⁻¹ * r = c := by rw [← hac]; simp
      rw [← hcar]
      exact (R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem haR) hr
    have hcQ : c ∈ Q := hRC ⟨hcR, hc⟩
    rw [← hac]
    exact H.mul_mem ((show A ≤ H from le_sup_left) ha)
      ((show Q ≤ H from le_sup_right) hcQ)
  have hRHeq : (R : Subgroup G) = H := le_antisymm hRH hHR
  exact ⟨R, hRHeq⟩

private theorem criticalPair_sourceSylow
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV)
    (Sbar : Sylow 2 (VertexActionQuotient S a))
    (hTbar : oppositeImage S a a' ha' = (Sbar : Subgroup _)) :
    IsSylowSubgroupIn
      (vertexZ S a' ⊔ vertexTwoCore S a) (stabilizer S a) := by
  classical
  let G := stabilizer S a
  let C : Subgroup G := vertexActionCentralizer S a
  let A : Subgroup G := (vertexZ S a').subgroupOf (stabilizer S a)
  let _ : C.Normal := vertexActionCentralizer_normal S a
  let _ : IsElementaryAbelian 2
      (omegaOneCenterAmbient (vertexTwoCore S a')) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hOmega2 : IsPGroup 2 (omegaOneCenterAmbient (vertexTwoCore S a')) :=
    IsElementaryAbelian.isPGroup 2 _
  have hA2ambient : IsPGroup 2 (vertexZ S a') :=
    hOmega2.to_le hinputs.right_Z_le_coreOmega
  have hA2 : IsPGroup 2 A :=
    hA2ambient.of_equiv (Subgroup.subgroupOfEquivOfLe ha').symm
  have hCeq : C = vertexCentralizerLocal S a := by
    simpa [C, G] using vertexActionCentralizer_eq_vertexCentralizerLocal S a
  obtain ⟨R, hR⟩ :=
    isSylowSubgroupIn_of_quotient_image C A
      (by rw [hCeq]; exact
        hinputs.critical.centralizer_odd.core_le_centralizer)
      (by rw [hCeq]; exact
        hinputs.critical.centralizer_odd.centralizer_mod_core_odd)
      hA2 Sbar
      (by simpa [C, A, G] using hTbar)
  refine ⟨R, ?_⟩
  rw [hR, Subgroup.map_sup]
  change A.map G.subtype ⊔ (pCore 2 G).map G.subtype =
    vertexZ S a' ⊔ vertexTwoCore S a
  rw [Subgroup.map_subgroupOf_eq_of_le ha']
  rfl

private theorem criticalPair_omegaCenter
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    {hV : IsElementaryAbelian 2 (vertexModule S a)}
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV)
    (hSylow : IsSylowSubgroupIn
      (vertexZ S a' ⊔ vertexTwoCore S a) (stabilizer S a)) :
    omegaOneCenterAmbient (vertexZ S a' ⊔ vertexTwoCore S a) =
      vertexZ S a ⊓ vertexTwoCore S a' := by
  classical
  let H : Subgroup (FreeAmalgam S) :=
    vertexZ S a' ⊔ vertexTwoCore S a
  let W : Subgroup (FreeAmalgam S) := omegaOneCenterAmbient H
  have hWZ : W ≤ vertexZ S a := by
    obtain ⟨P, hP⟩ := hSylow
    dsimp only [W, H]
    rw [← hP]
    change sylowOmegaAt S a P ≤ vertexZ S a
    apply le_sSup
    exact ⟨P, rfl⟩
  have hWGa' : W ≤ stabilizer S a' :=
    hWZ.trans hinputs.left_Z_le_right_stabilizer
  let Wa' : Subgroup (stabilizer S a') :=
    W.subgroupOf (stabilizer S a')
  let _ : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian H
  have hW2 : IsPGroup 2 W := IsElementaryAbelian.isPGroup 2 _
  have hWa'2 : IsPGroup 2 Wa' :=
    hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWGa').symm
  have hWa'C : Wa' ≤ vertexCentralizerLocal S a' := by
    intro x hx
    rw [mem_vertexCentralizerLocal_iff]
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hxW : (x : FreeAmalgam S) ∈ W := hx
    exact (mem_omegaOneCenterAmbient_iff H (x : FreeAmalgam S)).mp hxW |>.2.2
      z ((show vertexZ S a' ≤ H from le_sup_left) hz)
  have hWa'Q : Wa' ≤ pCore 2 (stabilizer S a') :=
    hWa'2.le_pCore_of_le_oddIndexOverCore
      hinputs.oppositeCentralizer_odd.core_le_centralizer
      hinputs.oppositeCentralizer_odd.centralizer_mod_core_odd hWa'C
  have hWQ' : W ≤ vertexTwoCore S a' := by
    intro x hx
    change x ∈ (pCore 2 (stabilizer S a')).map (stabilizer S a').subtype
    let xa' : stabilizer S a' := ⟨x, hWGa' hx⟩
    exact ⟨xa', hWa'Q (show xa' ∈ Wa' from hx), rfl⟩
  apply le_antisymm
  · exact fun _ hx ↦ ⟨hWZ hx, hWQ' hx⟩
  · intro x hx
    have hxOmegaQ := hinputs.left_Z_le_coreOmega hx.1
    obtain ⟨hxQ, hxpow, hxcentQ⟩ :=
      (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) x).mp hxOmegaQ
    have hxcentA : x ∈
        Subgroup.centralizer (vertexZ S a' : Set (FreeAmalgam S)) := by
      have hxQ' := hx.2
      change x ∈ (pCore 2 (stabilizer S a')).map
        (stabilizer S a').subtype at hxQ'
      obtain ⟨y, hy, rfl⟩ := hxQ'
      exact (mem_vertexCentralizerLocal_iff S a' y).mp
        (hinputs.oppositeCentralizer_odd.core_le_centralizer hy)
    apply (mem_omegaOneCenterAmbient_iff H x).mpr
    refine ⟨(show vertexTwoCore S a ≤ H from le_sup_right) hxQ, hxpow, ?_⟩
    apply Subgroup.mem_centralizer_iff.mp
    dsimp only [H]
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro q hq
    rcases hq with hq | hq
    · exact Subgroup.mem_centralizer_iff.mp hxcentA q hq
    · exact hxcentQ q hq

private theorem vertexCenterPart_map
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a : Vertex S) :
    ((vertexCenterPart S a).map (vertexModule S a).subtype).map
        (stabilizer S a).subtype =
      vertexZ S a ⊓
        (Subgroup.center (VertexGroup S a)).map (stabilizer S a).subtype := by
  change (((Subgroup.center (VertexGroup S a)).comap
      (vertexModule S a).subtype).map (vertexModule S a).subtype).map
        (stabilizer S a).subtype = _
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype,
    Subgroup.map_inf (vertexModule S a)
      (Subgroup.center (VertexGroup S a)) (stabilizer S a).subtype
      (stabilizer S a).subtype_injective,
    vertexZ_eq_local_vSubgroup]

private theorem criticalPair_sourceOmegaCenter
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV)
    (hfixed : CriticalPairSL2Two.FixedSpaceData S a a' ha' hV)
    (hSylow : IsSylowSubgroupIn
      (vertexZ S a' ⊔ vertexTwoCore S a) (stabilizer S a))
    (hdecomp :
      let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
      let _ := vertexQuotientConjugationAction S a
      FixedPoints.subgroup (oppositeImage S a a' ha')
          (vertexModule S a) =
        commutatorAction (oppositeImage S a a' ha')
            (vertexModule S a) ⊔
          FixedPoints.subgroup (VertexActionQuotient S a)
            (vertexModule S a)) :
    omegaOneCenterAmbient (vertexZ S a' ⊔ vertexTwoCore S a) =
      ⁅vertexZ S a, vertexZ S a'⁆ ⊔
        (vertexZ S a ⊓
          (Subgroup.center (VertexGroup S a)).map (stabilizer S a).subtype) := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  rw [criticalPair_omegaCenter S a a' ha' hinputs hSylow]
  rw [← hfixed.oppositeFixed_map, hdecomp, Subgroup.map_sup,
    Subgroup.map_sup, hfixed.commutator_map,
    hfixed.globalFixed_eq_centerPart, vertexCenterPart_map]

/-- The unbarred Sylow and omega-center reconstruction in Stellmacher's
critical-pair argument, after applying the barred finite-module theorem. -/
public theorem criticalPair_reconstruction
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV)
    (hfixed : CriticalPairSL2Two.FixedSpaceData S a a' ha' hV)
    (Sbar : Sylow 2 (VertexActionQuotient S a))
    (hTbar : oppositeImage S a a' ha' = (Sbar : Subgroup _))
    (hdecomp :
      let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
      let _ := vertexQuotientConjugationAction S a
      FixedPoints.subgroup (oppositeImage S a a' ha')
          (vertexModule S a) =
        commutatorAction (oppositeImage S a a' ha')
            (vertexModule S a) ⊔
          FixedPoints.subgroup (VertexActionQuotient S a)
            (vertexModule S a)) :
    IsSylowSubgroupIn
        (vertexZ S a' ⊔ vertexTwoCore S a) (stabilizer S a) ∧
      omegaOneCenterAmbient (vertexZ S a' ⊔ vertexTwoCore S a) =
        ⁅vertexZ S a, vertexZ S a'⁆ ⊔
          (vertexZ S a ⊓
            (Subgroup.center (VertexGroup S a)).map
              (stabilizer S a).subtype) := by
  have hSylow :=
    criticalPair_sourceSylow S a a' ha' hV hinputs Sbar hTbar
  exact ⟨hSylow,
    criticalPair_sourceOmegaCenter S a a' ha' hV hinputs hfixed hSylow
      hdecomp⟩

end Stellmacher.PushingUp
