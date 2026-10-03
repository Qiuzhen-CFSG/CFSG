module
public import Stellmacher.PushingUp.CriticalCommutatorNoncentral
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Normality of the shared core at the left vertex

Suppose `Q_a` lies in `G_u`, and a subgroup `V` of `G_a` is normal there
and contains `Z_u`. If `[V,Q_a ∩ Q_u]` is central in both stabilizers, then
`Q_a ∩ Q_u` is normal in `G_a`. The positive critical pair at `u` supplies
the natural-module noncentrality criterion; all other inputs are explicit
conclusions of the preceding steps of the distance-bound proof.

Take the normal closure `X` of the shared core inside `G_a`. It lies in
`Q_a`. Since `V` is normal and the commutator denominator is central in
`G_a`, the normal-closure commutator theorem gives
`[V,X] ≤ [V,Q_a ∩ Q_u]`. In particular `[Z_u,X]` is central in `G_u`.
The critical natural action forces the 2-subgroup `X` into `Q_u`, so its
normal closure is just the original shared core. Every normal closure and
quotient used here is inside a finite stabilizer, with no finiteness
hypothesis on the graph or free amalgam.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.4), step (4),
journal p.13. This is the normal-closure part after the source has shown
its subgroup `Y` central in both stabilizers.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
/-- A bicentral commutator forces the shared core to be normal on the left. -/
public theorem shift_coreIntersection_normal_left_of_bicentral
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a u c : Vertex S) (hcritU : IsCriticalPair S u c)
    (hb : 0 < criticalDistance S)
    (hQaGu : vertexTwoCore S a ≤ stabilizer S u)
    (V : Subgroup (FreeAmalgam S)) (hVGa : V ≤ stabilizer S a)
    (hVnormal : (V.subgroupOf (stabilizer S a)).Normal)
    (hZuV : vertexZ S u ≤ V)
    (hcentA : ⁅V, vertexTwoCore S a ⊓ vertexTwoCore S u⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype)
    (hcentU : ⁅V, vertexTwoCore S a ⊓ vertexTwoCore S u⁆ ≤
      (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype) :
    ((vertexTwoCore S a ⊓ vertexTwoCore S u).subgroupOf
      (stabilizer S a)).Normal := by
  let G := stabilizer S a
  let K := (vertexTwoCore S a ⊓ vertexTwoCore S u).subgroupOf G
  let W := V.subgroupOf G
  let Y := ⁅W, K⁆
  let X := Subgroup.normalClosure (K : Set G)
  let XA := X.map G.subtype
  have hWnormal : W.Normal := hVnormal
  let _ : W.Normal := hWnormal
  have hKGa : vertexTwoCore S a ⊓ vertexTwoCore S u ≤ G :=
    inf_le_left.trans (Subgroup.map_subtype_le _)
  have hKmap : K.map G.subtype = vertexTwoCore S a ⊓ vertexTwoCore S u :=
    Subgroup.map_subgroupOf_eq_of_le hKGa
  have hWmap : W.map G.subtype = V :=
    Subgroup.map_subgroupOf_eq_of_le hVGa
  have hYmap : Y.map G.subtype = ⁅V, vertexTwoCore S a ⊓ vertexTwoCore S u⁆ := by
    rw [Subgroup.map_commutator, hWmap, hKmap]
  have hYcenter : Y ≤ Subgroup.center G := by
    rw [← Subgroup.map_le_map_iff_of_injective G.subtype_injective, hYmap]
    exact hcentA
  let _ : Y.Normal := ⟨by
    intro y hy g
    have hc := Subgroup.mem_center_iff.mp (hYcenter hy) g
    rw [hc]
    simpa [mul_assoc] using hy⟩
  have hKQ : K ≤ pCore 2 G := by
    rw [← Subgroup.map_le_map_iff_of_injective G.subtype_injective, hKmap]
    exact inf_le_left
  have hXQ : X ≤ pCore 2 G := Subgroup.normalClosure_le_normal hKQ
  have hXAQa : XA ≤ vertexTwoCore S a := Subgroup.map_mono hXQ
  have hXAGu : XA ≤ stabilizer S u := hXAQa.trans hQaGu
  have hXAtwo : IsPGroup 2 XA :=
    ((pCore_isPGroup (p := 2) (G := G)).to_le hXQ).map G.subtype
  have hWX : ⁅W, X⁆ ≤ Y :=
    Subgroup.commutator_normalClosure_le_of_normal W K Y le_rfl
  have hVXA : ⁅V, XA⁆ ≤
      ⁅V, vertexTwoCore S a ⊓ vertexTwoCore S u⁆ := by
    have hm := Subgroup.map_mono (f := G.subtype) hWX
    rwa [Subgroup.map_commutator, hWmap, hYmap] at hm
  have hXAQu : XA ≤ vertexTwoCore S u := by
    by_contra hnot
    apply criticalPair_commutator_not_le_center S T hTS hP hSne hA u c
      hcritU hb XA hXAGu hXAtwo hnot
    exact (Subgroup.commutator_mono hZuV le_rfl).trans (hVXA.trans hcentU)
  have hXK : X ≤ K := by
    intro x hx
    have hxA : (x : FreeAmalgam S) ∈ XA := Subgroup.mem_map_of_mem G.subtype hx
    exact ⟨hXAQa hxA, hXAQu hxA⟩
  have hKX : K ≤ X := Subgroup.subset_normalClosure
  have heq : K = X := le_antisymm hKX hXK
  change K.Normal
  rw [heq]
  exact Subgroup.normalClosure_normal
end Stellmacher.PushingUp
