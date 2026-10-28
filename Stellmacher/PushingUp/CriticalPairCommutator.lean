module

public import Stellmacher.PushingUp.CriticalPairPath
public import Stellmacher.PushingUp.CriticalPairResidualTransport
public import Theory.GroupTheory.PCoreOddIndex

/-!
# Critical-pair commutators and reversal

This module proves clauses (b)--(d) of Stellmacher, *Pushing up*, Arch. Math.
46 (1986), Lemma (1.4), journal pp.10--11.  Starting with a critical pair
`(a,a')` at positive critical distance, it proves that
`[Z_a,Z_a']` is nontrivial and lies in `Z_a ∩ Z_a'`, that both oriented
left-normed triple commutators vanish, and that `(a',a)` is again critical.
Clause (a)'s odd-centralizer conclusion at `a` is included in the packaged
result.

The proof imports two source-neutral reductions.  `criticalPair_path`
supplies the opposite M-vertex orbit, mutual endpoint containment, the
intersection bound, and reversal once nontriviality is known.
`hasMinimalFrattiniResidual_of_mOrbit` transports the single nested-residual
minimality hypothesis from `a` to `a'`; no second such hypothesis is
assumed.

For nontriviality, suppose `Z_a` centralizes `Z_a'`.  Then `Z_a`, viewed
inside the stabilizer of `a'`, is a 2-subgroup of the local centralizer.
Clause (a) says that the vertex 2-core has odd index in this centralizer, so
it is its unique Sylow 2-subgroup.  Hence `Z_a` lies in that 2-core and then
in the neighborhood kernel at `a'`, contradicting criticality.  Finally
(1.3)(e) puts both endpoint groups in elementary-abelian omega centers; the
intersection bound therefore gives the two triple-commutator identities.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

namespace CriticalPairCommutator

public structure Conclusion (S : Subgroup M) (a a' : Vertex S) : Prop where
  centralizer_odd : CriticalVertexCentralizer.Conclusion S a
  commutator_ne_bot : ⁅vertexZ S a, vertexZ S a'⁆ ≠ ⊥
  commutator_le_inf :
    ⁅vertexZ S a, vertexZ S a'⁆ ≤ vertexZ S a ⊓ vertexZ S a'
  left_triple_commutator :
    ⁅⁅vertexZ S a, vertexZ S a'⁆, vertexZ S a⁆ = ⊥
  right_triple_commutator :
    ⁅⁅vertexZ S a', vertexZ S a⁆, vertexZ S a'⁆ = ⊥
  reverse_critical : IsCriticalPair S a' a

end CriticalPairCommutator

private theorem adjacent_of_mOrbit (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) :
    ∃ b : Vertex S, Adjacent S a b := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g (hVertex S 1), ?_⟩
  exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2
    (base_adjacent S)

private theorem vertexZ_le_coreOmega_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) := by
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  exact
    (criticalDistance_basic S T hTS hP hSne a b ha hab).vertexZ_le_coreOmega_or_distance_zero
      |>.resolve_right (Nat.ne_of_gt hb)

private theorem vertexZ_isPGroup_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    IsPGroup 2 (vertexZ S a) := by
  have hOmega : IsPGroup 2 (omegaOneCenterAmbient (vertexTwoCore S a)) := by
    let _ : IsElementaryAbelian 2
        (omegaOneCenterAmbient (vertexTwoCore S a)) :=
      omegaOneCenterAmbient_elementaryAbelian _
    exact IsElementaryAbelian.isPGroup 2 _
  exact hOmega.to_le
    (vertexZ_le_coreOmega_of_pos S T hTS hP hSne a ha hb)

private theorem vertexZ_self_commutator_eq_bot_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    ⁅vertexZ S a, vertexZ S a⁆ = ⊥ := by
  let W := omegaOneCenterAmbient (vertexTwoCore S a)
  let _ : IsElementaryAbelian 2 W :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hWab : ⁅W, W⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
  apply le_bot_iff.mp
  exact (Subgroup.commutator_mono
    (vertexZ_le_coreOmega_of_pos S T hTS hP hSne a ha hb)
    (vertexZ_le_coreOmega_of_pos S T hTS hP hSne a ha hb)).trans
      (le_of_eq hWab)

private theorem vertexTwoCore_le_neighborhoodKernel [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a) :
    vertexTwoCore S a ≤ neighborhoodKernel S a := by
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  obtain ⟨P, hPmap⟩ :=
    (criticalDistance_basic S T hTS hP hSne a b ha hab).twoCore_sylow_kernel
  rw [← hPmap]
  exact Subgroup.map_subtype_le _

/-- Stellmacher, *Pushing up* (1986), Lemma (1.4)(b)--(d). -/
public theorem criticalPair_commutator [Finite M]
    {S : Subgroup M}
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a a' : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (hres : HasMinimalFrattiniResidual S a) :
    CriticalPairCommutator.Conclusion S a a' := by
  classical
  have hpath := criticalPair_path T hTS hP hSne a a' hcrit hb
  have ha' := hpath.opposite_inMVertexOrbit
  have hres' :=
    hasMinimalFrattiniResidual_of_mOrbit S hcrit.1 ha' hres
  have hcentralA :=
    criticalVertex_centralizer_oddIndex T hTS hP hSne a hcrit.1 hb hres
  have hcentralA' :=
    criticalVertex_centralizer_oddIndex T hTS hP hSne a' ha' hb hres'
  have hcomm_ne : ⁅vertexZ S a, vertexZ S a'⁆ ≠ ⊥ := by
    intro hcomm_bot
    let A : Subgroup (stabilizer S a') :=
      (vertexZ S a).subgroupOf (stabilizer S a')
    have hAcentral : A ≤ vertexCentralizerLocal S a' := by
      intro x hx
      apply (mem_vertexCentralizerLocal_iff S a' x).2
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot) hx
    have hA2 : IsPGroup 2 A :=
      (vertexZ_isPGroup_of_pos S T hTS hP hSne a hcrit.1 hb).of_equiv
        (Subgroup.subgroupOfEquivOfLe hpath.left_Z_le_right_stabilizer).symm
    have hAcore : A ≤ pCore 2 (stabilizer S a') :=
      hA2.le_pCore_of_le_oddIndexOverCore
        hcentralA'.core_le_centralizer
        hcentralA'.centralizer_mod_core_odd hAcentral
    have hZaCore : vertexZ S a ≤ vertexTwoCore S a' := by
      intro z hz
      exact Subgroup.mem_map_of_mem (stabilizer S a').subtype
        (hAcore (show
          (⟨z, hpath.left_Z_le_right_stabilizer hz⟩ : stabilizer S a') ∈ A
            from hz))
    exact hcrit.2.2 <| hZaCore.trans
      (vertexTwoCore_le_neighborhoodKernel S T hTS hP hSne a' ha')
  have hcomm_le := hpath.commutator_le_intersection
  have hselfA : ⁅vertexZ S a, vertexZ S a⁆ = ⊥ :=
    vertexZ_self_commutator_eq_bot_of_pos
      S T hTS hP hSne a hcrit.1 hb
  have hselfA' : ⁅vertexZ S a', vertexZ S a'⁆ = ⊥ :=
    vertexZ_self_commutator_eq_bot_of_pos
      S T hTS hP hSne a' ha' hb
  have htripleA : ⁅⁅vertexZ S a, vertexZ S a'⁆, vertexZ S a⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono (hcomm_le.trans inf_le_left) le_rfl).trans
      (le_of_eq hselfA)
  have hcomm_le_rev : ⁅vertexZ S a', vertexZ S a⁆ ≤ vertexZ S a' := by
    rw [Subgroup.commutator_comm]
    exact hcomm_le.trans inf_le_right
  have htripleA' : ⁅⁅vertexZ S a', vertexZ S a⁆, vertexZ S a'⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hcomm_le_rev le_rfl).trans
      (le_of_eq hselfA')
  exact {
    centralizer_odd := hcentralA
    commutator_ne_bot := hcomm_ne
    commutator_le_inf := hcomm_le
    left_triple_commutator := htripleA
    right_triple_commutator := htripleA'
    reverse_critical := hpath.reverse_critical_of_commutator_ne hcomm_ne
  }

end Stellmacher.PushingUp
