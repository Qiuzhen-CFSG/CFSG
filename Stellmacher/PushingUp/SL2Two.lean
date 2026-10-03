module
public import Stellmacher.PushingUp.SL2TwoStructure
public import Stellmacher.OmegaOneCenterMap
public import FeitThompson.PFsection6.Basic

/-!
# The local pushing-up commutator bound

Under the original characteristic-Sylow obstruction (P) and nested-Frattini
SL₂(2) condition (A), the commutator [O₂(M),O²(M)] lies in the commutator of
M with the normal closure of Ω₁(Z(S)). This is the exact local input used by
Stellmacher (2.4); it does not identify the local commutator with the ambient
Section Two subgroup V.

The imported pushing-up structure has two cases. If S is elementary abelian,
its omega center contains O₂(M), so commutator monotonicity suffices. Otherwise
the local commutator is elementary and irreducible. As a nontrivial normal
subgroup of the nilpotent Sylow subgroup it meets Z(S) nontrivially, hence
meets Ω₁(Z(S)) nontrivially. Its intersection with the ambient normal closure
is invariant; irreducibility makes that intersection the whole commutator.
The structural commutator-generation conclusion then gives the desired bound.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Theorems 1--2 and
(2.4), (3.1)--(3.3), specialized to p = 2 and n = 1, as used in
`refs/latex/stellmacher-n-group.tex`, (2.4).
-/

namespace Stellmacher.PushingUp

universe u

private theorem twoResidualAmbient_top_normal
    {M : Type u} [Group M] :
    (twoResidualAmbient (⊤ : Subgroup M)).Normal := by
  have hres : (twoResidualSubgroup (⊤ : Subgroup M)).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N ↦
      Subgroup.normal_iInf_normal fun hN ↦ hN.1
  unfold twoResidualAmbient
  exact hres.map _ fun x ↦ ⟨⟨x, by simp⟩, rfl⟩

private theorem localCommutator_le_of_structure
    {M : Type u} [Group M] [Finite M] (S : Sylow 2 M)
    (hstructure :
      let V := ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆
      IsElementaryAbelian 2 (S : Subgroup M) ∨
        ∃ L : Subgroup M,
          IsElementaryAbelian 2 V ∧
            IsIrreducibleSection L ⊥ V ∧ V ≤ ⁅V, L⁆) :
    let V := ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆
    V ≤ ⁅Subgroup.normalClosure
        (omegaOneCenterAmbient (S : Subgroup M) : Set M),
      (⊤ : Subgroup M)⁆ := by
  classical
  dsimp only at hstructure ⊢
  let Q := pCore 2 M
  let R := twoResidualAmbient (⊤ : Subgroup M)
  let V := ⁅Q, R⁆
  let A := omegaOneCenterAmbient (S : Subgroup M)
  let N := Subgroup.normalClosure (A : Set M)
  let _ : Q.Normal := pCore_normal
  let _ : R.Normal := twoResidualAmbient_top_normal
  have hQS : Q ≤ (S : Subgroup M) := fitting_pCore_le_sylow S
  have hVQ : V ≤ Q := by
    dsimp [V]
    exact Subgroup.commutator_le_left _ _
  have hVS : V ≤ (S : Subgroup M) := hVQ.trans hQS
  change V ≤ ⁅N, (⊤ : Subgroup M)⁆
  rcases hstructure with hSelem | ⟨L, hVelem, hVirred, hVcomm⟩
  · have hSA : (S : Subgroup M) ≤ A := by
      intro x hx
      apply (mem_omegaOneCenterAmbient_iff (S : Subgroup M) x).2
      refine ⟨hx, ?_, ?_⟩
      · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
      · intro s hs
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := S)).comm ⟨s, hs⟩ ⟨x, hx⟩)
    have hAN : A ≤ N := Subgroup.le_normalClosure
    have hQN : Q ≤ N := hQS.trans (hSA.trans hAN)
    exact Subgroup.commutator_mono hQN le_top
  · let _ : IsElementaryAbelian 2 V := hVelem
    have hVnormal : V.Normal := inferInstance
    have hNnormal : N.Normal := Subgroup.normalClosure_normal
    let _ : V.Normal := hVnormal
    let _ : N.Normal := hNnormal
    by_cases hVbot : V = ⊥
    · simp [hVbot]
    have hVsubnormal : (V.subgroupOf (S : Subgroup M)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hVS]
      intro v s hv hs
      exact hVnormal.conj_mem v hv s
    let _ : (V.subgroupOf (S : Subgroup M)).Normal := hVsubnormal
    let _ : Group.IsNilpotent S := S.isPGroup'.isNilpotent
    have hVsubne : V.subgroupOf (S : Subgroup M) ≠ ⊥ := by
      intro hsubbot
      apply hVbot
      have hdisjoint : Disjoint V (S : Subgroup M) :=
        Subgroup.subgroupOf_eq_bot.mp hsubbot
      exact (inf_eq_left.2 hVS).symm.trans (disjoint_iff.mp hdisjoint)
    have hcenter :
        V.subgroupOf (S : Subgroup M) ⊓ Subgroup.center S ≠ ⊥ :=
      Section6.nilpotent_normal_inf_center_ne_bot
        (V.subgroupOf (S : Subgroup M)) hVsubne
    obtain ⟨x, hx, hxne⟩ :=
      (V.subgroupOf (S : Subgroup M) ⊓ Subgroup.center S).bot_or_exists_ne_one.resolve_left
        hcenter
    have hxV : (x : M) ∈ V := hx.1
    have hxA : (x : M) ∈ A := by
      apply (mem_omegaOneCenterAmbient_iff (S : Subgroup M) (x : M)).2
      refine ⟨x.property, ?_, ?_⟩
      · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : M) hxV
      · intro s hs
        exact congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp hx.2) ⟨s, hs⟩)
    have hxN : (x : M) ∈ N := Subgroup.le_normalClosure hxA
    have hVNne : V ⊓ N ≠ ⊥ := by
      intro hbot
      have hxone : (x : M) = 1 := by
        have : (x : M) ∈ (⊥ : Subgroup M) := by
          rw [← hbot]
          exact ⟨hxV, hxN⟩
        simpa using this
      exact hxne (Subtype.ext hxone)
    have hVNinv : IsConjugateInvariantBy (V ⊓ N) L := by
      intro l a ha
      exact ⟨hVnormal.conj_mem a ha.1 l, hNnormal.conj_mem a ha.2 l⟩
    have hVNeq : V ⊓ N = V := by
      rcases hVirred.2.2 (V ⊓ N) bot_le inf_le_left hVNinv with hbot | hV
      · exact (hVNne hbot).elim
      · exact hV
    have hVN : V ≤ N := by
      rw [← hVNeq]
      exact inf_le_right
    exact hVcomm.trans (Subgroup.commutator_mono hVN le_top)


public theorem sl2Two_localCommutator_le_centerNormalClosureCommutator
    {M : Type u} [Group M] [Finite M] (S : Sylow 2 M)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup M).subtype).Normal)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M))) :
    ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆ ≤
      ⁅Subgroup.normalClosure
          (omegaOneCenterAmbient (S : Subgroup M) : Set M),
        (⊤ : Subgroup M)⁆ :=
  localCommutator_le_of_structure S (sl2Two_structure S hP hA)


end Stellmacher.PushingUp
