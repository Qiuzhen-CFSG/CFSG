module
public import Stellmacher.PushingUp.SL2TwoStructure
public import Stellmacher.TwoResidualSylowSupplement

/-!
# Local pushing-up inside a prescribed normal module

Suppose a finite local group satisfies pushing-up hypotheses (P) and the
nested Frattini SL₂(2) condition (A). Let V be normal and contained in its
Sylow two-subgroup. A homomorphism with kernel C(V) detects the conjugation
action: assume its Sylow image is nontrivial and its full image is not a
two-group. Then [O₂(M),O²(M)] lies in this prescribed V.

The elementary Sylow branch of the pushing-up structure would centralize V,
contradicting its nontrivial image. In the other branch the local commutator
W is irreducible. The subgroup [V,O²(M)] lies in W∩V and is nontrivial:
otherwise residual-Sylow generation would make the full image a two-group.
Normality makes W∩V invariant, and irreducibility gives W≤V.

This supplies the original-module transfer in Stellmacher (4.6), Journal
of Algebra 190 (1997), p26, for its application of (2.4). The imported
structure comes from Stellmacher, Pushing up, Arch. Math. 46 (1986).
-/

namespace Stellmacher.PushingUp

private theorem residual_normal {M : Type*} [Group M] :
    (twoResidualAmbient (⊤ : Subgroup M)).Normal := by
  have hres : (twoResidualSubgroup (⊤ : Subgroup M)).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N ↦
      Subgroup.normal_iInf_normal fun hN ↦ hN.1
  unfold twoResidualAmbient
  exact hres.map _ fun x ↦ ⟨⟨x, by simp⟩, rfl⟩

/-- A prescribed normal module contains the local commutator when both the Sylow
and an odd part of the local action act nontrivially. -/
public theorem sl2Two_localCommutator_le_normal_module
    {M H : Type*} [Group M] [Finite M] [Group H]
    (S : Sylow 2 M)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup M).subtype).Normal)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (V : Subgroup M) [V.Normal] (hVS : V ≤ (S : Subgroup M))
    (f : M →* H) (hker : f.ker = Subgroup.centralizer (V : Set M))
    (hSimage : (S : Subgroup M).map f ≠ ⊥)
    (himage : ¬ IsPGroup 2 f.range) :
    ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆ ≤ V := by
  let R := twoResidualAmbient (⊤ : Subgroup M)
  let W := ⁅pCore 2 M, R⁆
  let _ : R.Normal := residual_normal
  let _ : W.Normal := inferInstance
  have hVtwo : IsPGroup 2 V := S.isPGroup'.to_le hVS
  have hVcore : V ≤ pCore 2 M := le_sSup ⟨inferInstance, hVtwo⟩
  have hVRne : ⁅V, R⁆ ≠ ⊥ := by
    intro hbot
    have hRC : R ≤ Subgroup.centralizer (V : Set M) :=
      Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hRmap : R.map f = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (hRC.trans_eq hker.symm)
    have himageEq : f.range = (S : Subgroup M).map f := by
      rw [MonoidHom.range_eq_map, ← twoResidualAmbient_top_sup_sylow S,
        Subgroup.map_sup, hRmap, bot_sup_eq]
    exact himage (himageEq ▸ S.isPGroup'.map f)
  rcases sl2Two_structure S hP hA with hSe | ⟨L, _hWe, hWi, _hWcomm⟩
  · let _ : IsElementaryAbelian 2 (S : Subgroup M) := hSe
    apply False.elim
    apply hSimage
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hker]
    intro s hs
    apply Subgroup.mem_centralizer_iff.mpr
    intro v hv
    exact setLike_mul_comm (hVS hv) hs
  · have hVWne : W ⊓ V ≠ ⊥ := by
      intro hbot
      apply hVRne
      apply le_bot_iff.mp
      rw [← hbot]
      exact le_inf (Subgroup.commutator_mono hVcore le_rfl)
        (Subgroup.commutator_le_left _ _)
    have hVWnormal : (W ⊓ V).Normal := inferInstance
    have hInv : IsConjugateInvariantBy (W ⊓ V) L := by
      intro l a ha
      exact hVWnormal.conj_mem a ha l
    rcases hWi.2.2 (W ⊓ V) bot_le inf_le_left hInv with hbot | hW
    · exact (hVWne hbot).elim
    · change W ⊓ V = W at hW
      change W ≤ V
      rw [← hW]
      exact inf_le_right

end Stellmacher.PushingUp
