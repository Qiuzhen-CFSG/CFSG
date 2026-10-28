module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Center
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual

/-!
# Excluding simultaneous displacement by the exchanged residuals

Let K = O₂(Y_L) ∩ O₂(Y_C). Index two and residual exchange make K invariant
under t. If both residuals displace all of Q, then Q ≤ K. Fixation of Z(Q)
by Y_C and faithfulness of the natural action put K in O₂(L). The residual
commutator bound then proves the actual identities [K,Y_L] = Q = [K,Y_C].
Conjugating these identities proves Qᵗ = Q, hence Z(Q)ᵗ = Z(Q). Exchange
would now make Y_L fix Z(Q), contrary to its faithful natural action.

This proves the needed moving-case contradiction without assuming the stronger
printed intersection equality K = Q or assuming Qᵗ = Q. The full-displacement
and fixed-or-moving calculations remain separate mathematical obligations.

Source: Aschbacher–Smith, proof of 15.3.23, k = 3 paragraph, printed p.1129
(combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W" => Fin 3 → ZMod 2

variable [Finite G]

omit [Finite G] in
/-- Index two and exchange transport the S-invariance of Y_L to Y_C. -/
theorem S_normalizes_YC (d : LocalData G) (L : Subgroup G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d L).conjBy t = YC d L) :
    d.S ≤ normalizer (YC d L : Set G) := by
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  rw [← hex]
  change d.S ≤ normalizer ((YL d L).map (MulAut.conj t).toMonoidHom : Set G)
  rw [← map_equiv_normalizer_eq]
  have h := map_mono (f := (MulAut.conj t).toMonoidHom) hSYL
  have he : d.S.map (MulAut.conj t).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS ht)
  rwa [he] at h

omit [Finite G] in
/-- The square of the exchanging element lies in S, so the reverse exchange holds. -/
theorem exchange_back (d : LocalData G) (L : Subgroup G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d L).conjBy t = YC d L) :
    (YC d L).conjBy t = YL d L := by
  have ht2 : t ^ 2 ∈ d.S := (d.S.subgroupOf (d.T : Subgroup G)).sq_mem_of_index_two
    hindex ⟨t, ht⟩
  rw [← hex, ← conjBy_mul, ← pow_two]
  exact mem_normalizer_iff_map_conj_eq.mp (hSYL ht2)

/-- The incompatible actions on the actual natural center exclude conjugation invariance. -/
theorem core_not_conjugation_invariant (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hU : ⁅d.V, YL d L⁆ ≠ ⊥)
    (hfix : YC d L ≤ centralizer (coreCenter L : Set G))
    (t : G) (hex : (YL d L).conjBy t = YC d L) :
    (commutatorCore L).conjBy t ≠ commutatorCore L := by
  intro hQ
  have hZ : (coreCenter L).map (MulAut.conj t).toMonoidHom = coreCenter L := by
    unfold coreCenter
    rw [map_subgroup_center_eq _ (MulAut.conj t).injective]
    exact congrArg (fun H : Subgroup G => (center H).map H.subtype) hQ
  apply YL_not_fixes_center d L m hU
  intro y hy z hz
  have hy' : (MulAut.conj t) y ∈ YC d L := hex ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hy
  have hz' : (MulAut.conj t) z ∈ coreCenter L := hZ ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hz
  have h := hfix hy' _ hz'
  apply (MulAut.conj t).injective
  simpa only [map_mul] using h

/-- The actual intersection of the residual two-cores. -/
noncomputable def commonCore (d : LocalData G) (L : Subgroup G) : Subgroup G :=
  (YL d L).pCoreIn 2 ⊓ (YC d L).pCoreIn 2

omit [Finite G] in
/-- The literal intersection of the two residual cores is preserved by exchange. -/
theorem commonCore_conj_eq (d : LocalData G) (L : Subgroup G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d L).conjBy t = YC d L) :
    (commonCore d L).conjBy t = commonCore d L := by
  have hback := exchange_back d L hindex hSYL t ht hex
  have hc : ((YC d L).pCoreIn 2).conjBy t = (YL d L).pCoreIn 2 := by
    change ((YC d L).pCoreIn 2).map (MulAut.conj t).toMonoidHom = _
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective]
    exact congrArg (fun H : Subgroup G => H.pCoreIn 2) hback
  change ((YL d L).pCoreIn 2 ⊓ (YC d L).pCoreIn 2).map (MulAut.conj t).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj t).injective]
  change ((YL d L).pCoreIn 2).conjBy t ⊓ ((YC d L).pCoreIn 2).conjBy t = _
  rw [conjugate_YL_core d L t hex, hc, inf_comm]
  rfl

omit [Finite G] in
/-- Full displacement by Y_C puts Q in its intrinsic two-core. -/
theorem core_le_YC_core (d : LocalData G) (L : Subgroup G)
    (hSQ : commutatorCore L ≤ d.S)
    (hSC : d.S ≤ normalizer (YC d L : Set G))
    (hfull : ⁅commutatorCore L, YC d L⁆ = commutatorCore L) :
    commutatorCore L ≤ (YC d L).pCoreIn 2 := by
  have hCQ := (YC_section_action d L).1.trans (normalizer_le_normalizer_commutatorCore L)
  have h := le_pCoreIn_of_normalizes
    (((L.isPGroup_pCoreIn 2).to_le (commutatorCore_le L)).to_le
      (le_normalizer_iff_commutator_le_left.mp hCQ))
    (le_normalizer_iff_commutator_le_right.mp (hSQ.trans hSC))
    (normalizer_commutator_ge_right (commutatorCore L) (YC d L))
  rwa [hfull] at h

/-- Both residuals displace the common core onto Q in the moving case.
This avoids assuming that the intersection itself equals Q. -/
theorem commonCore_displacement (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hSC : d.S ≤ normalizer (YC d c.L : Set G))
    (hfix : YC d c.L ≤ centralizer (coreCenter c.L : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (hfullC : ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L) :
    ⁅commonCore d c.L, YL d c.L⁆ = commutatorCore c.L ∧
    ⁅commonCore d c.L, YC d c.L⁆ = commutatorCore c.L := by
  have hQK : commutatorCore c.L ≤ commonCore d c.L :=
    le_inf (core_le_YL_core d c.L hSQ hSYL hfullL) (core_le_YC_core d c.L hSQ hSC hfullC)
  have hKL : commonCore d c.L ≤ c.L := inf_le_left.trans
    (((YL d c.L).pCoreIn_le 2).trans ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right))
  have hKC : commonCore d c.L ≤ YC d c.L := inf_le_right.trans ((YC d c.L).pCoreIn_le 2)
  have hKO : commonCore d c.L ≤ c.L.pCoreIn 2 :=
    (le_inf hKL (hKC.trans hfix)).trans (natural_centralizer_le_core m)
  have hYL : YL d c.L ≤ c.L := (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  constructor
  · exact le_antisymm (commutator_mono hKO hYL)
      (hfullL.ge.trans (commutator_mono hQK le_rfl))
  · apply le_antisymm _ (hfullC.ge.trans (commutator_mono hQK le_rfl))
    rw [commutator_comm]
    exact (commutator_mono le_rfl hKL).trans (YC_commutator_le d c)

/-- Common-core displacement, rather than an unproved intersection equality,
forces Q to be invariant under the exchanging element. -/
theorem core_invariant_of_both_moving (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hfix : YC d c.L ≤ centralizer (coreCenter c.L : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (hfullC : ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    (commutatorCore c.L).conjBy t = commutatorCore c.L := by
  have hh := commonCore_displacement d c m hSQ hSYL
    (S_normalizes_YC d c.L hindex hSYL t ht hex) hfix hfullL hfullC
  calc
    (commutatorCore c.L).conjBy t = (⁅commonCore d c.L, YL d c.L⁆).conjBy t := congrArg (fun H : Subgroup G => H.conjBy t) hh.1.symm
    _ = ⁅(commonCore d c.L).conjBy t, (YL d c.L).conjBy t⁆ := map_commutator _ _ _
    _ = ⁅commonCore d c.L, YC d c.L⁆ := by rw [commonCore_conj_eq d c.L hindex hSYL t ht hex, hex]
    _ = commutatorCore c.L := hh.2

/-- The moving Y_C alternative is impossible by comparing the actual center
layer actions after constructing conjugation invariance of Q. -/
theorem not_both_moving (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    ⁅commutatorCore c.L, YC d c.L⁆ ≠ commutatorCore c.L := by
  intro hfullC
  have hfix := YC_fixes_center d c.L m hcore hR
    (S_normalizes_YC d c.L hindex hSYL t ht hex) hUZ hU hfixU
  exact core_not_conjugation_invariant d c.L m hU hfix t hex
    (core_invariant_of_both_moving d c m hindex (commutatorCore_le_S d c.L hcore hR)
      hSYL hfix hfullL hfullC t ht hex)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
end
