module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanStructure
public import Theory.Representation.BinaryConjugationSection.FixedCentralizerCommutator
/-!
# The original core commutator modulo its exact centralizer

The selected order-four square root has fixed space V/V₁. Since it lies
in the original Q and Q centralizes V, the whole Q has exactly that fixed
space. Apply the proved commutator duality to P = O₂(K): the annihilator of
V/V₁ is both [P/C_P(U),Q] and C_P(V)/C_P(U). The original natural centralizer
identity gives C_P(V) = P ∩ Q. The resulting equality retains C_P(U), and
is paired with the already proved index |P:P∩Q| = 4.

This is the original-group application of 14.7.16(3) and 14.7.20(4),
Aschbacher–Smith, printed pp.1048–1049, refs/quasithin.pdf. It assumes no
later Data. The remaining extraspecial alternatives and residual/component
classification through 14.7.52 remain open. Genuine earlier structural and
faithful-classification inputs retain their existing source producers.
-/
public noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The fixed space of the whole original Q is precisely V/V₁. -/
theorem extraspecial_core_fixed_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = s.imageSpace V := by
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  have hk := (extraspecial_critical_root_fixed_plane h hab structural previous he s c hs
    a b ha hane hb hba (hbo ▸ pow_orderOf_eq_one _)).1
  have hQV : Q T L ≤ centralizer (V : Set G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    rw [←h.centralizer_LT structural]
    exact inf_le_right
  apply le_antisymm
  · intro v hv
    rw [←hk]
    exact sub_eq_zero.mpr (hv ⟨b,hb⟩)
  · intro v hv q
    exact s.fixed_on_imageSpace_of_commutator_le (Q T L) V
      ((commutator_eq_bot_iff_le_centralizer.mpr hQV).le.trans bot_le) q q.property v hv

/-- Source 14.7.20(4), with the exact original centralizer kernel retained.
The equality expresses [P/C_P(U),Q]=(P∩Q)/C_P(U) as an equality of preimages. -/
theorem extraspecial_residual_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let P := (K F).pCoreIn 2
    ⁅P,Q T L⁆ ⊔ (P ⊓ centralizer (F.U : Set G)) = P ⊓ Q T L ∧
      (P ⊓ Q T L).relIndex P = 4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  let P := (K F).pCoreIn 2
  obtain ⟨X,aX,mX,ρ,sU,sP,_,_,hpair⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  have hfixed := extraspecial_core_fixed_seed h hab structural previous faithful ⟨e⟩ sU c hs
  have hh := BinaryConjugationSection.commutator_sup_kernel_eq_centralizer_of_dual_pairing
    sU sP hpair (Q T L) V (Q_le_H F) (le_conjugateSpanBy V F.H) hfixed
  have hPQ : P ≤ F.H.pCoreIn 2 := pCoreIn_mono_of_normalizes
    (map_subtype_le _) (le_normalizer_embedded_pResidual 2 F.H)
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hPLT : P ≤ L ⊔ (T : Subgroup G) := (hPQ.trans hQT).trans le_sup_right
  have hPC : P ⊓ Q T L = P ⊓ centralizer (V : Set G) := by
    change P ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [←h.centralizer_LT structural,←inf_assoc,inf_eq_left.mpr hPLT]
  exact ⟨hh.trans hPC.symm,extraspecial_residual_core_seed_index h hab structural previous hex hcard hexp⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
