module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeRecognition
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeParabolic
/-!
# Exclusion of the natural SL₃ block in original 4.3.7

The source configuration supplies a parabolic-residual marking of its actual
L-image. Transporting both quotient and module by the same linear change of
basis allows the natural additive-subgroup calculation to identify [U(K),L]
with the original full module W. Crossing preserves W, so every crossed
actor fixes L modulo O₂(K). The full SL₃ automorphism-fixer theorem forces
its quotient action to be trivial, contradicting the crossed-layer obstruction.

These results discharge the SL₃ action and fixed-layer premises. The separate
C.4.1 classification must still supply the SL₃ block-type hypothesis; the
Sp₄ branch and final alternatives remain with qt-d-1222-rankone-uniqueness-block.
No identification of W with the separately chosen Chapter 12 module is used.
Source: Aschbacher–Smith C.4.7 and original 4.3.7, printed pp.153 and616.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private noncomputable def reframe
    {F : Type*} [Field F]
    {rho : SL(3,F) →* MulAut (Multiplicative (Fin 3 → F))}
    (m : BlockModuleModel L rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) : BlockModuleModel L rho where
  quotientIso := m.quotientIso.trans (Matrix.HigherLinear.SubspaceTransport.slConj e)
  moduleIso := m.moduleIso.trans e.toAddEquiv.toMultiplicative
  intertwining l u := by
    change e.toAddEquiv.toMultiplicative
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u))) = _
    rw [m.intertwining]
    apply Multiplicative.toAdd.injective
    change e ((rho (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l))
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) u))).toAdd) = _
    rw [hrho,hrho]
    have heM (v : Multiplicative (Fin 3 → F)) :
        (e.toAddEquiv.toMultiplicative v).toAdd = e v.toAdd := rfl
    simp only [MulEquiv.trans_apply, heM]
    symm
    simpa only [LinearEquiv.symm_apply_apply, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply] using
      Matrix.HigherLinear.SubspaceTransport.slConj_apply e
        (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l))
        (e (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd)

/-- The original full module is the commutator of the SL₃ block layer with
L. This discharges the fixed-layer inclusion without a parabolic premise. -/
theorem SourceConfiguration.block_commutator_eq_fullModule_of_linearThree
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hlinear : IsSL3EvenBlock c.K n) :
    ⁅c.blockLayer,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  obtain ⟨_,_,F,_,_,hF,rho,⟨m⟩,hrho⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [←Nat.card_eq_fintype_card,hF]
    simp [Nat.pow_mod,show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨e,he⟩ := c.block_linearThree_local_frame hn hf hb hF m.quotientIso
  exact c.block_commutator_eq_fullModule_of_sl3_parabolic hf (reframe m hrho e) hrho he

/-- The natural SL₃ block is impossible in the original crossing configuration.
The parabolic marking and full-module commutator identity are derived internally. -/
theorem SourceConfiguration.false_of_linearThree_block
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    {n : ℕ} (hn : 1 < n)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hlinear : IsSL3EvenBlock c.K n) : False := by
  obtain ⟨_,_,F,_,_,hF,rho,⟨m⟩,hrho⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [←Nat.card_eq_fintype_card,hF]
    simp [Nat.pow_mod,show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨e,he⟩ := c.block_linearThree_local_frame hn hf hb hF m.quotientIso
  exact c.false_of_sl3_parabolic D hf hb (by omega) hF (reframe m hrho e) hrho he
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
