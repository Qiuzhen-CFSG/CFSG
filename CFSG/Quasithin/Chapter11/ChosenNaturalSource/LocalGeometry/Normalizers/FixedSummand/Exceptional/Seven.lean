module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Component
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Alternating.Aut

/-!
# The seven-residual on the first rank-one quotient

The exceptional parameters force q=4. The literal quotient L₁/O₂(L₁)
is then PSL₂(4), whose automorphism group has order 120 via A₅. Hence
O^{7′}(Y) acts trivially on that quotient, and its commutators with L₁
lie in the original O₂(L₁). This supplies the quotient-action input for
the two natural chief sections in the SL₃ branch.

The rank-one quotient and fixed-line hypotheses are preceding flag inputs
owned by qt-d-1222-natural-flag-cartan; the normalizer-source parent
discharges them. The remaining chief-section calculation and final
Goldschmidt–O’Nan assembly stay with qt-d-1222-natural-point-fixed-summand.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem automorphism_card_of_psl_four
    {A : Type*} [Group A] (hm : ClassicalGroup.IsPSL A 2 4) :
    Nat.card (MulAut A) = 120 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨j⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let a := e.trans j
  let b : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  rw [Nat.card_congr (MulAut.congr a).toEquiv, Nat.card_congr b.symm.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

/-- The first quotient in the exceptional branch is the original PSL₂(4),
whose automorphism group has order 120. -/
theorem exceptional_first_automorphism_card
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    Nat.card (MulAut (f.Li 0 ⧸ pCore 2 (f.Li 0))) = 120 := by
  have hn := (chosen_exceptional_parameters D S f X hcenter hfixed he).1
  apply automorphism_card_of_psl_four
  simpa only [hn, Nat.reducePow] using hm

/-- The seven-residual acts trivially on the literal first two-core quotient. -/
theorem exceptional_sevenResidual_le_first_quotient_kernel
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
      (normalizer (f.Ri 0 : Set G)).subtype ≤
      (coreQuotientAction (f.Li 0)).ker.map (normalizer (f.Li 0 : Set G)).subtype := by
  have hn := chosen_exceptional_normalizes_first D S f hm hfix X hcenter hfixed he
  let a := (coreQuotientAction (f.Li 0)).comp (inclusion hn)
  have hk : primeToResidual 7 (normalizer (f.Ri 0 : Set G)) ≤ a.ker :=
    primeToResidual_le_ker a (by
      rw [exceptional_first_automorphism_card D S f hm X hcenter hfixed he]
      decide)
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨inclusion hn y, hk hy, rfl⟩

/-- On the actual local radical, every seven-residual commutator with L₁
lies in O₂(L₁). This is the first action reduction for its chief sections. -/
theorem exceptional_sevenResidual_commutator_le_first_core
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    ⁅(primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
      (normalizer (f.Ri 0 : Set G)).subtype, f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2 := by
  apply commutator_le.mpr
  intro y hy l hl
  obtain ⟨a, ha, rfl⟩ :=
    exceptional_sevenResidual_le_first_quotient_kernel D S f hm hfix X hcenter hfixed he hy
  let l' : f.Li 0 := ⟨l, hl⟩
  let r := (f.Li 0).normalizerMonoidHom a l' * l'⁻¹
  have hr : r ∈ pCore 2 (f.Li 0) := by
    apply (QuotientGroup.eq_one_iff _).mp
    have h := DFunLike.congr_fun (show coreQuotientAction (f.Li 0) a = 1 from ha)
      (QuotientGroup.mk' (pCore 2 (f.Li 0)) l')
    change quotientAut (pCore 2 (f.Li 0)) ((f.Li 0).normalizerMonoidHom a)
      (QuotientGroup.mk' (pCore 2 (f.Li 0)) l') = _ at h
    rw [quotientAut_apply_mk] at h
    change QuotientGroup.mk' (pCore 2 (f.Li 0)) r = 1
    dsimp only [r]
    rw [map_mul, map_inv, h]
    exact mul_inv_cancel _
  exact mem_map_of_mem (f.Li 0).subtype hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
