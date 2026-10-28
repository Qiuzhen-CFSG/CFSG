module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.Representation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ShortImage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.Normalization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ShortCentralKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.KernelControl

/-!
# Marked action and non-shortness for the higher-field SL₃ branch

The complete adequate B.5 classifier on the literal plus representation
preserves both flag types, including every permitted natural, dual, repeated
and extension alternative. The actual Sylow intersection upgrades the
aligned model's containment marking to equality. Equivariance then proves
Tᵥ-normalization of both original flag preimages independently of local
membership.

A moving residual has affine plus image. LocalStructure supplies centrality
of its intrinsic-to-plus core comparison kernel, allowing odd central
kernel elements. Core-image surjectivity and C.1.7 irreducibility prove
non-shortness, without a nonzero triple-commutator assertion. The final
consumer selects this moving residual and retains its maximality, marked
intersection and literal plus-core PSL₂ equivalence.

The universal adequate B.5 and A.3.6 inputs and the earlier elementary,
reduced-family, Sylow and component-invariance hypotheses remain with
qt-13-06-centralizer-reduction and the existing source owners. The final
SL₃ exclusion remains with qt-13-06-higher-field-sl3-parabolics, which applies
the independent C.1.26 local-structure result to this non-short residual.
All original LinearThree and LocalStructure interfaces are preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.19, printed p.931, using the module setup on p.929.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The source kernel theorem gives non-shortness for either moving flag.
This uses its central comparison kernel, permitting odd central elements;
no assertion that the whole action kernel is a two-group remains. -/
theorem source_flag_residual_not_short [IsElementaryAbelian 2 (Uv z v)]
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (P : Subgroup G)
    (hflag : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
    (hmove : ¬ residualIn P ≤ centralizer ({z} : Set G)) :
    ¬ ChapterC.IsShort (residualIn P) := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = (2 : ℕ) ^ 2 by decide).le.trans
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hm)
  have hPK : P ≤ K := by
    rcases hflag with h | h
    · subst P
      exact preimageIn_le _ _ _
    · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp h
      subst P
      exact preimageIn_le _ _ _
  exact flag_residual_not_short_of_central_kernel hcard K L T z v hL hz
    (WK_le_Tv_of_ambient_core K L T z v hK.1.1 hU hSyl) hn e P hflag hPK hmove
    (LocalStructure.source_coreComparison_ker_le_center hG hA36 F hF hm
      K L T (residualIn P) z v hv hL hz ((map_subtype_le _).trans hPK) hK hW e)

/-- The complete marked-action output for the SL₃ branch of 13.6.19.
The same aligned model supplies an actual maximal flag preimage with a moving,
Tᵥ-invariant, non-short residual and its literal plus-core PSL₂ quotient.
Movement, flag preservation and non-shortness are all conclusions. The
universal B.5 and A.3.6 inputs and the earlier ambient source hypotheses retain
their original assembly owners; the final SL₃ exclusion is assembled separately. -/
theorem source_moving_normalized_nonshort_flag [IsElementaryAbelian 2 (Uv z v)]
    {𝒦 : GroupClass.{u}}
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
        Matrix.PSL3.LinearThree.unipotentSL F) :
    ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        Tv T v ≤ normalizer (P : Set G) ∧
        Tv T v ≤ normalizer (residualIn P : Set G) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
  have hnorm := flagPreimages_normalized K L T z v hL hz source
    (hG.involution_centralizer_sqtk hv) hK hn hU hSyl
    (LocalStructure.plus_twoCore_eq_bot_of_reduced K L T z v hL hz hW)
    hF hm e hmark
  obtain ⟨P, hflag, hPK, hmax, hinter, hmove, he⟩ :=
    moving_marked_flag_residual F hm hF K L T z v hL hz hK hn e hmark
  have hnP : Tv T v ≤ normalizer (P : Set G) := by
    rcases hflag with h | h
    · exact h ▸ hnorm.1
    · exact (Set.mem_singleton_iff.mp h) ▸ hnorm.2
  exact ⟨P, hflag, hPK, hmax, hinter, hnP, residualIn_normalized (Tv T v) P hnP,
    hmove, source_flag_residual_not_short K L T z v hL hz hG hA36 hF hm hv
      hK hn hU hSyl hW e P hflag hmove, he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
