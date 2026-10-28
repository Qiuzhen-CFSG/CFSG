module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerEscape
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerLocalG2

/-!
# The invariant local residual in the original binary G₂ Weyl row

The literal quotient marking identifies O²(C_L(Ω₁Z(T))) with the ambient
prime-to-three residual. Hence N_G(T) preserves this subgroup and the
two-core of its join with T. The original fixed-involution setup also makes
C_G(Ω₁Z(T)) normalize every N_G(T)-conjugate of the chosen module.
Consequently all these conjugates lie in that same local two-core.

The final application supplies the actual odd escaping conjugator and both
local-core containments for the source factorization argument. No intrinsic
short-block reconstruction or NoEscape premise is used.
Source: Aschbacher--Smith 3.3.25(2), 3.3.28, pp.599--601; 12.4.3, p.813.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The original quotient marking suffices for invariance of X=O²(C_L(Z))
and R=O₂(XT); a reconstructed block is not needed. -/
theorem normalizer_preserves_local_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    normalizer (T : Set G) ≤ normalizer (omegaLocalResidual T L : Set G) ∧
      normalizer (T : Set G) ≤ normalizer (omegaResidualCore T L : Set G) := by
  have he := g2Two_omega_cubic_residual_eq_local h D hne e.groupEquiv
  rw [← omega_local_residuals_eq_of_g2Two D e.groupEquiv] at he
  exact ⟨sylow_normalizer_normalizes_omegaLocalResidual he,
    sylow_normalizer_normalizes_omegaResidualCore he⟩

omit [Finite G] in
/-- The original core lies in the local residual core, which lies in T. -/
theorem local_core_containments :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ omegaResidualCore T L ∧
      omegaResidualCore T L ≤ (T : Subgroup G) := by
  let X := omegaLocalResidual T L
  let H := L ⊔ (T : Subgroup G)
  have hXL : X ≤ L := (map_subtype_le _).trans inf_le_left
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [H, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow H (T.subtype le_sup_right)
  refine ⟨le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    (hQT.trans le_sup_right) ?_, ?_⟩
  · exact (sup_le (hXL.trans le_sup_left) le_sup_right).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  · change (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- Every conjugate of the literal chosen V by N_G(T) lies in the source
local core R. This supplies the placement used in the G₂ factorization. -/
theorem conjugate_chosen_le_local_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G)) :
    V.map (MulAut.conj d).toMonoidHom ≤ omegaResidualCore T L := by
  let E := omegaCenterIn (T : Subgroup G)
  let C := centralizer (E : Set G)
  let X := omegaLocalResidual T L
  let f := (MulAut.conj d).toMonoidHom
  obtain ⟨_, _, _, _, hNV, _, _⟩ := exists_fixed_involution_setup h D structural e hne
  have hCN : C ≤ normalizer (V : Set G) := (omega_centralizer_le h D hne).trans hNV.le
  have hCd : C.map f = C := mem_normalizer_iff_map_conj_eq.mp
    (sylow_normalizer_normalizes_omega_centralizer hd)
  have hCVd : C ≤ normalizer (V.map f : Set G) := by
    have hh := (map_mono (f := f) hCN).trans (V.le_normalizer_map f)
    rwa [hCd] at hh
  have hTd : (T : Subgroup G).map f = T := mem_normalizer_iff_map_conj_eq.mp hd
  have hVdT : V.map f ≤ (T : Subgroup G) := (map_mono D.le_sylow).trans hTd.le
  have hTVd : (T : Subgroup G) ≤ normalizer (V.map f : Set G) := by
    have hh := (map_mono (f := f) ((structural L h).2.2 V D).1).trans
      (V.le_normalizer_map f)
    rwa [hTd] at hh
  have hXC : X ≤ C := (map_subtype_le _).trans inf_le_right
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hVdT)
    (hVdT.trans le_sup_right) (sup_le (hXC.trans hCVd) hTVd)

/-- The actual odd escaping configuration inside the invariant source core.
The remaining factorization and elementary-lift arguments use these exact
subgroups; no conjugate module has been replaced by an abstract model. -/
theorem exists_odd_escape_in_local_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    let R := omegaResidualCore T L
    normalizer (T : Set G) ≤ normalizer (R : Set G) ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R ∧ R ≤ (T : Subgroup G) ∧
      ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
        ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
          V.map (MulAut.conj d).toMonoidHom ≤ R ∧
          V.map (MulAut.conj d).toMonoidHom ≠ V ∧
          omegaCenterIn (T : Subgroup G) ≤ V ⊓ V.map (MulAut.conj d).toMonoidHom := by
  obtain ⟨A, hAN, ho, _, d, hd, hout, _, _, _, hEV, hmove⟩ :=
    exists_odd_escape_geometry h D structural e hne hescape
  exact ⟨(normalizer_preserves_local_residual h D e hne).2,
    local_core_containments.1, local_core_containments.2, A, hAN, ho, d, hd, hout,
    conjugate_chosen_le_local_core h D structural e hne (hAN hd), hmove, hEV⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
