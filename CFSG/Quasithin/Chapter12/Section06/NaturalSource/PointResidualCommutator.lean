module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidualMovement
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidualMovement
public import Theory.GroupTheory.PResidual.CommutatorImage
/-!
# Full commutator generation of the original point residual

The marked C_L(z) surjection has two-group kernel C_L(z) ∩ O₂(L).
Its actual Sylow subgroup is T ∩ L. Full movement of the four-block
residual lifts through this kernel using two-perfectness, proving
L₁=[L₁,T ∩ L] before passing to any star quotient.

This supplies the inner-action step of the normal-component analysis.
The intrinsic O₂(L₁) is never identified with L₁ ∩ O₂(L).
Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
-/
public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original Sylow intersection generates the whole point residual by commutators. -/
theorem SourceHypothesis.original_point_residual_full_commutator
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    ⁅(D.fullSetup hZ T z).L₁,(T : Subgroup G) ⊓ L⁆ = (D.fullSetup hZ T z).L₁ := by
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component (hTC.trans E.Gz.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let J := C ⊔ (T : Subgroup G)
  have hCJ : C ≤ J := le_sup_left
  let : (C.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le C.le_normalizer hnC)
  obtain ⟨P₀,hP₀⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (C.subgroupOf J)
  let e := subgroupOfEquivOfLe hCJ
  let P := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup C) = (T : Subgroup G).subgroupOf C := by
    change (P₀ : Subgroup (C.subgroupOf J)).map e.toMonoidHom = _
    rw [hP₀]
    ext c
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro ht
      exact ⟨⟨⟨c,hCJ c.property⟩,c.property⟩,ht,rfl⟩
  obtain ⟨_,f,hf,_,hk⟩ := S.original_point_stabilizer_map D hZ z hz hTz
  have hker : IsPGroup 2 f.ker := hk ▸ (isPGroup_pCoreIn 2 L).comap_subtype
  have hfull : pResidual 2 C = ⁅pResidual 2 C,(P : Subgroup C)⁆ := by
    apply eq_commutator_of_isPPerfect_of_map_eq _ _ (isPPerfect_pResidual 2)
      le_normalizer_of_normal f hker
    rw [map_pResidual_of_surjective 2 f hf]
    exact (BinaryPermutation.TerminalOrthogonal.FourBlockResidual.full_sylow_commutator
      (P.mapSurjective (f := f) hf)).symm
  have hm := congrArg (map C.subtype) hfull
  rw [map_commutator,hP,subgroupOf_map_subtype] at hm
  have hi : (T : Subgroup G) ⊓ C = (T : Subgroup G) ⊓ L := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hTC))
  rw [hi] at hm
  exact hm.symm
end CFSG.Quasithin.Chapter12.Section06
