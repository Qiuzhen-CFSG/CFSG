module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Transports
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.ResidualAction

/-!
# The marked residual automizer obstruction

An equality `L₁ = O²(H₁)` in the ambient subgroup lattice induces actual
group and quotient equivalences. These intertwine conjugation, transporting
the computed wreath automizer to the action of `H₁` on `L₁/O₂(L₁)`.
If `H₁ ≤ M`, that image embeds in the conventional `M` automizer, so an
`E₄` image for `M` contradicts the constructed `D₈` image for `H₁`.

This is the terminal conditional deduction in Aschbacher--Smith 13.8.16(1),
printed p.952 (PDF p.969). Its source assembly must construct `H₁`, its
wreath quotient, and the residual equality, and establish the `E₄` image
from the marked triple-cover case. None is discharged by this helper.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree
variable {G : Type*} [Group G]

/-- The embedded two-residual is normalized by its original overgroup. -/
theorem normalizes_embedded_residual (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype) :
    H₁ ≤ normalizer (L₁ : Set G) := by
  rw [hres]
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pResidual 2 H₁).le_normalizer_map H₁.subtype

/-- The residual marking identifies the actual subgroup carriers. -/
noncomputable def markedResidualEquiv (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype) : pResidual 2 H₁ ≃* L₁ :=
  ((pResidual 2 H₁).equivMapOfInjective H₁.subtype H₁.subtype_injective).trans
    (MulEquiv.subgroupCongr hres.symm)

/-- This identification preserves inclusion into the original ambient group. -/
theorem markedResidualEquiv_coe (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype) (r : pResidual 2 H₁) :
    (markedResidualEquiv L₁ H₁ hres r : G) = ((r : H₁) : G) := rfl

/-- The marking identifies quotients by their intrinsic two-cores. -/
noncomputable def markedQuotientEquiv (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype) :
    (pResidual 2 H₁ ⧸ pCore 2 (pResidual 2 H₁)) ≃* (L₁ ⧸ pCore 2 L₁) :=
  QuotientGroup.congr _ _ (markedResidualEquiv L₁ H₁ hres)
    (pCore_map_iso 2 (markedResidualEquiv L₁ H₁ hres))

/-- The quotient comparison is induced by the marked subgroup comparison. -/
theorem markedQuotientEquiv_mk (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype) (r : pResidual 2 H₁) :
    markedQuotientEquiv L₁ H₁ hres (QuotientGroup.mk' (pCore 2 (pResidual 2 H₁)) r) =
      QuotientGroup.mk' (pCore 2 L₁) (markedResidualEquiv L₁ H₁ hres r) := by rfl

/-- The marked quotient comparison preserves literal ambient conjugation. -/
theorem marked_intertwines (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (hn : H₁ ≤ normalizer (L₁ : Set G)) (h : H₁)
    (r : pResidual 2 H₁ ⧸ pCore 2 (pResidual 2 H₁)) :
    markedQuotientEquiv L₁ H₁ hres (ResidualAction.action h r) =
      quotientAction L₁ H₁ hn h (markedQuotientEquiv L₁ H₁ hres r) := by
  induction r using Quotient.inductionOn with
  | h r =>
    change markedQuotientEquiv L₁ H₁ hres
      (ResidualAction.action h (QuotientGroup.mk' (pCore 2 (pResidual 2 H₁)) r)) =
        quotientAction L₁ H₁ hn h (markedQuotientEquiv L₁ H₁ hres
          (QuotientGroup.mk' (pCore 2 (pResidual 2 H₁)) r))
    rw [show ResidualAction.action h (QuotientGroup.mk' (pCore 2 (pResidual 2 H₁)) r) =
      QuotientGroup.mk' (pCore 2 (pResidual 2 H₁)) (MulAut.conjNormal h r) from
        quotientAut_apply_mk _ _ _]
    rw [markedQuotientEquiv_mk, markedQuotientEquiv_mk, quotientAction_mk]
    apply congrArg (QuotientGroup.mk' (pCore 2 L₁))
    apply Subtype.ext
    rfl

variable [Finite G]

/-- A wreath quotient supplies the actual `D₈` action image on the marked section. -/
noncomputable def markedActionEquivDihedral (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (hn : H₁ ≤ normalizer (L₁ : Set G))
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) :
    (quotientAction L₁ H₁ hn).range ≃* D8 := by
  let c := MulAut.congr (markedQuotientEquiv L₁ H₁ hres)
  have hc : c.toMonoidHom.comp ResidualAction.action = quotientAction L₁ H₁ hn := by
    apply MonoidHom.ext
    intro h
    apply MulEquiv.ext
    intro r
    change markedQuotientEquiv L₁ H₁ hres
      (ResidualAction.action h ((markedQuotientEquiv L₁ H₁ hres).symm r)) = _
    rw [marked_intertwines L₁ H₁ hres hn, MulEquiv.apply_symm_apply]
  have hr : (ResidualAction.action (X := H₁)).range.map c.toMonoidHom =
      (quotientAction L₁ H₁ hn).range := by
    rw [← MonoidHom.range_comp, hc]
  exact ((c.subgroupMap (ResidualAction.action (X := H₁)).range).trans
    (MulEquiv.subgroupCongr hr)).symm.trans (ResidualAction.actionEquivDihedral e)

/-- The marked intrinsic quotient has order nine. -/
theorem markedQuotient_card (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) :
    Nat.card (L₁ ⧸ pCore 2 L₁) = 9 :=
  (Nat.card_congr (markedQuotientEquiv L₁ H₁ hres).symm.toEquiv).trans
    (ResidualAction.residualQuotient_card e)

/-- The source three-rank bound and wreath quotient force `m₃(L₁) = 2`. -/
theorem marked_threeRank (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) (hr : primeRank 3 H₁ ≤ 2) :
    primeRank 3 L₁ = 2 := by
  rw [← primeRank_congr 3 (markedResidualEquiv L₁ H₁ hres)]
  exact ResidualAction.residual_threeRank e hr

/-- An overgroup with the constructed wreath residual action cannot lie
inside an actor inducing `E₄` on the same marked section. -/
theorem no_wreath_residual_under_e4_automizer (L₁ H₁ M : Subgroup G)
    (hHM : H₁ ≤ M)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W)
    (hM : Nonempty ((automizerAction L₁ M).range ≃* E4)) : False := by
  have hn := normalizes_embedded_residual L₁ H₁ hres
  let ι : H₁ →* (M ⊓ normalizer (L₁ : Set G) : Subgroup G) :=
    inclusion (le_inf hHM hn)
  apply no_restricted_e4_dihedral_images (automizerAction L₁ M)
    (quotientAction L₁ H₁ hn) ι rfl hM
  exact ⟨markedActionEquivDihedral L₁ H₁ hres hn e⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree
end
