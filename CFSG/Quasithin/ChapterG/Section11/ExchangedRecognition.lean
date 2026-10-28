module
public import CFSG.Quasithin.ChapterG.Section11.FullLinearFourModelForm
public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowMatrices
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# Recognition of all full-linear exchanged constituents in the low-rank case

Perfectness makes the original normal component orbit have full linear image.
The isotropic complementary pair makes that action faithful. The original
normal elementary Sylow actor supplies an outer involution; the checked
binary Sylow calculation forces dimension four. Thus every full-linear row
is the actual marked whole S₈ action, with its natural-plus-dual intertwiner.

A symmetric natural row is self-dual for the literal component-orbit action.
Homogeneous selection then excludes an isotropic exchanged pair, so its
restriction of the original alternating form is nondegenerate.

The arguments are generalized from the checked Chapter 14 larger-actor adapter
`ComponentCatalogueLargeActorDegreesExchanged`; no larger-actor or small-actor
premise is used here. These results feed `CorrectedReduction` and its literal
strict-quotient application. They do not assert exhaustive classification.
Source: Aschbacher--Smith G.10.15--16 and G.11.6, printed pp.363--366,
with the full-four correction in `docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
/-- Coordinates on the actual faithful constituent quotient. -/
private theorem linear_quotient_coordinates {D U : Type*} [Group D] [AddCommGroup U]
    [Module (ZMod 2) U] (σ : Representation (ZMod 2) D U) (n : ℕ)
    (hm : Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤ (Section06.binaryLinearAction n)) :
    ∃ (d : (D ⧸ σ.ker) ≃* BinaryLinear.OuterCyclic.LinearGroup n)
      (f : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n),
      ∀ (g : D) (u : U), f (σ g u) = d (QuotientGroup.mk' σ.ker g) (f u) := by
  obtain ⟨e,c,stable,hc⟩ := hm
  refine ⟨Subgroup.topEquiv.symm.trans e,
    (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) U) ≃ₗ[ZMod 2] U).symm.trans c, ?_⟩
  intro g u
  exact hc ⟨QuotientGroup.mk' σ.ker g,mem_top _⟩ ⟨u,Submodule.mem_top⟩

/-- Perfectness removes the abelian supplement from the full linear image. -/
private theorem full_linear_constituent
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H Y : Subgroup G) [H.Normal]
    [IsMulCommutative Y] (I : Submodule (ZMod 2) V)
    (hH : H ≤ subspaceStabilizer ρ I) (hY : Y ≤ subspaceStabilizer ρ I)
    (n : ℕ) (hn : 3 ≤ n)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H Y I hH hY)) ⊤ ⊤
      (Section06.binaryLinearAction n)) :
    finrank (ZMod 2) I = n ∧
      Function.Surjective (invariantSubspace ρ H I hH).toRepresentation.asGroupHom := by
  let P := H ⊔ Y
  let σ := Section09.constituentAction ρ H Y I hH hY
  obtain ⟨d,f,hf⟩ := linear_quotient_coordinates σ n hm
  have hd : finrank (ZMod 2) I = n := by simpa [BinaryLinear.OuterCyclic.Space] using f.finrank_eq
  have hs : Function.Surjective σ.asGroupHom := by
    intro a
    let t := (f.symm.trans (LinearMap.GeneralLinearGroup.toLinearEquiv a)).trans f
    obtain ⟨q,hq⟩ := d.surjective t
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective σ.ker q
    refine ⟨g,?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply f.injective
    change f (σ g u) = f (a.val u)
    rw [hf,hq]
    change f (a.val (f.symm (f u))) = f (a.val u)
    rw [f.symm_apply_apply]
  let E := (LinearMap.GeneralLinearGroup.congrLinearEquiv f).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _)
  let := BinaryNaturalDual.ModelOrbits.AutomorphismModel.linear_perfect hn
  let : Group.IsPerfect (LinearMap.GeneralLinearGroup (ZMod 2) I) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  let N := (H.subgroupOf P).map σ.asGroupHom
  let Z := (Y.subgroupOf P).map σ.asGroupHom
  let : N.Normal := Subgroup.Normal.map inferInstance σ.asGroupHom hs
  have hNZ : N ⊔ Z = ⊤ := by
    rw [← Subgroup.map_sup, (Subgroup.codisjoint_subgroupOf_sup H Y).eq_top,
      ← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr hs]
  have hN : N = ⊤ := by
    have hh := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNZ inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hh
    exact top_unique hh
  refine ⟨hd,?_⟩
  intro a
  obtain ⟨g,hg,he⟩ := hN.ge (mem_top a)
  exact ⟨⟨g.val,hg⟩,he⟩

private theorem natural_constituent_selfDual
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H Y : Subgroup G)
    (I : Submodule (ZMod 2) V)
    (hH : H ≤ subspaceStabilizer ρ I) (hY : Y ≤ subspaceStabilizer ρ I)
    (n : ℕ) (hn : 0 < n)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H Y I hH hY)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    Nonempty (Representation.Equiv (invariantSubspace ρ H I hH).toRepresentation
      (invariantSubspace ρ H I hH).toRepresentation.dual) := by
  let : NeZero n := ⟨by omega⟩
  let P := H ⊔ Y
  let σ := Section09.constituentAction ρ H Y I hH hY
  let R : Representation (ZMod 2) H I := (invariantSubspace ρ H I hH).toRepresentation
  obtain ⟨e,c,stable,hc⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let f := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) I) ≃ₗ[ZMod 2] I).symm.trans c
  let r : H →* Equiv.Perm (Fin n) := d.toMonoidHom.comp
    ((QuotientGroup.mk' σ.ker).comp (inclusion (show H ≤ P from le_sup_left)))
  have hf (a : H) (u : I) : f (R a u) =
      BinaryPermutation.naturalRepresentation (Fin n) (r a) (f u) :=
    hc ⟨QuotientGroup.mk' σ.ker (inclusion (show H ≤ P from le_sup_left) a),mem_top _⟩
      ⟨u,Submodule.mem_top⟩
  change Nonempty (Representation.Equiv R R.dual)
  refine ⟨.mk ((f.trans (BinaryPermutation.naturalDualEquiv (Fin n))).trans f.dualMap) ?_⟩
  intro a
  ext u w
  change BinaryPermutation.naturalDualEquiv (Fin n) (f (R a u)) (f w) =
    BinaryPermutation.naturalDualEquiv (Fin n) (f u) (f (R a⁻¹ w))
  rw [hf,BinaryPermutation.naturalDualEquiv_equivariant,hf]
  change BinaryPermutation.naturalDualEquiv (Fin n) (f u)
    (BinaryPermutation.naturalRepresentation (Fin n) ((r a)⁻¹) (f w)) = _
  rw [r.map_inv]


open Representation.BinaryOffender.FullLinearFourLift
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- An exchanged full-linear constituent for the original actor has degree
four, using its literal conjugation action on the component orbit. -/
theorem exchanged_full_linear_degree
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hnonsolv : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤)
      X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v
      W X I)
    (n : ℕ) (hn : 3 ≤ n)
    (hmodel : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I)
        I hI.invariant inf_le_right)) ⊤ ⊤ (Section06.binaryLinearAction n)) : n = 4 := by
  let H := componentOrbit L ⊤
  let Y := X ⊓ subspaceStabilizer ρ I
  let := componentOrbit_top_normal L
  let : IsMulCommutative Y := ⟨⟨fun a b => Subtype.ext
    (setLike_mul_comm (s := X) a.property.1 b.property.1)⟩⟩
  obtain ⟨hd,hs⟩ := full_linear_constituent ρ H Y I hI.invariant
    inf_le_right n hn hmodel
  obtain ⟨x,hx,hcompl,_⟩ := exchanged_lowRank_pair h cover
    hw hS hnonsolv hL hm hI hgeo
  have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : G) x.property)
  have hi := h.irreducible_of_not_solvable hnonsolv
  have hiI := hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H
  have hiso := isotropic_of_full_constituent ρ B h.alternating
    h.preserves H I hI.invariant (by omega) hs
  have hfI := faithful_isotropic_pair ρ h.faithful B h.nondegenerate
    h.preserves H I hI.invariant hiI hiso (x : G)
    (by simpa only [hxinv] using hcompl.sup_eq_top)
  let e := MulEquiv.ofBijective
    (invariantSubspace ρ H I hI.invariant).toRepresentation.asGroupHom ⟨hfI,hs⟩
  have hHne : H ≠ ⊥ := hL.componentOrbit_top_ne_bot
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ
    h.faithful hi H hHne
  have ho := hI.conjugation_not_inner ρ hfix x (by simpa only [hxinv] using hx)
  obtain ⟨S,_,hXS,hSX⟩ := hS
  let a := ElementaryOuterSylowAction.of_normal_elementary H S X hXS
    ((normal_subgroupOf_iff_le_normalizer hXS).mp hSX) x ho
  exact hd.symm.trans (BinaryLinear.ElementaryOuterSylow.finrank_eq_four a e (by omega))

/-- A natural symmetric constituent in the exchanged branch is nondegenerate
for the original form. Its natural self-duality excludes the isotropic pair. -/
theorem exchanged_natural_nondegenerate
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hnonsolv : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤)
      X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v
      W X I)
    (n : ℕ) (hn : 0 < n)
    (hmodel : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) : (B.restrict I).Nondegenerate := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hnonsolv
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ
    h.faithful hi H hL.componentOrbit_top_ne_bot
  rcases hI.isIrrPlus.isotropic_or_nondegenerate_of_normal_restriction ρ hi H B
    h.alternating h.preserves with hiso | hnd
  · obtain ⟨x,hx,hcompl,_⟩ := exchanged_lowRank_pair h cover
      hw hS hnonsolv hL hm hI hgeo
    have hxinv (y : X) : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (y : G) y.property)
    have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
      apply top_unique
      rw [← hcompl.sup_eq_top]
      exact sup_le (Homogeneous.le_orbitSpan ρ X I) (le_iSup (fun y : X => I.map (ρ y)) x)
    have hdim := hI.isIrrPlus.finrank_gt_two ρ H
    have hpair (y : X) (hy : I.map (ρ (y : G)⁻¹) ≠ I) :
        I ⊔ I.map (ρ (y : G)⁻¹) = ⊤ := by
      rw [hxinv] at hy ⊢
      exact (h.independent_orbit_pair I (by omega)
        (hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix) y hy).1.symm.trans hgen
    have hd := (hI.faithful_dual_of_isotropic_pair ρ h.faithful B
      h.nondegenerate h.preserves hfix
      (hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H) hiso
      ⟨x,by simpa only [hxinv] using hx⟩ hpair).2.1
    exact (hd (natural_constituent_selfDual ρ H
      (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right n hn hmodel)).elim
  · exact hnd

/-- Every exchanged full-linear row for the original actor is the marked
whole S₈ action in degree eight. This is recognition, not an ambient exclusion. -/
theorem exchanged_full_linear_alternative
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hnonsolv : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤)
      X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v
      W X I)
    (n : ℕ) (hn : 3 ≤ n)
    (hmodel : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I)
        I hI.invariant inf_le_right)) ⊤ ⊤ (Section06.binaryLinearAction n)) :
    finrank (ZMod 2) V = 8 ∧
      Nonempty (G ≃* Equiv.Perm (Fin 8)) ∧
      FullLinearFour.MarkedAlternative ρ B v W
        X
        X₀ := by
  have hn4 := exchanged_full_linear_degree h cover hw hS hnonsolv hL hm hI hgeo n hn hmodel
  subst n
  obtain ⟨x,⟨m⟩⟩ := FullLinearFour.exchanged_full_four_model h
    cover hw hS hnonsolv hL hm hI hgeo hmodel
  refine ⟨?_,⟨m.symmetricEquiv⟩,FullLinearFour.exchanged_full_four_marked_alternative
    h cover hw hS hnonsolv
    hL hm hI hgeo hmodel⟩
  simpa [BinaryNaturalDual.CoordinateSpace,BinaryNaturalDual.Space,BinaryLinear.OuterCyclic.Space]
    using m.spaceEquiv.finrank_eq

end CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
