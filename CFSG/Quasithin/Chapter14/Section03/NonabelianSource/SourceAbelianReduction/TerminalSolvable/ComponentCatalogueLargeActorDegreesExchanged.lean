module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesLowRank
public import CFSG.Quasithin.ChapterG.Section11.FullLinearFourModelForm
public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowMatrices
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# Refined exchanged alternatives for the original larger actor

A full binary linear constituent is isotropic. Its complementary conjugate
makes the component-orbit action faithful, and the original normal elementary
Sylow actor induces an outer automorphism. The checked binary Sylow calculation
therefore forces constituent degree four, excluding GL₃(2) and GL₅(2).
The full-four reconstruction preserves the actual dotted group, actor, point
and form and gives the marked eight-dimensional S₈ action.

A natural symmetric constituent is self-dual for the literal component-orbit
action. Homogeneous selection forbids self-duality of an isotropic exchanged
pair, so every remaining natural constituent is nondegenerate. Its actual
coordinates force whole-module degree eight or twelve. The numerical and
component consumers retain only these rows, the exceptional marked S₈ action,
and the independent whole-component branch. Their recognition or ambient
exclusion, and hence the unconditional degree alternatives, remain open.

Source: Aschbacher--Smith G.10.15--16 and G.11.6--7, printed pp.363--367;
14.3.13--14, printed pp.993--994. The full-four source correction in
`docs/quasithin-proof-basis.md` is retained: no exclusion of this action is
claimed from the insufficient local hypotheses.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
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

/-- The exchanged remainder retains only nondegenerate natural symmetric
constituents, with the same original action and quotient map. -/
@[expose] def WholeOrNondegenerateNaturalModels
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (B : LinearMap.BilinForm (ZMod 2) U)
    (v : U) (W : Submodule (ZMod 2) U) (X : Subgroup D)
    [IsElementaryAbelian 2 X] : Prop :=
  ∃ L : Subgroup D, IsComponent D L ∧ ⁅L,X⁆ ≠ ⊥ ∧
    Section10.ComponentOrthogonalData ρ B L ∧
    (Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive X)) ∨
      ∃ I : Submodule (ZMod 2) U,
        ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
          v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I ∧
          (∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x))) ∧
          finrank (ZMod 2) U = 2 * finrank (ZMod 2) I ∧
          (finrank (ZMod 2) U = 8 ∨ finrank (ZMod 2) U = 12) ∧
          (B.restrict I).Nondegenerate ∧
          ∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Section06.HasModelOn
            (kerRepresentation (Section09.constituentAction ρ (componentOrbit L ⊤)
              (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
            (BinaryPermutation.naturalRepresentation (Fin n)))

end CFSG.Quasithin.ChapterG.Section11
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11 Representation.BinaryOffender.FullLinearFourLift
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- An exchanged full-linear constituent for the original actor has degree
four, using its literal conjugation action on the component orbit. -/
theorem exchanged_full_linear_degree
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (n : ℕ) (hn : 3 ≤ n)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤ (ChapterG.Section06.binaryLinearAction n)) : n = 4 := by
  let ρ := F.terminalRepresentation
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let Y := X ⊓ subspaceStabilizer ρ I
  let := componentOrbit_top_normal L
  let : IsMulCommutative Y := ⟨⟨fun a b => Subtype.ext
    (setLike_mul_comm (s := X) a.property.1 b.property.1)⟩⟩
  obtain ⟨hd,hs⟩ := ChapterG.Section11.full_linear_constituent ρ H Y I hI.invariant
    inf_le_right n hn hmodel
  obtain ⟨x,hx,hcompl,_⟩ := exchanged_lowRank_pair s.hypothesis s.classification_input.1
    s.low_rank_witness s.normal_sylow s.nonsolvable hL hm hI hgeo
  have hxinv : (x : F.TerminalHdot)⁻¹ = x := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : F.TerminalHdot) x.property)
  have hi := s.hypothesis.irreducible_of_not_solvable s.nonsolvable
  have hiI := hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H
  have hiso := isotropic_of_full_constituent ρ B s.hypothesis.alternating
    s.hypothesis.preserves H I hI.invariant (by omega) hs
  have hfI := faithful_isotropic_pair ρ s.hypothesis.faithful B s.hypothesis.nondegenerate
    s.hypothesis.preserves H I hI.invariant hiI hiso (x : F.TerminalHdot)
    (by simpa only [hxinv] using hcompl.sup_eq_top)
  let e := MulEquiv.ofBijective
    (invariantSubspace ρ H I hI.invariant).toRepresentation.asGroupHom ⟨hfI,hs⟩
  have hHne : H ≠ ⊥ := hL.componentOrbit_top_ne_bot
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ
    s.hypothesis.faithful hi H hHne
  have ho := hI.conjugation_not_inner ρ hfix x (by simpa only [hxinv] using hx)
  obtain ⟨S,_,hXS,hSX⟩ := s.normal_sylow
  let a := ElementaryOuterSylowAction.of_normal_elementary H S X hXS
    ((normal_subgroupOf_iff_le_normalizer hXS).mp hSX) x ho
  exact hd.symm.trans (BinaryLinear.ElementaryOuterSylow.finrank_eq_four a e (by omega))

/-- A natural symmetric constituent in the exchanged branch is nondegenerate
for the original form. Its natural self-duality excludes the isotropic pair. -/
theorem exchanged_natural_nondegenerate
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (n : ℕ) (hn : 0 < n)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) : (B.restrict I).Nondegenerate := by
  let ρ := F.terminalRepresentation
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := s.hypothesis.irreducible_of_not_solvable s.nonsolvable
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ
    s.hypothesis.faithful hi H hL.componentOrbit_top_ne_bot
  rcases hI.isIrrPlus.isotropic_or_nondegenerate_of_normal_restriction ρ hi H B
    s.hypothesis.alternating s.hypothesis.preserves with hiso | hnd
  · obtain ⟨x,hx,hcompl,_⟩ := exchanged_lowRank_pair s.hypothesis s.classification_input.1
      s.low_rank_witness s.normal_sylow s.nonsolvable hL hm hI hgeo
    have hxinv (y : X) : (y : F.TerminalHdot)⁻¹ = y := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (y : F.TerminalHdot) y.property)
    have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
      apply top_unique
      rw [← hcompl.sup_eq_top]
      exact sup_le (Homogeneous.le_orbitSpan ρ X I) (le_iSup (fun y : X => I.map (ρ y)) x)
    have hdim := hI.isIrrPlus.finrank_gt_two ρ H
    have hpair (y : X) (hy : I.map (ρ (y : F.TerminalHdot)⁻¹) ≠ I) :
        I ⊔ I.map (ρ (y : F.TerminalHdot)⁻¹) = ⊤ := by
      rw [hxinv] at hy ⊢
      exact (s.hypothesis.independent_orbit_pair I (by omega)
        (hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix) y hy).1.symm.trans hgen
    have hd := (hI.faithful_dual_of_isotropic_pair ρ s.hypothesis.faithful B
      s.hypothesis.nondegenerate s.hypothesis.preserves hfix
      (hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H) hiso
      ⟨x,by simpa only [hxinv] using hx⟩ hpair).2.1
    exact (hd (ChapterG.Section11.natural_constituent_selfDual ρ H
      (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right n hn hmodel)).elim
  · exact hnd

/-- Every exchanged full-linear row for the original actor is the marked
whole S₈ action in degree eight. This is recognition, not an ambient exclusion. -/
theorem exchanged_full_linear_alternative
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (n : ℕ) (hn : 3 ≤ n)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤ (ChapterG.Section06.binaryLinearAction n)) :
    finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
      Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
      FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
        (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := by
  have hn4 := s.exchanged_full_linear_degree hL hm hI hgeo n hn hmodel
  subst n
  obtain ⟨x,⟨m⟩⟩ := FullLinearFour.exchanged_full_four_model s.hypothesis
    s.classification_input.1 s.low_rank_witness s.normal_sylow s.nonsolvable hL hm hI hgeo hmodel
  refine ⟨?_,⟨m.symmetricEquiv⟩,FullLinearFour.exchanged_full_four_marked_alternative
    s.hypothesis s.classification_input.1 s.low_rank_witness s.normal_sylow s.nonsolvable
    hL hm hI hgeo hmodel⟩
  simpa [BinaryNaturalDual.CoordinateSpace,BinaryNaturalDual.Space,BinaryLinear.OuterCyclic.Space]
    using m.spaceEquiv.finrank_eq

/-- The original degree problem now retains the whole-component branch,
the marked full-four action, and only nondegenerate natural exchanged rows.
The full G₂(2) equivalence in the successful degree-six branch is unchanged. -/
theorem degree_cases_or_full_four_or_natural :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        WholeOrNondegenerateNaturalModels F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_remaining_models with hd | ⟨hd,L,hL,hm,horth,hwhole | hex⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inr ⟨hd,L,hL,hm,horth,Or.inl hwhole⟩)
  · obtain ⟨I,hI,hv,hgeo,hcompl,hdim,_,hmodels⟩ := hex
    rcases hmodels with ⟨n,hn,_,hmodel⟩ | ⟨n,hn,hnu,hmodel⟩
    · exact Or.inr (Or.inl (s.exchanged_full_linear_alternative hL hm hI hgeo n hn hmodel))
    · have hnd := s.exchanged_natural_nondegenerate hL hm hI hgeo n (by omega) hmodel
      have hdimI : finrank (ZMod 2) I = 4 ∨ finrank (ZMod 2) I = 6 := by
        obtain ⟨e,c,stable,hc⟩ := hmodel
        have he := c.finrank_eq
        rw [finrank_top] at he
        have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
        rcases hn' with rfl | rfl | rfl | rfl
        all_goals simp only [BinaryPermutation.finrank_natural_even (Fin 6) (by decide),
          BinaryPermutation.finrank_natural_even (Fin 8) (by decide),
          BinaryPermutation.finrank_natural_odd (Fin 5) (by decide),
          BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] at he
        all_goals omega
      exact Or.inr (Or.inr ⟨hd,L,hL,hm,horth,Or.inr
        ⟨I,hI,hv,hgeo,hcompl,hdim,by omega,hnd,n,hn,hnu,hmodel⟩⟩)

/-- Apply the refined action alternatives to the literal component consumer. -/
theorem component_or_full_four_or_natural
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        WholeOrNondegenerateNaturalModels F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_full_four_or_natural with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
