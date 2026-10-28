module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.TerminalGeometry
public import Theory.Representation.PSL3Two.NaturalDualBounds
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The component action supplies the original terminal bounds

For H=Mc, set V=localModule T M, Z=centralInvolutions T,
U=conjugateSpanBy V Mc and Q=Mc.pCoreIn 2. The single component L=H∞
normalizes its natural support A. Its actual quotient L/O₂(L) is SL₃(2),
and the same full action f on N=Mc∩N_G(A) marks both A/Z and B/Z.

The component image in Mc/O₂(Mc) lies in the generalized Fitting subgroup.
Residual functoriality proves that f restricted to L is surjective. The
natural action and [U,Q]≤Z then put Q∩L in its kernel, giving |T:Q|≥8.
A Singer lift in L centralizes X=C_G(Q)∩U, since X≤Ω₁Z(Q). The natural/dual
pair count gives |A∨B:X∩(A∨B)|≥64 and hence the required logarithmic bound.
The final application supplies both numerical premises of
`source_terminal_witness_of_geometry` for the same suitable u, P and R.

These are conditional applications of the preceding source inputs. The
normalization, full action, literal sections, support containment and
separation come from 14.6.22--23; the single-component equality and actual
SL₃(2) quotient come from 14.6.24(2--3). Their construction, and the residual
coordinates and crossing geometry, remain with the earlier source arguments.

Source: Aschbacher--Smith, 14.6.20--24, printed pp.1037--1042, especially
the two numerical hypotheses in the final argument on printed p.1042.
-/

public section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hunique hmany hcard e in
/-- Placement and full image of the actual single component. The component
normalizes its natural support; its equality with the embedded solvable residual
makes it T-invariant and forces its image under the full support action to be
all of SL₃(2). -/
theorem source_component_action_placement
    (L A : Subgroup G)
    (hres : (solvableResidual Mc).map Mc.subtype = L)
    (hc : (L.subgroupOf Mc).IsCComponent)
    (eL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hLA : L ≤ normalizer (A : Set G))
    (f : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* Matrix.PSL3Two.SL)
    (hf : Function.Surjective f) :
    ∃ hLN : L ≤ Mc ⊓ normalizer (A : Set G),
      (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      L ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc ∧
      Function.Surjective (f.comp (inclusion hLN)) := by
  have hLH : L ≤ Mc := hres ▸ map_subtype_le _
  have hLN : L ≤ Mc ⊓ normalizer (A : Set G) := le_inf hLH hLA
  have hHL : Mc ≤ normalizer (L : Set G) := by
    rw [← hres]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (solvableResidual Mc).le_normalizer_map Mc.subtype
  have hTL :=
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e).1.2.trans hHL
  let j := subgroupOfEquivOfLe hLH
  let eqL := (QuotientGroup.congr (pCore 2 (L.subgroupOf Mc)) (pCore 2 L)
    j (pCore_map_iso 2 j)).trans eL
  let := hc.perfect
  let : Group.IsPerfect Matrix.PSL3Two.SL := Group.IsPerfect.ofSurjective
    (f := eqL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (L.subgroupOf Mc))))
    (eqL.surjective.comp (QuotientGroup.mk'_surjective _))
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  let : IsQuasisimple Matrix.PSL3Two.SL := ⟨
    ((QuotientGroup.quotientMulEquivOfEq Matrix.PSL3Two.center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let C := (L.subgroupOf Mc).map q
  let ec := (cComponentTwoCoreQuotientEquiv hc).symm.trans eqL
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv ec.symm
  let := pCore_isNilpotent (p := 2) (G := Mc)
  have hC : IsComponent (Mc ⧸ pCore 2 Mc) C :=
    ⟨(hc.map_quotient (pCore 2 Mc)).subnormal, inferInstance⟩
  have hLF : L ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc := by
    rw [← map_subgroupOf_eq_of_le hLH]
    exact map_mono (map_le_iff_le_comap.mp (component_le_generalizedFitting _ _ hC))
  refine ⟨hLN, hTL, hLF, ?_⟩
  intro y
  have hy : y ∈ (solvableResidual (Mc ⊓ normalizer (A : Set G) : Subgroup G)).map f := by
    rw [map_solvableResidual_eq f hf, solvableResidual_eq_top]
    trivial
  obtain ⟨x, hx, hxy⟩ := hy
  have hxL : (x : G) ∈ L := by
    rw [← hres]
    exact map_solvableResidual_mono inf_le_left (mem_map_of_mem _ hx)
  exact ⟨⟨x, hxL⟩, hxy⟩

include hG hempty hM hunique hmany hcard e hab in
/-- The literal component action gives both numerical hypotheses of 14.6.9.
The quotient map, its full natural/dual action, and the component's placement
are the explicit 14.6.20--22 data; neither numerical bound is a premise. -/
theorem source_terminal_bounds_of_natural_dual
    (N L A B : Subgroup G) (hLN : L ≤ N)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLF : L ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (f : N →* Matrix.PSL3Two.SL)
    (hf : Function.Surjective (f.comp (inclusion hLN)))
    (a : BinaryConjugationSection N A (centralInvolutions T)
      ((specialLinearNatural 3).comp f))
    (b : BinaryConjugationSection N B (centralInvolutions T) (fullDual.comp f))
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : A ⊓ B ≤ centralInvolutions T) :
    4 < (Mc.pCoreIn 2).relIndex (T : Subgroup G) ∧
      4 ≤ Nat.log 2 ((centralizer (Mc.pCoreIn 2 : Set G)).relIndex
        (conjugateSpanBy (localModule T M) Mc)) := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Q := Mc.pCoreIn 2
  let X := centralizer (Q : Set G) ⊓ U
  let : IsElementaryAbelian 2 U := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hker : Q.subgroupOf L ≤ (f.comp (inclusion hLN)).ker := by
    intro x hx
    change f (inclusion hLN x) = 1
    apply specialLinearNatural_injective 3
    rw [map_one]
    apply LinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := a.onto (Multiplicative.ofAdd v)
    have hcomm : ⁅(w : G), (x : G)⁆ ∈ centralInvolutions T :=
      h.commutator_UH_QH_le_point (commutator_mem_commutator (hAU w.property) hx)
    have he := (a.fixed_coordinate_iff_commutator_mem (inclusion hLN x) w).mpr hcomm
    change specialLinearNatural 3 (f (inclusion hLN x)) (a.coordinates w).toAdd =
      (a.coordinates w).toAdd at he
    rw [hw] at he
    exact he
  have hindex := core_index_bound T Q L hTL (f.comp (inclusion hLN)) hf hker
  refine ⟨?_, ?_⟩
  · exact (by decide : 4 < 8).trans_le hindex
  obtain ⟨k, hk⟩ := hf naturalDualSinger
  have hout := ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e
  have hcent := hLF.trans (source_generalizedFittingPreimage_centralizes_omegaCore
    hG T hempty hout h.H_centralizes)
  have hX : (inclusion hLN k : G) ∈ centralizer (X : Set G) := by
    intro x hx
    apply hcent k.property x
    exact (mem_omegaOneCenterAmbient_iff Q x).mpr
      ⟨h.UH_le_QH hx.2, elemPow_eq_one_of_isElementaryAbelian x hx.2, hx.1⟩
  have hbn : B ≤ normalizer (A : Set G) :=
    hBU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans
      ((centralizer_le hAU).trans (Subgroup.centralizer_le_normalizer _)))
  have h64 := pair_index_bound f a b hsep hbn (inclusion hLN k) hk hX h.point_card
  have hle : X.relIndex (A ⊔ B) ≤ X.relIndex U :=
    relIndex_le_of_le_right (sup_le hAU hBU) Subgroup.index_ne_zero_of_finite
  have h64' : 64 ≤ (centralizer (Q : Set G)).relIndex U := by
    simpa only [X, inf_relIndex_right] using h64.trans hle
  apply Nat.le_log_of_pow_le (by decide : 1 < 2)
  exact (by decide : 2 ^ 4 ≤ 64).trans h64'

/-- Supply the two numerical premises of the original terminal witness using
the same full support action and the same suitable u, P and R. The earlier
source owners still supply the natural/dual sections, the single-component
identification, the residual coordinates and the crossing geometry. -/
theorem source_terminal_witness_of_natural_dual
    (L A B : Subgroup G)
    (hres : (solvableResidual Mc).map Mc.subtype = L)
    (hc : (L.subgroupOf Mc).IsCComponent)
    (eL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hLA : L ≤ normalizer (A : Set G))
    (f : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* Matrix.PSL3Two.SL)
    (hf : Function.Surjective f)
    (a : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
      ((specialLinearNatural 3).comp f))
    (b : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
      (fullDual.comp f))
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : A ⊓ B ≤ centralInvolutions T)
    (u : G)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let P := h.kernel (zpowers u)
    let R := (pResidual 2 P).map P.subtype
    SourceParabolicAction P →
    SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T) R →
    SourceCrossingGeometry (localModule T M) Mc Mc u →
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  dsimp only
  intro action coords crossing
  obtain ⟨hLN, hTL, hLF, hfull⟩ := source_component_action_placement
    hG T hempty hM hunique hmany hcard e L A hres hc eL hLA f hf
  obtain ⟨hcoreIndex, hrank⟩ := source_terminal_bounds_of_natural_dual
    hG T hempty hM hunique hmany hcard e hab
    (Mc ⊓ normalizer (A : Set G)) L A B hLN hTL hLF f hfull a b hAU hBU hsep
  exact source_terminal_witness_of_geometry hG T hempty hM hunique hmany hcard e hab Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
    u hu.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hu.2.2.2.2.2
    hcoreIndex hrank action coords crossing

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
