module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.GroupTheory.NormalizerInnerAutomorphisms

/-!
# The actual projective action in the PSL₂(4) branch

The faithful five-point model compares PSL₂(4) with A₅, and the proved
icosahedral presentation compares PSL₂(5) with the same A₅. Prime-field
automorphism coverage then represents every automorphism by an actual
PGL₂(5) matrix. Thus the outer-PGL exclusion of 16.4.6 excludes precisely
the noninner involution actions on the component in this branch.

The earlier-source input is quantified over every conjugate-centralizer
intersection setup for the fixed component and Sylow subgroup. It is the
parameter-five specialization of 16.4.6, not a claimed proof of that lemma.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 16.4.6,
printed pp.1184–1186, and Proposition 16.5.1, printed p.1194.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.SmallLinear
open Subgroup GorensteinWalter OuterResidual OuterResidual.PGLShadow

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
/-- The centerless field-four component is the actual prime-field PSL₂(5). -/
theorem exists_five_equiv (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 4) :
    Nonempty (L ≃* PSL2 (ZMod 5)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.trans (e.trans (e4.trans e5.symm))⟩

/-- Every noninner action on this actual model comes from an outer PGL matrix. -/
theorem not_outerPGL_iff_inner (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (e : L ≃* PSL2 (ZMod 5)) :
    (¬ InducesOuterPGL (F := ZMod 5) h hr e) ↔ ∃ x : L, involutionAction h hr = MulAut.conj x := by
  let hF : IsOddPrimePower (Nat.card (ZMod 5)) :=
    ⟨5, 1, by decide, by decide, by decide, by simp⟩
  have hc : 3 < Nat.card (ZMod 5) := by norm_num
  constructor
  · intro hn
    obtain ⟨A, hA⟩ := Theory.PSL2.primeField_pgl_coverage (p := 5) (by decide : Odd 5)
      (by decide) (MulAut.congr e (involutionAction h hr))
    have hAi : A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod 5)).range := by
      by_contra hAi
      exact hn ((inducesOuterPGL_iff (F := ZMod 5) h hr e hF hc).mpr ⟨A, hAi, hA.symm⟩)
    obtain ⟨y, rfl⟩ := hAi
    refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hA.symm.trans (pgl2InnerAutPSL2_toPGL (ZMod 5) hF hc y)
  · intro hi ho
    exact not_inner_of_inducesOuterPGL (F := ZMod 5) h hr e hF hc ho hi

/-- The required specialization of source 16.4.6, with its universal
quantification over applicable conjugate-centralizer configurations retained. -/
def FiveOuterPGLExclusion (T : Sylow 2 G) (z : G) (L : Subgroup G) : Prop :=
  ∀ (b : G) (S : Subgroup G) (h : IntersectionSetup T z L b S)
    (r : G) (hr : r ∈ S), orderOf r = 2 →
    ∀ e : L ≃* PSL2 (ZMod 5), ¬ InducesOuterPGL (F := ZMod 5) h hr e

/-- The source exclusion puts every involution generator of a relative Sylow
in the inner-action preimage C_G(L)L. -/
theorem omega_le_inner_join (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 (ZMod 5)) (hex : FiveOuterPGLExclusion T z L) :
    omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro r hr hr2
  by_cases hr1 : r = 1
  · exact hr1 ▸ one_mem _
  have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
  obtain ⟨x, hx⟩ := (not_outerPGL_iff_inner h hr e).mp (hex g R h r hr hro e)
  have hm : (⟨r, h.sylow_normalizes (h.le_sylow hr)⟩ : normalizer (L : Set G)) ∈
      (MulAut.conj : L →* MulAut L).range.comap L.normalizerMonoidHom :=
    ⟨x, hx.symm⟩
  rw [normalizerMonoidHom_comap_conj_range] at hm
  simpa only [mem_subgroupOf, sup_comm] using hm

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.SmallLinear
