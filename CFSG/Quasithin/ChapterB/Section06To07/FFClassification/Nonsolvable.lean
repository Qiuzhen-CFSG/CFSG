module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.NormalComplement

/-!
# The nonsolvable FF residual before recognition

Minimal-parabolic uniqueness makes the two-residual the perfect terminal
derived subgroup. If minimal offenders moved the Fitting subgroup, the
proved B.1.9 theorem would construct an actual S3 coordinate. Its cubic
core lies in the two-residual, while every map from that perfect residual
to S3 is trivial, a contradiction. Thus the residual centralizes F(G).
The component-layer dichotomy and generalized Fitting self-centralization
then give O²(G)=E(G)=F*(G). No representation-family classification is used.

Source: Aschbacher–Smith, proof of B.6.9, printed p.116 (1 March 2004).
These are the original faithful FF hypotheses, with no semisimple-residual
or Fitting-centralization premise. The subsequent natural-family recognition
remains separate.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem minimalParabolic_nonsolvable_residual_eq_solvableResidual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) : pResidual 2 G = solvableResidual G := by
  have hn : ¬ solvableResidual G ≤ minimalParabolicCore T hP := by
    intro h
    let := minimalParabolic_core_solvable T hP
    let : Group.IsSolvable (solvableResidual G) :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion h) (inclusion_injective h)
    exact hs ((Group.isSolvable_iff_subgroup_quotient (solvableResidual G)).mpr
      ⟨inferInstance, inferInstance⟩)
  refine le_antisymm
    ((minimalParabolic_normal_subgroup_residual_dichotomy T hP _).resolve_left hn) ?_
  let : Group.IsNilpotent (G ⧸ pResidual 2 G) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact solvableResidual_le_of_solvable_quotient _

theorem minimalParabolic_nonsolvable_residual_perfect
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) : Group.IsPerfect (pResidual 2 G) := by
  rw [minimalParabolic_nonsolvable_residual_eq_solvableResidual T hP hs]
  infer_instance

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem minimalParabolic_nonsolvable_fittingMoved_eq_bot
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    FittingStructure.fittingMoved ρ = ⊥ := by
  classical
  by_contra hn
  obtain ⟨d⟩ := source_lemma_B_1_9 ρ hfaith hcore hn
  let i : Fin d.count := ⟨0, d.count_pos⟩
  let R := pResidual 2 G
  let : Group.IsPerfect R := minimalParabolic_nonsolvable_residual_perfect T hP hs
  have hrJ : R ≤ offenderSubgroup ρ := (offender_generation T hP ρ hff hcore).1
  let f : R →* d.factor i :=
    (Pi.evalMonoidHom (fun j => d.factor j) i).comp
      ((MonoidHom.fst _ _).comp (d.groupProduct.symm.toMonoidHom.comp (inclusion hrJ)))
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  have hfs : Group.IsSolvable (d.factor i) :=
    Group.isSolvable_of_isSolvable_injective (f := (d.factorModel i).toMonoidHom) (d.factorModel i).injective
  let := hfs
  have hz : ∀ r : R, f r = 1 := by
    intro r
    have hm := map_solvableResidual_le f
    rw [solvableResidual_eq_top, solvableResidual_eq_bot, ← MonoidHom.range_eq_map] at hm
    exact mem_bot.mp (hm (MonoidHom.mem_range.mpr ⟨r, rfl⟩))
  have hcard : Nat.card (d.oddFactor i) = 3 := by
    rw [Nat.card_congr (d.oddFactorModel i).toEquiv]
    exact Nat.card_zmod 3
  have hp : IsPGroup 3 (d.oddFactor i) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hne : d.oddFactor i ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hcard
    omega
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let x : G := a
  have hx : x ∈ d.oddFactor i := a.property
  have hxne : x ≠ 1 := fun he => hane (Subtype.ext he)
  have hxR : x ∈ R := by
    apply mem_pResidual_of_orderOf_coprime
    have hh := hp.orderOf_coprime (by decide : Nat.Coprime 3 2) (⟨x,hx⟩ : d.oddFactor i)
    rw [← Subgroup.orderOf_coe] at hh
    exact hh.symm
  have hxi : x ∈ d.factor i := by
    rw [d.oddFactor_eq] at hx
    exact map_subtype_le _ hx
  have hxJ : inclusion hrJ ⟨x,hxR⟩ = d.groupProduct (Pi.mulSingle i ⟨x,hxi⟩,1) :=
    Subtype.ext (d.groupProduct_single i ⟨x,hxi⟩).symm
  have he : f ⟨x,hxR⟩ = ⟨x,hxi⟩ := by
    change (d.groupProduct.symm (inclusion hrJ ⟨x,hxR⟩)).1 i = _
    rw [hxJ, MulEquiv.symm_apply_apply]
    simp
  exact hxne (congrArg Subtype.val (he.symm.trans (hz ⟨x,hxR⟩)))

/-- The non-solvable source residual centralizes the entire Fitting subgroup. -/
theorem minimalParabolic_nonsolvable_residual_centralizes_fitting
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    pResidual 2 G ≤ centralizer (fittingSubgroup G : Set G) := by
  have hf := minimalParabolic_nonsolvable_fittingMoved_eq_bot ρ T hP hs hcore hfaith hff
  have hm := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hf)
  exact (minimal_best_offender_generation T hP ρ hff hcore).1.trans hm

/-- The nonsolvable FF residual is exactly the component layer and F*(G). -/
theorem minimalParabolic_nonsolvable_semisimple_residual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    componentLayer G = pResidual 2 G ∧ generalizedFitting G = pResidual 2 G := by
  let : Group.IsPerfect (componentLayer G) := componentLayer_isPerfect
  have hLR : componentLayer G ≤ pResidual 2 G := by
    let : Group.IsNilpotent (G ⧸ pResidual 2 G) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_of_isPerfect_of_solvable_quotient _ _
  have hRL : pResidual 2 G ≤ componentLayer G := by
    obtain hl | hl := minimalParabolic_normal_subgroup_residual_dichotomy T hP (componentLayer G)
    · have hb : componentLayer G = ⊥ := by
        by_contra hn
        let : Nontrivial (componentLayer G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
        let := minimalParabolic_core_solvable T hP
        exact Group.IsPerfect.not_isSolvable (componentLayer G)
          (Group.isSolvable_of_isSolvable_injective (f := inclusion hl) (inclusion_injective hl))
      have hgf : generalizedFitting G = fittingSubgroup G := by
        rw [generalizedFitting, hb, sup_bot_eq]
      have hrF : pResidual 2 G ≤ fittingSubgroup G := by
        have hc := minimalParabolic_nonsolvable_residual_centralizes_fitting ρ T hP hs hcore hfaith hff
        have hz := centralizer_generalizedFitting_le G
        rw [hgf] at hz
        exact hc.trans hz
      let : Group.IsSolvable (pResidual 2 G) :=
        Group.isSolvable_of_isSolvable_injective (f := inclusion hrF) (inclusion_injective hrF)
      let : Group.IsNilpotent (G ⧸ pResidual 2 G) := (isPGroup_quotient_pResidual 2).isNilpotent
      exact (hs ((Group.isSolvable_iff_subgroup_quotient (pResidual 2 G)).mpr
        ⟨inferInstance,inferInstance⟩)).elim
    · exact hl
  have he := le_antisymm hLR hRL
  refine ⟨he, ?_⟩
  rw [generalizedFitting, he]
  exact sup_eq_right.mpr ((fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore).trans pPrimeCore_le_pResidual)

end CFSG.Quasithin.ChapterB
