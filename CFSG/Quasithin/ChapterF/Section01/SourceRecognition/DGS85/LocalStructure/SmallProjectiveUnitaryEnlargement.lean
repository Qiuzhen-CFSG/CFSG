module
public import Theory.SpecificGroups.SU3.SmallProjectiveTwoActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitaryThreeCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementAction

/-!
# The precise remaining small projective enlargement alternative

The original full Borel core preserves a quotient Sylow. Its image contains
the inner image of the original starred Sylow and restricts faithfully to
the characteristic nine-group. The GL₂(3) bound therefore gives inner index
at most two. The literal enlargement action identifies the actual two-core
quotient with this generated automorphism image: either the enlargement
is the original starred subgroup or that quotient has order 144.

The original F.1.1 application retains the full Borel, starred inclusion,
and supplied quotient marking. It provides the enlarged PSU₃(2) marking
unless the actual quotient has order 144. The strict alternative is not
excluded here, and this does not prove unrestricted DGS 6.1.
Source: Aschbacher--Smith F.1.1 and F.1.9, pp.259--262;
DGS, Groups and Graphs (1985), p.104 and 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The degree-one projective enlargement either preserves the original starred
endpoint or has actual two-core quotient of order 144. -/
theorem localEnlargement_small_projective_alternatives (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    localEnlargement d = d.Pstar ∨
      Nat.card (localEnlargement d ⧸ pCore 2 (localEnlargement d)) = 144 := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let D := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite D := Nat.finite_of_card_ne_zero
    (by rw [HermitianForm.FixedFieldTwo.card_projective J hc hconj]; decide)
  let M := localEnlargement d
  let R := B.pCoreIn 2
  let a : M →* MulAut D := (MulAut.congr e).toMonoidHom.comp (localStarCoreAction d)
  let c := markedBorelCoreAction d e
  let I := MulAut.innerSubgroup D
  have ha (x : d.Pstar) : a (inclusion le_sup_left x) =
      MulAut.conj (e (QuotientGroup.mk' (pCore 2 d.Pstar) x)) := by
    change MulAut.congr e (localStarCoreAction d (inclusion le_sup_left x)) = _
    rw [localStarCoreAction_on_star]
    ext z
    simp [MulAut.congr_apply,MulAut.conj_apply]
  have hr (r : R) : a (inclusion le_sup_right r) = c r := by
    apply MulEquiv.ext
    intro z
    obtain ⟨q,rfl⟩ := e.surjective z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.Pstar) q
    change e (localStarCoreAction d (inclusion le_sup_right r)
      (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply]
    exact (congrArg e (localStarCoreAction_mk d
      (inclusion (show R ≤ M from le_sup_right) r) x)).trans
        (markedBorelCoreAction_mk d e r x).symm
  have hI : I ≤ a.range := by
    rintro z ⟨q,rfl⟩
    obtain ⟨q,rfl⟩ := e.surjective q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.Pstar) q
    exact ⟨inclusion le_sup_left x,ha x⟩
  have hgen : a.range = I ⊔ c.range := by
    apply le_antisymm
    · have hl : d.Pstar.subgroupOf M ≤ (I ⊔ c.range).comap a := by
        intro x hx
        have he : x = inclusion le_sup_left (⟨x,hx⟩ : d.Pstar) := rfl
        change a x ∈ I ⊔ c.range
        rw [he,ha]
        exact (show I ≤ I ⊔ c.range from le_sup_left) ⟨e (QuotientGroup.mk' _ ⟨x,hx⟩),rfl⟩
      have hR : R.subgroupOf M ≤ (I ⊔ c.range).comap a := by
        intro x hx
        have he : x = inclusion le_sup_right (⟨x,hx⟩ : R) := rfl
        change a x ∈ I ⊔ c.range
        rw [he,hr]
        exact (show c.range ≤ I ⊔ c.range from le_sup_right) ⟨⟨x,hx⟩,rfl⟩
      have hh := sup_le hl hR
      rw [←subgroupOf_sup (show d.Pstar ≤ M from le_sup_left)
        (show R ≤ M from le_sup_right)] at hh
      change M.subgroupOf M ≤ _ at hh
      rw [subgroupOf_self] at hh
      rintro z ⟨x,rfl⟩
      exact hh (mem_top x)
    · refine sup_le hI ?_
      rintro z ⟨r,rfl⟩
      exact ⟨inclusion le_sup_right r,hr r⟩
  have hTR : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ R :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  let U := (quotientSylow d.sylow).mapSurjective (f := e.toMonoidHom) e.surjective
  have hU : (U : Subgroup D).map (MulAut.conj : D →* MulAut D) ≤ c.range := by
    rintro z ⟨u,hu,rfl⟩
    change u ∈ ((d.sylow : Subgroup d.Pstar).map (QuotientGroup.mk' (pCore 2 d.Pstar))).map e.toMonoidHom at hu
    obtain ⟨q,⟨x,hx,rfl⟩,rfl⟩ := hu
    let r : R := ⟨x,hTR (mem_map_of_mem _ hx)⟩
    refine ⟨r,?_⟩
    exact (hr r).symm.trans (ha x)
  obtain ⟨T,hT⟩ := markedBorelCoreAction_normalizer_displacements d hB e
  have hp : IsPGroup 2 c.range :=
    (isPGroup_pCoreIn 2 B).of_surjective c.rangeRestrict c.rangeRestrict_surjective
  obtain ⟨_,he⟩ := HermitianForm.SmallThreeCore.projective_inner_join_two_actor_index
    J hc hconj c.range hp T (fun r => by
      obtain ⟨x,hx⟩ := r.property
      exact hx ▸ (hT x).1) U hU
  have hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center D := (centerCongr e ⟨x,hx⟩).property
    rw [HermitianForm.EvenProjectiveComparison.center_eq_bot J (n := 1)
      (by decide) (by simpa using hc) (by simpa using hconj),mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  rcases he with he | he
  · left
    apply localEnlargement_eq_star_of_inner d hz
    rintro b ⟨x,rfl⟩
    have hh : a x ∈ I := by
      change I ⊔ c.range = I at he
      rw [←he,←hgen]
      exact ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hh
    obtain ⟨t,ht⟩ := (MulAut.congr_inner_iff e (localStarCoreAction d x)).mp ⟨y,hy.symm⟩
    exact ⟨t,ht.symm⟩
  · right
    let f : (localStarCoreAction d).range ≃* a.range :=
      ((localStarCoreAction d).range.equivMapOfInjective (MulAut.congr e).toMonoidHom
        (MulAut.congr e).injective).trans (MulEquiv.subgroupCongr (by
          exact MonoidHom.range_comp (MulAut.congr e).toMonoidHom (localStarCoreAction d) |>.symm))
    have he' : Nat.card a.range = 144 := hgen.symm ▸ he
    exact (Nat.card_congr ((localStarCoreQuotientEquiv d hz).trans f).toEquiv).trans he'

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal original full-Borel-core action has two-power image of order dividing sixteen. -/
theorem original_small_projective_actor_card (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nat.card (originalMarkedBorelCoreAction h i e).range ∣ 16 := by
  let a := originalMarkedBorelCoreAction h i e
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Nat.finite_of_card_ne_zero
    (by rw [HermitianForm.FixedFieldTwo.card_projective J hc hconj]; decide)
  obtain ⟨T,hT⟩ := original_marked_borel_core_preserves_sylow h i e
  apply HermitianForm.SmallThreeCore.projective_two_actor_card_dvd_sixteen J hc hconj
    ((isPGroup_pCoreIn 2 (commonBorel L S)).of_surjective a.rangeRestrict a.rangeRestrict_surjective)
    a.range.subtype a.range.subtype_injective T
  intro r
  obtain ⟨x,hx⟩ := r.property
  change (T : Subgroup _).map r.val.toMonoidHom = T
  rw [←hx]
  exact hT x

/-- The original small projective endpoint is unchanged or has actual enlarged quotient of order 144. -/
theorem original_small_projective_enlargement_alternatives (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    enlargedEndpoint L S i = starredParabolic L S i ∨
      Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) = 144 := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have hB : ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup _) = pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
    apply f11_borel_core_sylow hh
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  have he := localEnlargement_small_projective_alternatives (hh.starredLocalRankOneData i)
    hB J hc hconj ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i,HypothesisF11.starredLocalRankOneData_Pstar,
    SuzukiContainment.reduced_starredParabolic h i] at he
  exact he

/-- The original marking yields an enlarged PSU3(2) marking, with only the explicit order-144 alternative retained. -/
theorem original_small_projective_enlarged_marking_or_card (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    ClassicalGroup.IsPSU (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 3 2 ∨
      Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) = 144 := by
  obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  rcases original_small_projective_enlargement_alternatives h i J hc hconj e with he | he
  · left
    let a := MulEquiv.subgroupCongr he
    let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    exact ⟨F,inferInstance,inferInstance,J,hc,hconj,
      ⟨b.trans ((h.starredQuotientEquiv i).symm.trans e)⟩⟩
  · exact Or.inr he
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
