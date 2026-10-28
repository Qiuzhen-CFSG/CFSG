module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.Source
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors

/-!
# Small fixed codimension and the E.3.6 premise in degree four

On an inner natural-plus-dual action, the two positive fixed codimensions
add. If their sum is at most two, the displacement-map rank bound gives
actor rank at most one. An outer involution fixes dimension four, so every
elementary actor fixing codimension at most two is inner. The same calculations
prove the local involution parameter at least two. Together with r≥4 this
supplies s>1 and E.3.6's centralizer equality for the actual first-stage offender.
The literal automizer application is the small-rank reverse-action bound
used in 12.1.8; the ambient reverse-action assembly remains with this owner.
Source: Aschbacher--Smith, H.9.3 and 12.1.8, printed pp.391--392,792--793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {n : ℕ} {M E : Type*} [Group M] [Finite M]
  [AddCommGroup E] [Module (ZMod 2) E]

omit [Finite M] in
theorem inner_fixedCodim_eq (S : SourceSetup n M E) (I : Subgroup M) :
    fixedCodim ((innerNatural S I).prod (innerNatural S I).dual) ⊤ =
      fixedCodim S.representation (I ⊓ componentLayer M) := by
  let : FiniteDimensional (ZMod 2) E :=
    FiniteDimensional.of_injective S.model.coordinates.toLinearMap S.model.coordinates.injective
  have hh := fixedCodim_map_equivariant
    (S.representation.comp (I ⊓ componentLayer M).subtype)
    ((innerNatural S I).prod (innerNatural S I).dual)
    (MonoidHom.id ↥(I ⊓ componentLayer M)) S.model.coordinates
    (innerNatural_equivariant S I) ⊤
  rw [Subgroup.map_id] at hh
  rw [← hh, fixedCodim, fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

/-- In a faithful inner doubled action, fixed codimension at most two
forces actor rank at most one. -/
theorem inner_small_fixedCodim (S : SourceSetup n M E) (I : Subgroup M)
    (hI : I ≤ componentLayer M) (hc : fixedCodim S.representation I ≤ 2) :
    rank I ≤ 1 := by
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  have hc' : fixedCodim (ρ.prod ρ.dual) ⊤ ≤ 2 := by
    rw [inner_fixedCodim_eq, inf_eq_left.mpr hI]
    exact hc
  have he : J = I := inf_eq_left.mpr hI
  have hrt : rank (⊤ : Subgroup J) = rank J := by simp [rank]
  by_cases hz : (⊤ : Subgroup J) = ⊥
  · have hr : rank (⊤ : Subgroup J) = 0 := by simp [hz,rank]
    rw [hrt, he] at hr
    omega
  have hp := fixedCodim_pos_of_faithful ρ (innerNatural_faithful S I) hz
  have hq := fixedCodim_pos_of_faithful ρ.dual
    (faithful_dual ρ (innerNatural_faithful S I)) hz
  have hr := rank_le_fixedCodim_mul_dual ρ (innerNatural_faithful S I) ⊤
  rw [fixedCodim_prod] at hc'
  have ha : fixedCodim ρ ⊤ = 1 := by omega
  have hb : fixedCodim ρ.dual ⊤ = 1 := by omega
  rw [ha,hb,mul_one,hrt,he] at hr
  exact hr

omit [Finite M] in
/-- Nontrivial inner actors fix codimension at least two on the doubled module. -/
theorem inner_fixedCodim_ge_two (S : SourceSetup n M E) (I : Subgroup M)
    (hI : I ≤ componentLayer M) (hne : I ≠ ⊥) :
    2 ≤ fixedCodim S.representation I := by
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  have hj : J = I := inf_eq_left.mpr hI
  have ht : (⊤ : Subgroup J) ≠ ⊥ := by
    intro he
    apply hne
    apply bot_unique
    intro a ha
    have he' : (⟨a,hj ▸ ha⟩ : J) ∈ (⊥ : Subgroup J) := he ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp he')
  have hp := fixedCodim_pos_of_faithful ρ (innerNatural_faithful S I) ht
  have hq := fixedCodim_pos_of_faithful ρ.dual
    (faithful_dual ρ (innerNatural_faithful S I)) ht
  have he : fixedCodim (ρ.prod ρ.dual) ⊤ = fixedCodim S.representation I :=
    (inner_fixedCodim_eq S I).trans (congrArg (fixedCodim S.representation) hj)
  rw [fixedCodim_prod] at he
  omega

omit [Finite M] in
theorem four_outer_fixedCodim (S : SourceSetup 4 M E) (a : M)
    (ha : orderOf a = 2) (hout : a ∉ componentLayer M) :
    fixedCodim S.representation (zpowers a) = 4 := by
  let : FiniteDimensional (ZMod 2) E :=
    FiniteDimensional.of_injective S.model.coordinates.toLinearMap S.model.coordinates.injective
  let T : Sylow 2 M := Classical.choice inferInstance
  have hd : Module.finrank (ZMod 2) E = 8 := by
    rw [S.model.coordinates.finrank_eq]
    norm_num [CoordinateSpace, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
  have he : fixedSpace S.representation (zpowers a) = SourceFourActors.elementFixed S a := by
    ext v
    rw [SourceFourActors.mem_elementFixed]
    exact mem_fixedSpace_zpowers_iff S.representation a v
  have hh := fixedCodim_add_finrank S.representation (zpowers a)
  rw [he, SourceFourActors.outer_fixed_finrank S T a ha hout, hd] at hh
  omega

/-- Any elementary actor fixing codimension at most two is inner and has
rank at most one; this is the reverse-action contradiction of 12.1.8. -/
theorem four_small_fixedCodim (S : SourceSetup 4 M E) (I : Subgroup M)
    [IsElementaryAbelian 2 I] (hc : fixedCodim S.representation I ≤ 2) :
    I ≤ componentLayer M ∧ rank I ≤ 1 := by
  let : FiniteDimensional (ZMod 2) E :=
    FiniteDimensional.of_injective S.model.coordinates.toLinearMap S.model.coordinates.injective
  have hi : I ≤ componentLayer M := by
    intro a ha
    by_contra ho
    have ha1 : a ≠ 1 := by intro he; exact ho (he ▸ one_mem _)
    have horder : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hm := CFSG.Quasithin.ChapterE.fixedCodim_mono S.representation (zpowers_le.mpr ha)
    rw [four_outer_fixedCodim S a horder ho] at hm
    omega
  exact ⟨hi,inner_small_fixedCodim S I hi hc⟩

omit [Finite M] in
/-- The local involution parameter is at least two on the degree-four module. -/
theorem four_moduleM_ge_two (S : SourceSetup 4 M E) :
    2 ≤ CFSG.Quasithin.ChapterE.moduleM S.representation := by
  unfold CFSG.Quasithin.ChapterE.moduleM
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro k (rfl | ⟨a,ha,rfl⟩)
  · rw [S.model.coordinates.finrank_eq]
    norm_num [CoordinateSpace, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
  · by_cases hi : a ∈ componentLayer M
    · apply inner_fixedCodim_ge_two S (zpowers a) (zpowers_le.mpr hi)
      intro he
      have h1 : a = 1 := by simpa only [he,mem_bot] using mem_zpowers a
      simp [h1] at ha
    · rw [four_outer_fixedCodim S a ha hi]
      decide

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank

open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

/-- The reverse-action rank bound for the literal ambient automizer.
In 12.1.8 the inner preimage B supplies the fixed subspace of corank two. -/
theorem actual_four_small_fixedCodim
    (S : SourceSetup 4 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (W : Set G))
    (hc : subgroupCorank W (W ⊓ centralizer (A : Set G)) ≤ 2) :
    rank (inducedAutomizer W A) ≤ 1 := by
  let := inducedAutomizer_elementary W A hA
  apply (four_small_fixedCodim S (inducedAutomizer W A) ?_).2
  rw [hρ,fixedCodim_inducedAutomizer W A hA]
  exact hc

/-- E.3.6's fixed-space equality for the actual first-stage degree-four
conjugate, deriving s>1 from r≥4 and the proved local involution bound. -/
theorem four_first_centralizer_eq
    (S : SourceSetup 4 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    {T : Subgroup G} {g : G} (hg : IsWOffenderAt W T g)
    (hw : globalW W T = 1) (hr : (4 : ℕ∞) ≤ globalR W) :
    W ⊓ centralizer (offenderNormalizer W g : Set G) =
      W ⊓ centralizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply (offender_fixedSpaceFamily_of_lt_globalS hg ?_).1
  have hm : 2 ≤ localM W := by
    rw [localM, ← hρ]
    exact four_moduleM_ge_two S
  rw [hw,globalS]
  apply lt_min
  · exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 4) hr
  · exact_mod_cast (show 1 < localM W by omega)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank

