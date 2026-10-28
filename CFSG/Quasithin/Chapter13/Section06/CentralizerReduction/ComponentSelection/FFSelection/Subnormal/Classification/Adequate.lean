module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource

/-!
# The adequate normalizer bound for the literal cubic

The outer group configuration suffices to identify the restricted cubic as
O₃(J) ∩ J′, hence to prove its normality in the original ambient group.
The remaining alternatives retain the source action data and give their
proved normalizer bounds. Thus the full corrected adequate alternatives
give the ambient normalizer-index conclusion used in 13.6.10.

The moved-plane conclusion remains separate: its old outer proof used
secondDimension, which is absent from OuterSixThreeShape. None of the
results here asserts that dimension or the disputed fixed-space splitting.
Source: Aschbacher–Smith, B.5.6(4), p.105; 13.6.10, p.928
(combined manuscript, 1 March 2004).
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
variable {D : Type*} [Group D] [Finite D]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W)

private theorem six_threeCore : pCore 3 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 3 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top
    with hb | ht
  · exact hb
  · have hp := pCore_isPGroup (p := 3) (G := alternatingGroup (Fin 6))
    rw [ht] at hp
    have hp' : IsPGroup 3 (alternatingGroup (Fin 6)) := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp'
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have htwo : 2 ∣ 3 ^ n := hn ▸ (by rw [hc]; norm_num)
    have := Nat.prime_two.dvd_of_dvd_pow htwo
    norm_num at this

omit [Finite D] in
private theorem core_derived_le_second (c : ChapterB.OuterSixThreeShape D) :
    pCore 3 D ⊓ _root_.commutator D ≤ c.second := by
  have hfirst : pCore 3 c.first = ⊥ := by
    apply map_injective (f := c.firstEquiv.toMonoidHom) c.firstEquiv.injective
    rw [pCore_map_iso, Subgroup.map_bot, six_threeCore]
  let f : (c.first × c.second) →* D :=
    (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp c.product.injective
  let R := (pCore 3 D).comap f
  have hp : IsPGroup 3 R := pCore_isPGroup.comap_of_injective f hf
  have hmap : R.map (MonoidHom.fst c.first c.second) ≤ pCore 3 c.first :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ Prod.fst_surjective, hp.map _⟩
  rw [hfirst] at hmap
  have hk : R ≤ (MonoidHom.fst c.first c.second).ker :=
    (map_eq_bot_iff R).mp (le_bot_iff.mp hmap)
  let := outerSixThreeShape_product_normal c
  let := outerSixThreeShape_quotient_isCyclic c
  have hd : _root_.commutator D ≤ c.first ⊔ c.second :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rintro x ⟨hx, hxd⟩
  let y := c.product.symm ⟨x, hd hxd⟩
  have he : (c.product y : D) = x := congrArg Subtype.val (c.product.apply_symm_apply _)
  have hy : y ∈ R := by
    change (c.product y : D) ∈ pCore 3 D
    rwa [he]
  have hy1 : y.1 = 1 := hk hy
  have he' : x = (y.2 : D) := by
    calc
      x = (c.product (y.1, y.2) : D) := he.symm
      _ = (y.1 : D) * (y.2 : D) := c.product_apply _ _
      _ = (y.2 : D) := by simp [hy1]
  rw [he']
  exact y.2.property

variable {ρ} {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
omit [Finite D] in
private theorem internal_le_derived (h : CubicHypothesis ρ A S C) :
    A.subgroupOf (offenderSubgroup ρ) ≤ _root_.commutator (offenderSubgroup ρ) := by
  rw [h.internal_full]
  exact commutator_mono le_top le_top

/-- The actual restricted cubic is the specified C₃ factor, using its
subnormality and full commutator condition, with no factor placement assumed. -/
theorem outerSixThree_internal_eq_second_of_adequate (h : CubicHypothesis ρ A S C)
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) :
    A.subgroupOf (offenderSubgroup ρ) = c.second := by
  apply eq_of_le_of_card_ge
    ((le_inf h.internal_le_threeCore (internal_le_derived h)).trans
      (core_derived_le_second c))
  rw [h.internal_card, Nat.card_congr c.secondEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- An intrinsic characteristic description of the cubic inside J.
The three-core itself need not be identified. -/
theorem outerSixThree_internal_eq_core_derived_of_adequate (h : CubicHypothesis ρ A S C)
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) :
    A.subgroupOf (offenderSubgroup ρ) =
      pCore 3 (offenderSubgroup ρ) ⊓ _root_.commutator (offenderSubgroup ρ) := by
  apply le_antisymm (le_inf h.internal_le_threeCore (internal_le_derived h))
  rw [outerSixThree_internal_eq_second_of_adequate h c]
  exact core_derived_le_second c

/-- The cubic in the outer alternative is normal in the original ambient D. -/
theorem outerSixThree_normal_of_adequate (h : CubicHypothesis ρ A S C)
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) : A.Normal := by
  have hchar : (A.subgroupOf (offenderSubgroup ρ)).Characteristic := by
    rw [outerSixThree_internal_eq_core_derived_of_adequate h c]
    infer_instance
  let := hchar
  have hn : ((A.subgroupOf (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  simpa only [map_subgroupOf_eq_of_le h.le_offender] using hn


/-- Every adequate branch supplies the original ambient orbit bound.
The outer branch uses characteristicity, not any module dimension. -/
theorem normalizer_bound_of_adequate [FiniteDimensional (ZMod 2) W]
    (h : CubicHypothesis ρ A S C)
    (hc : ProjectiveLine.AdequateSourceAlternative (offenderRepresentation ρ)) :
    (normalizer (A : Set D)).index ≤ 2 := by
  cases hc with
  | trivial ht => exact (h.not_trivial ht).elim
  | quasisimple hq ha => exact (quasisimple_excluded_of_source ρ h hq ha).elim
  | symmetricThree c => exact (symmetricThree_bounds ρ h c).2
  | twoFactors c => exact (twoFactors_bounds ρ h c).2
  | outerSixThree c =>
    rw [normalizer_eq_top_iff.mpr (outerSixThree_normal_of_adequate h c), index_top]
    decide
  | hyperplane c => exact (hyperplane_bounds ρ h c).2

section Application
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "ρ₀" => uvRepresentation z₀ v₀ (A5Module.markedZ_mem_Gv s)
local notation "A₀" => starImage z₀ v₀ (Lv L v₀)

/-- Apply the orbit bound to the original G_v quotient action and Sylow.
Only the universal adequate classifier and genuine earlier local data remain. -/
theorem marked_normalizer_bound_of_adequate (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    {𝒦 : GroupClass.{u}}
    (classification : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀)) : (normalizer (A₀ : Set (Gstar z₀ v₀))).index ≤ 2 :=
  normalizer_bound_of_adequate
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    (classification _ _ _
      (uv_offender_hypothesis z₀ v₀ (A5Module.markedZ_mem_Gv s) hSQ hcore))

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
