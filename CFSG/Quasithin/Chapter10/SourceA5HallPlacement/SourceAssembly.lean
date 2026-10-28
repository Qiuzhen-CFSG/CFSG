module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelCounterexample
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelSource
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FaithfulConsumers
/-!
# Assembly of the original Hall placement from the two earlier source steps

The actual intrinsic Hall witness is faithful: a nontrivial kernel supplies
an elementary odd actor whose normalizer escapes by 4.4.13(1), whereas the
nonnormal-pair case of 4.4.3 puts that same normalizer inside M. Faithful
placement then gives the original generation bound. The two earlier-source
steps remain explicit until their independent producers are integrated.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual Hall witness is faithful once the two source normalizer
steps are supplied. Its inclusion, Hall property and ambient image are literal. -/
theorem source_a5_hstar_hall_faithful_of_oddNormalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn)
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  obtain ⟨n,hg,hb,d,hm,_⟩ := source_a5_hstar_cartan_data D e hn hH hlarge
  have hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ := by
    by_contra hk
    obtain ⟨p,B,hp,ho,hB,hBe,_,hBC,hBV,hBT,hout⟩ :=
      source_a5_hstar_hall_kernel_escaping_elementary D e hn ht htn hcoords
        earlier hH hlarge d hm hk
    exact hout (hcontrol p hp ho B hB hBe hBC hBV hBT)
  refine ⟨d.witness.abelianGroup,hm ▸ d.hall_le,hm ▸ d.hall,?_⟩
  apply eq_bot_iff.mpr
  rintro x ⟨⟨a,ha,rfl⟩,hC⟩
  have ha1 : a = 1 := by
    have ham : a ∈ d.witness.abelianGroup ⊓
        (sectionCentralizer (localOrbit T L)).subgroupOf H := ⟨ha,hC⟩
    simpa only [hk,mem_bot] using ham
  simp only [ha1,map_one,mem_bot]

/-- The complete separated source inputs reduce the generation bound to
4.4.13(1) and the nonnormal-pair normalizer conclusion of 4.4.3. -/
theorem source_a5_hstar_generation_bound_of_oddNormalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H ≤ 2 := by
  by_cases hlarge : 1 < generationParameter H
  · obtain ⟨B,hBM,hHall,hfaith⟩ := source_a5_hstar_hall_faithful_of_oddNormalizer_control
      D e hn ht htn (source_a5_original_bounded_separated_coordinates D e hn ht htn
        hD hbound hsep) earlier hcontrol hH hlarge
    exact source_a5_hstar_generation_bound_of_hall_faithful D e hn hH B hBM hHall hfaith
  · omega
local instance hallAssemblyMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance hallAssemblyFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The separated original source reaches its natural weak-closure endpoint
once the two independent odd-normalizer source results are supplied. -/
theorem source_a5_natural_and_parameters_eq_two_of_oddNormalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧ generationParameter H = 2 ∧
      ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  obtain ⟨hi,hcross⟩ := source_a5_original_irreducible_of_minimal_separated_seed
    D e hn ht htn hD hbound hsep
  have hb := source_a5_hstar_generation_bound_of_oddNormalizer_control
    D e hn ht htn hD hbound hsep earlier hcontrol hH
  have hlargeE : (1 : ℕ∞) < (generationParameter H : ℕ∞) :=
    (source_a5_globalW_gt_one D e hi hn ht htn hcross hcent).trans_le
      (source_a5_hstar_globalW_le_generation D e hcent hH hb)
  have hlarge : 1 < generationParameter H := by exact_mod_cast hlargeE
  obtain ⟨B,hBM,hHall,hfaith⟩ := source_a5_hstar_hall_faithful_of_oddNormalizer_control
    D e hn ht htn (source_a5_original_bounded_separated_coordinates D e hn ht htn
      hD hbound hsep) earlier hcontrol hH hlarge
  exact source_a5_natural_and_parameters_eq_two_of_hall_faithful
    D e hi hn ht htn hcross hcent hH B hBM hHall hfaith
end CFSG.Quasithin.Chapter10
