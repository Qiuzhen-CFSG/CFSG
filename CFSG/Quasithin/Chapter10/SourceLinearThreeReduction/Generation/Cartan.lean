module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Contracts
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section02.Structure.ThreeHallGeneration
public import Theory.NumberTheory.BinaryMersenneDivisibility

/-!
# Original H-star Cartan data without an A₅ marking

An H-star member with generation parameter greater than one cannot have a
normal Sylow two-subgroup: a two-closed group is solvable and has parameter
at most one. Its unique maximal overgroup is therefore the literal H∩M.
The complete E.2.2 dispatcher supplies an actual odd Hall subgroup, cyclic
torus, and reflected normalizer escape on this same carrier.

The orthogonal centralizer branch needs only an exponent bound on that
Hall subgroup. Its cyclic torus then has order 2ᶠ−1 dividing 2ⁿ+1, forcing
f=2. We use the proved inequality n(H)≤f, never equality through a solvable
kernel. The geometry establishing this exponent bound remains separate.

Source: Aschbacher--Smith, 3.1.3, E.2.2 and 10.2.3,
combined manuscript of 1 March 2004, pp.572,215--216,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Large generation supplies minimal parabolicity without a Sylow-normalizer
control premise, for every original fundamental setup. -/
theorem source_hstar_minimal_parabolic_of_generation_gt_one
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  apply minimalParabolic_subtype T H
  apply Chapter3.HStar.minimalParabolic T (le_normalizer_componentOrbit L T) hH
  right
  intro hn
  let : Group.IsSolvable H :=
    IsTwoClosed.isSolvable ⟨T.subtype hH.1.1.2, hn⟩
  exact (not_lt_of_ge generationParameter_le_one_of_solvable) hlarge

/-- The intrinsic unique maximal subgroup is exactly the original overlap. -/
theorem source_hstar_parabolicMax_eq_overlap
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hP = D.maximalLocal.subgroupOf H := by
  let J := minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ D.maximalLocal.subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : D.maximalLocal.subgroupOf H ≠ ⊤ := fun he =>
    hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

/-- The actual E.2.2 data, with the prescribed Sylow, literal overlap,
ambient permutation and reflected normalizer escape all retained. -/
theorem source_hstar_cartan_data_of_generation_gt_one
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (f : ℕ),
      IsEGenerated f H ∧ generationParameter H ≤ f ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f,
        minimalParabolicMax (T.subtype hH.1.1.2) hP = D.maximalLocal.subgroupOf H ∧
        (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) ∧
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p →
          A ≤ d.witness.cyclicGroup → IsPGroup p A →
          ¬ H ⊓ normalizer (A.map H.subtype : Set G) ≤ D.maximalLocal := by
  let hP := source_hstar_minimal_parabolic_of_generation_gt_one D hH hlarge
  obtain ⟨f,hg,hb,d,hescape⟩ := MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) hP hlarge
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  refine ⟨hP,f,hg,hb,d,he,?_,?_⟩
  · have hp := d.witness.permutes
    rw [d.sylow_eq] at hp
    have hm := congrArg (Set.image H.subtype) hp
    change H.subtype '' ((d.witness.abelianGroup : Set H) *
      ((T : Subgroup G).subgroupOf H : Set H)) =
      H.subtype '' (((T : Subgroup G).subgroupOf H : Set H) *
        (d.witness.abelianGroup : Set H)) at hm
    simpa only [Set.image_mul, ← Subgroup.coe_map,
      map_subgroupOf_eq_of_le hH.1.1.2, Sylow.coe_coe] using hm
  · intro p hp A ho hA hAp hN
    apply hescape p hp A ho hA hAp
    rw [he]
    intro x hx
    exact hN ⟨x.property, A.le_normalizer_map H.subtype (mem_map.mpr ⟨x,hx,rfl⟩)⟩

/-- Exponent control on the actual Hall subgroup bounds the original
generation parameter; no equality n(H)=f is used. -/
theorem source_hstar_generation_le_two_of_hall_exponent
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤) {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP f)
    (hf : generationParameter H ≤ f)
    (hexp : ∃ n : ℕ, Monoid.exponent d.witness.abelianGroup ∣ 2 ^ n + 1) :
    generationParameter H ≤ 2 := by
  by_cases hsmall : f ≤ 1
  · omega
  obtain ⟨n,hn⟩ := hexp
  let := d.witness.cyclic
  have hd := (Monoid.exponent_dvd_of_monoidHom (inclusion d.witness.cyclic_le)
    (inclusion_injective d.witness.cyclic_le)).trans hn
  rw [IsCyclic.exponent_eq_card, d.witness.card] at hd
  have he := Nat.eq_two_of_two_pow_sub_one_dvd_two_pow_add_one (by omega : 2 ≤ f) hd
  omega

end CFSG.Quasithin.Chapter10
