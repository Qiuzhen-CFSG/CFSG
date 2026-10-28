module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalLocalPassage
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductEmbedding
public import Theory.Alternating.FivePairOuterTwo

/-!
The original full actor contains the literal orbit image as a centerless A₅
square. If that image has trivial centralizer, its outer automorphism quotient
is a two-group. The original Sylow subgroup then forces full/local equality,
which closes the separated-seed irreducibility and cross-centralization branch.

This isolates the centralizer input in the passage used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.3.9 and D.3.21. Its discharge is
separate from the orbit marking and the original module comparison proved here.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

include D e in
/-- The actual orbit image, not an abstract replacement, is the marked A₅ pair. -/
theorem source_a5_original_actor_orbit_model
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    Nonempty (J ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let J := (R.subgroupOf M).map q
  obtain ⟨i,hi,_,hdiagram⟩ := source_a5_original_product_embedding D e hn ht htn
  have hrange : i.range = J := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := originalA5ProductProjection_surjective D e hn ht htn a
      rw [hdiagram]
      exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨originalA5ProductProjection D e hn ht htn ⟨x,hx⟩,hdiagram ⟨x,hx⟩⟩
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hi).symm⟩

include D e in
/-- The actual A₅ orbit image is centerless. -/
theorem source_a5_original_actor_orbit_center
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    center J = ⊥ := by
  dsimp only
  obtain ⟨f⟩ := source_a5_original_actor_orbit_model D e hn ht htn
  have hz : center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = ⊥ := by
    rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot]
  apply eq_bot_iff.mpr
  intro x hx
  have hfx := (centerCongr f ⟨x,hx⟩).property
  change f x ∈ center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) at hfx
  rw [hz,mem_bot] at hfx
  exact f.map_eq_one_iff.mp hfx

include D e in
/-- Triviality of the actual pair centralizer closes the outer actor quotient. -/
theorem source_a5_original_actor_quotient_two_of_centralizer_eq_bot
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) = ⊥ →
      IsPGroup 2 ((D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) ⧸ J) := by
  dsimp only
  intro hc
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let J := (R.subgroupOf M).map q
  obtain ⟨i,hi,hinormal,hdiagram⟩ := source_a5_original_product_embedding D e hn ht htn
  have hrange : i.range = J := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := originalA5ProductProjection_surjective D e hn ht htn a
      rw [hdiagram]
      exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨originalA5ProductProjection D e hn ht htn ⟨x,hx⟩,hdiagram ⟨x,hx⟩⟩
  let _ := hinormal
  have hc' : centralizer (i.range : Set (M ⧸ centralizer (U : Set M))) = ⊥ := by
    rw [hrange]
    exact hc
  have hp := Theory.AlternatingFive.quotient_isPGroup_two_of_normal_pair i hi hc'
  exact hp.of_surjective (QuotientGroup.quotientMulEquivOfEq hrange).toMonoidHom
    (QuotientGroup.quotientMulEquivOfEq hrange).surjective

include D e in
/-- The centralizer bound feeds the actual full/local module equality. -/
theorem source_a5_full_eq_local_of_actor_pair_centralizer_eq_bot
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hc : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) = ⊥) :
    D.fullModule = D.moduleSubgroup :=
  source_full_eq_local_of_actor_orbit_quotient_two D
    (source_a5_original_actor_quotient_two_of_centralizer_eq_bot D e hn ht htn hc)

local instance originalCentralizerPassageElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The actual centralizer and separated seed conclude the original source consumer. -/
theorem source_a5_original_irreducible_of_actor_pair_centralizer_eq_bot
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hc : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) = ⊥) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_separated_seed D hn ht htn e
    (source_a5_full_eq_local_of_actor_pair_centralizer_eq_bot D e hn ht htn hc) hsep

end CFSG.Quasithin.Chapter10
