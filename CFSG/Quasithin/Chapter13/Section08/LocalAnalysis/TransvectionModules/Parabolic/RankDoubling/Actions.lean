module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.CommutingActions
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Actual quotient actions and orbit generation

K₂ normalizes U₂ and centralizes V₂, so its conjugation action descends to
the literal binary quotient. An index-two flag V₂ < V₃ selects a single
nonzero quotient direction. Its vector orbit spans exactly W. The defining
K₂-conjugate generation of U₂ also proves the generation condition used
by the two-coordinate decomposition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6, printed p.948. This supplies canonical actions and generation,
without assuming the missing extension to the source local S₃-action.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
variable {G : Type*} [Group G]
variable (H V V₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

private theorem K2_normalizes_V2 : Source.K2 H V₂ ≤ normalizer (V₂ : Set G) :=
  (Source.K2_le_centralizer H V₂).trans (inf_le_right.trans (centralizer_le_normalizer _))

noncomputable def quotientAction : Source.K2 H V₂ →* MulAut (Uhat H V V₂) :=
  (exists_quotient_conjugation_action (Source.K2 H V₂) (Source.U2 H V V₂) V₂
    (le_normalizer_conjugateSpanBy V (Source.K2 H V₂))
    (K2_normalizes_V2 H V₂) inferInstance).choose

omit [IsElementaryAbelian 2 V] in
theorem quotientAction_mk (k : Source.K2 H V₂) (u : Source.U2 H V V₂) :
    quotientAction H V V₂ k (QuotientGroup.mk' (V₂.subgroupOf (Source.U2 H V V₂)) u) =
      QuotientGroup.mk' (V₂.subgroupOf (Source.U2 H V V₂))
        ⟨(k : G) * (u : G) * (k : G)⁻¹,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V (Source.K2 H V₂)
            k.property) u).mp u.property⟩ :=
  (exists_quotient_conjugation_action (Source.K2 H V₂) (Source.U2 H V V₂) V₂
    (le_normalizer_conjugateSpanBy V (Source.K2 H V₂))
    (K2_normalizes_V2 H V₂) inferInstance).choose_spec k u

noncomputable def representation : Representation (ZMod 2) (Source.K2 H V₂)
    (Additive (Uhat H V V₂)) where
  toFun k := (quotientAction H V V₂ k).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext x
    change Additive.ofMul (quotientAction H V V₂ 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' a b := by
    ext x
    change Additive.ofMul (quotientAction H V V₂ (a * b) x.toMul) = _
    rw [map_mul]
    rfl

theorem representation_mk (k : Source.K2 H V₂) (u : Source.U2 H V V₂) :
    representation H V V₂ k (quotientMap H V V₂ (Additive.ofMul u)) =
      quotientMap H V V₂ (Additive.ofMul
        ⟨(k : G) * (u : G) * (k : G)⁻¹,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V (Source.K2 H V₂)
            k.property) u).mp u.property⟩) :=
  congrArg Additive.ofMul (quotientAction_mk H V V₂ k u)

/-- The image of a vector of V in the literal quotient. -/
@[expose] def seedVector (v : V) : Additive (Uhat H V V₂) :=
  quotientMap H V V₂ (Additive.ofMul ⟨v, Source.seed_le_U2 H V V₂ v.property⟩)

theorem W_eq_orbits (V₃ : Subgroup G) (h₃ : V₃ ≤ V) :
    W H V V₂ V₃ h₃ = Submodule.span (ZMod 2)
      {x | ∃ k : Source.K2 H V₂, ∃ v : V₃,
        x = representation H V V₂ k (seedVector H V V₂ ⟨v, h₃ v.property⟩)} := by
  unfold W
  congr 1
  ext x
  simp only [seedVector, representation_mk]

/-- The literal conjugate-span definition proves that the whole seed orbit spans U₂/V₂. -/
theorem W_seed_top : W H V V₂ V le_rfl = ⊤ := by
  rw [W_eq_image_span]
  apply top_unique
  intro x _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (V₂.subgroupOf (Source.U2 H V V₂)) x.toMul
  refine ⟨Additive.ofMul u, u.property, ?_⟩
  exact congrArg Additive.ofMul hu

/-- An index-two flag selects a single nonzero direction modulo V₂. -/
theorem exists_seed_direction (V₃ : Subgroup G) (h₃ : V₃ ≤ V)
    (hindex : V₂.relIndex V₃ = 2) :
    ∃ a : V₃, (a : G) ∉ V₂ ∧ ∀ b : V₃,
      seedVector H V V₂ ⟨b, h₃ b.property⟩ = 0 ∨
      seedVector H V V₂ ⟨b, h₃ b.property⟩ = seedVector H V V₂ ⟨a, h₃ a.property⟩ := by
  obtain ⟨a, ha, hnot, hcoset⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hindex
  refine ⟨⟨a,ha⟩, hnot, ?_⟩
  intro b
  rcases hcoset b b.property with hab | hb
  · right
    have hz : seedVector H V V₂ ⟨b, h₃ b.property⟩ + seedVector H V V₂ ⟨a, h₃ ha⟩ = 0 := by
      exact (QuotientGroup.eq_one_iff _).mpr hab
    have haa : seedVector H V V₂ ⟨a, h₃ ha⟩ + seedVector H V V₂ ⟨a, h₃ ha⟩ = 0 := by
      simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
        (add_smul (1 : ZMod 2) 1 (seedVector H V V₂ ⟨a, h₃ ha⟩)).symm
    exact add_right_cancel (hz.trans haa.symm)
  · exact Or.inl ((QuotientGroup.eq_one_iff _).mpr hb)

/-- Any nonzero vector of the one-dimensional quotient may be chosen as seed. -/
theorem seed_direction (V₃ : Subgroup G) (h₃ : V₃ ≤ V)
    (hindex : V₂.relIndex V₃ = 2) (a : V₃) (ha : (a : G) ∉ V₂) :
    ∀ b : V₃, seedVector H V V₂ ⟨b, h₃ b.property⟩ = 0 ∨
      seedVector H V V₂ ⟨b, h₃ b.property⟩ = seedVector H V V₂ ⟨a, h₃ a.property⟩ := by
  obtain ⟨a₀, _, hdir⟩ := exists_seed_direction H V V₂ V₃ h₃ hindex
  have he : seedVector H V V₂ ⟨a, h₃ a.property⟩ =
      seedVector H V V₂ ⟨a₀, h₃ a₀.property⟩ :=
    (hdir a).resolve_left (fun hz => ha ((quotientMap_eq_zero H V V₂
      (Additive.ofMul ⟨a, Source.seed_le_U2 H V V₂ (h₃ a.property)⟩)).mp hz))
  intro b
  exact (hdir b).imp id (fun hb => hb.trans he.symm)

/-- Quotienting the three-space by the two-space turns its orbit into a vector orbit. -/
theorem W_eq_orbitSpan (V₃ : Subgroup G) (h₃ : V₃ ≤ V) (a : V₃)
    (hdir : ∀ b : V₃, seedVector H V V₂ ⟨b, h₃ b.property⟩ = 0 ∨
      seedVector H V V₂ ⟨b, h₃ b.property⟩ = seedVector H V V₂ ⟨a, h₃ a.property⟩) :
    W H V V₂ V₃ h₃ = orbitSpan (representation H V V₂)
      (seedVector H V V₂ ⟨a, h₃ a.property⟩) := by
  rw [W_eq_orbits]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨k, b, rfl⟩
    rcases hdir b with hb | hb
    · rw [hb, map_zero]; exact Submodule.zero_mem _
    · rw [hb]; exact Submodule.subset_span ⟨k,rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k,a,rfl⟩

/-- A marked basis of V/V₂ supplies generation by the two directions used in doubling. -/
theorem orbit_pair_generates (v w : Additive (Uhat H V V₂))
    (hseed : ∀ b : V, seedVector H V V₂ b ∈ Submodule.span (ZMod 2) {v,w}) :
    Submodule.span (ZMod 2) {x | ∃ k : Source.K2 H V₂,
      x = representation H V V₂ k v ∨ x = representation H V V₂ k w} = ⊤ := by
  let S := Submodule.span (ZMod 2) {x | ∃ k : Source.K2 H V₂,
    x = representation H V V₂ k v ∨ x = representation H V V₂ k w}
  apply top_unique
  rw [← W_seed_top H V V₂, W_eq_orbits]
  apply Submodule.span_le.mpr
  rintro x ⟨k, b, rfl⟩
  have hle : Submodule.span (ZMod 2) {v,w} ≤
      S.comap (representation H V V₂ k) := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact Submodule.subset_span ⟨k, Or.inl rfl⟩
    · have he : z = w := Set.mem_singleton_iff.mp hz
      subst z
      exact Submodule.subset_span ⟨k, Or.inr rfl⟩
  exact hle (hseed ⟨b, b.property⟩)

/-- Local action facts still to be constructed from G.2.2 and the marked source flag.
There is no dimension or decomposition in these data. The K₂-action is canonical. -/
structure LocalDoublingAction (V₃ : Subgroup G) (h₃ : V₃ ≤ V) (a : V₃) where
  symmetric : Representation F InvertedCubicTensor.S₃ (Additive (Uhat H V V₂))
  commutes : ∀ k x, symmetric InvertedCubicTensor.cubic (representation H V V₂ k x) =
    representation H V V₂ k (symmetric InvertedCubicTensor.cubic x)
  seed_polynomial : symmetric InvertedCubicTensor.cubic
      (symmetric InvertedCubicTensor.cubic (seedVector H V V₂ ⟨a,h₃ a.property⟩)) =
    seedVector H V V₂ ⟨a,h₃ a.property⟩ +
      symmetric InvertedCubicTensor.cubic (seedVector H V V₂ ⟨a,h₃ a.property⟩)
  fixes_orbit : ∀ k, symmetric InvertedCubicTensor.inverter
      (representation H V V₂ k (seedVector H V V₂ ⟨a,h₃ a.property⟩)) =
    representation H V V₂ k (seedVector H V V₂ ⟨a,h₃ a.property⟩)
  seed_plane : ∀ b : V, seedVector H V V₂ b ∈ Submodule.span F
    {seedVector H V V₂ ⟨a,h₃ a.property⟩,
      symmetric InvertedCubicTensor.cubic (seedVector H V V₂ ⟨a,h₃ a.property⟩)}

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
