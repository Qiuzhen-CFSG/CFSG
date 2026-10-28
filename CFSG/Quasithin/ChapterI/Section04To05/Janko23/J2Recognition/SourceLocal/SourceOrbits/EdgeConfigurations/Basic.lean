module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Completion

/-!
# The literal edge intersections and triple centralizers

We use left conjugation throughout. For g in N_G(X), the conjugate of
F = G_{X,Y} is exactly G_{X,gY}; hence F ∩ Fᵍ is the centralizer of the
triple join when F is A₅. This retains the actual subgroup inclusion,
which is needed both by the local model calculations and by Cauchy's
construction of an involution in the distinguished source class.

The three sets below are the X-orbit of Y and the two source double-coset
sets. Their neighbor cover follows from 47.5; it does not assume their
sizes, their join types, or their transitivity under F ⊔ X.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6, pp.263–264.
-/

@[expose] public section

open Subgroup MulAction
open scoped Pointwise
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G]

abbrev fixer (D : Seed G) (Y : D.Vertex) := edgeFixer G D.base Y
abbrev actor (D : Seed G) (Y : D.Vertex) := fixer D Y ⊔ D.X
abbrev localCentralizer (D : Seed G) := centralizer (D.X : Set G)
abbrev localNormalizer (D : Seed G) := normalizer (D.X : Set G)

/-- The conjugate used here is g F g⁻¹, matching the existing left action. -/
def intersection (D : Seed G) (Y : D.Vertex) (g : G) : Subgroup G :=
  fixer D Y ⊓ (fixer D Y).map (MulAut.conj g).toMonoidHom

def innerSet (D : Seed G) (Y : D.Vertex) : Set D.Vertex :=
  {U | ∃ g : G, g ∈ localCentralizer D ∧ g ∉ actor D Y ∧ g • Y = U}

def outerSet (D : Seed G) (Y : D.Vertex) : Set D.Vertex :=
  {U | ∃ g : G, g ∈ localNormalizer D ∧ g ∉ localCentralizer D ∧ g • Y = U}

def endpointOrbit (D : Seed G) (Y : D.Vertex) : Set D.Vertex := orbit D.X Y

/-- Conjugating both point stabilizers retains the actual ambient map. -/
theorem map_fixer (D : Seed G) (Y : D.Vertex) (g : localNormalizer D) :
    (fixer D Y).map (MulAut.conj (g : G)).toMonoidHom =
      edgeFixer G D.base ((g : G) • Y) := by
  rw [fixer, edgeFixer, map_inf _ _ _ (MulAut.conj (g : G)).injective,
    ← stabilizer_smul_eq_stabilizer_map_conj,
    ← stabilizer_smul_eq_stabilizer_map_conj, normalizer_fixes_base]
  rfl

/-- The pointwise fixer centralizes X, not merely normalizes it. -/
theorem fixer_le_localCentralizer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    fixer D Y ≤ localCentralizer D := by
  rw [fixer, edgeFixer_eq_centralizer_join_of_alternatingFive D D.base Y hF]
  exact centralizer_le (show D.X ≤ D.X ⊔ Y.val from le_sup_left)

/-- The source intersection is the full centralizer of the literal triple. -/
theorem intersection_eq_triple_centralizer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (g : localNormalizer D) :
    intersection D Y g = centralizer ((D.X ⊔ Y.val ⊔ ((g : G) • Y).val : Subgroup G) : Set G) := by
  have hFg : Nonempty (edgeFixer G D.base ((g : G) • Y) ≃* alternatingGroup (Fin 5)) :=
    ⟨(MulEquiv.subgroupCongr (map_fixer D Y g).symm).trans
      (((fixer D Y).equivMapOfInjective (MulAut.conj (g : G)).toMonoidHom
        (MulAut.conj (g : G)).injective).symm.trans hF.some)⟩
  have h₁ := edgeFixer_eq_centralizer_join_of_alternatingFive D D.base Y hF
  have h₂ := edgeFixer_eq_centralizer_join_of_alternatingFive D D.base ((g : G) • Y) hFg
  rw [intersection, map_fixer, h₂, show fixer D Y = _ from h₁]
  apply le_antisymm
  · apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_left
    · exact le_centralizer_iff.mp
        (inf_le_right.trans (centralizer_le
          (show ((g : G) • Y).val ≤ D.X ⊔ ((g : G) • Y).val from le_sup_right)))
  · exact le_inf (centralizer_le
      (show D.X ⊔ Y.val ≤ D.X ⊔ Y.val ⊔ ((g : G) • Y).val from le_sup_left))
      (centralizer_le (show D.X ⊔ ((g : G) • Y).val ≤
        D.X ⊔ Y.val ⊔ ((g : G) • Y).val from
        sup_le (le_sup_left.trans le_sup_left) le_sup_right))

/-- Every subgroup of the intersection retains its embedding in the triple
centralizer; this is the containment used with O₂(A₄) and D₁₀ in the source. -/
theorem triple_le_centralizer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (g : localNormalizer D) (B : Subgroup G) (hB : B ≤ intersection D Y g) :
    D.X ⊔ Y.val ⊔ ((g : G) • Y).val ≤ centralizer (B : Set G) := by
  apply le_centralizer_iff.mp
  rwa [intersection_eq_triple_centralizer D Y hF g] at hB

/-- Even order of the actual intersection constructs a source-class involution;
no assertion about an abstract isomorphism is substituted for the embedding. -/
theorem commonInvolution_of_even_intersection (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localNormalizer D) (heven : 2 ∣ Nat.card (intersection D Y g)) :
    ∃ t : G, IsConj D.z t ∧
      D.X ⊔ Y.val ⊔ ((g : G) • Y).val ≤ involutionCentralizer t := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := intersection D Y g) 2 heven
  have ho : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hc : (t : G) ∈ centralizer
      ((D.X ⊔ Y.val ⊔ ((g : G) • Y).val : Subgroup G) : Set G) := by
    rw [← intersection_eq_triple_centralizer D Y hF g]
    exact t.property
  exact ⟨t, hclass t t.property.1 ho, fun u hu =>
    mem_centralizer_singleton_iff.mpr (hc u hu)⟩

/-- The base point and every vertex contained in the endpoint join already
have a common source-class involution. In particular this closes U = X. -/
theorem commonInvolution_of_le_join (D : Seed G) (Y U : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (hU : U.val ≤ D.X ⊔ Y.val) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  have hc : Nat.card (fixer D Y) = 60 := by
    rw [Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fixer D Y) 2 (by rw [hc]; norm_num)
  have ho : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hcentral : (t : G) ∈ centralizer ((D.X ⊔ Y.val : Subgroup G) : Set G) := by
    change (t : G) ∈ centralizer ((D.base.val ⊔ Y.val : Subgroup G) : Set G)
    rw [← edgeFixer_eq_centralizer_join_of_alternatingFive D D.base Y hF]
    exact t.property
  refine ⟨t, hclass t t.property ho, ?_⟩
  rw [sup_eq_left.mpr hU]
  exact fun u hu => mem_centralizer_singleton_iff.mpr (hcentral u hu)

/-- The F ⊔ X orbit of Y is already its X orbit: F centralizes X and fixes Y. -/
theorem actor_orbit_eq_endpointOrbit (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    orbit (actor D Y) Y = endpointOrbit D Y := by
  ext U
  constructor
  · rintro ⟨g, rfl⟩
    have hg := g.property
    have hFN : fixer D Y ≤ normalizer (D.X : Set G) :=
      (fixer_le_localCentralizer D Y hF).trans (centralizer_le_normalizer _)
    change (g : G) ∈ ((fixer D Y ⊔ D.X : Subgroup G) : Set G) at hg
    rw [coe_mul_of_left_le_normalizer_right _ _ hFN] at hg
    obtain ⟨f, hf, x, hx, hfx⟩ := hg
    change f * x = (g : G) at hfx
    refine ⟨⟨x, hx⟩, ?_⟩
    have hcomm : x * f = f * x := fixer_le_localCentralizer D Y hF hf x hx
    have hfix : f • Y = Y := hf.2
    change x • Y = (g : G) • Y
    rw [← hfx, ← hcomm, mul_smul, hfix]
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, (le_sup_right : D.X ≤ actor D Y) x.property⟩, rfl⟩

/-- The three endpoint-orbit vertices lie in the literal A₄ join. -/
theorem endpointOrbit_le_join (D : Seed G) (Y U : D.Vertex)
    (hU : U ∈ endpointOrbit D Y) : U.val ≤ D.X ⊔ Y.val := by
  obtain ⟨x, rfl⟩ := hU
  exact conj_smul_le_of_le (show Y.val ≤ D.X ⊔ Y.val from le_sup_right)
    (⟨x, (le_sup_left : D.X ≤ D.X ⊔ Y.val) x.property⟩ : ↥(D.X ⊔ Y.val))

/-- The genuine 47.5 transitivity covers the neighbors by the three literal
conjugating-element ranges. Sizes and pair types remain to be calculated. -/
theorem neighbor_cover (D : Seed G) (R : FourSuborbits D) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (U : D.Vertex) (hU : D.graph.Adj D.base U) :
    U ∈ endpointOrbit D Y ∨ U ∈ innerSet D Y ∨ U ∈ outerSet D Y := by
  classical
  obtain ⟨g, hg⟩ := R.neighbors Y hY U hU
  by_cases hL : (g : G) ∈ localCentralizer D
  · by_cases hA : (g : G) ∈ actor D Y
    · left
      rw [← actor_orbit_eq_endpointOrbit D Y hF]
      exact ⟨⟨g, hA⟩, hg⟩
    · exact Or.inr (Or.inl ⟨g, hL, hA, hg⟩)
  · exact Or.inr (Or.inr ⟨g, g.property, hL, hg⟩)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
