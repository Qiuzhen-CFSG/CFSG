module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Geometry
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Fusion
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Fusion separation by the three ambient centralizer orders

Conjugate elements have isomorphic ambient centralizers. Consequently the
three different two-parts in 12.1.5 separate the H.9 classes. Lifting the
H.9 conjugator then gives the literal normalizer-fusion equality.

The order estimates are explicit source obligations: this module does not
infer ambient Sylow control from a Sylow of a normalizer centralizer.
Source: Aschbacher--Smith 12.1.5, printed p.791.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The order of a Sylow two-subgroup of the full ambient point centralizer. -/
def centralizerTwoPart (_B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G)) : ℕ :=
  2 ^ (Nat.card (centralizer ({(w : G)} : Set G))).factorization 2

/-- The three numerical conclusions used in the proof of 12.1.5(2). -/
structure CentralizerOrders : Prop where
  pure : ∀ w, B.IsPureVector w → 2 * B.centralizerTwoPart w = Nat.card T
  diagonal : ∀ w, B.IsSingularDiagonal w → B.centralizerTwoPart w = Nat.card T
  nonsingular : ∀ w, B.quadratic (Additive.ofMul w) = 1 →
    2 * B.centralizerTwoPart w < Nat.card T

omit [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
theorem centralizerTwoPart_conj (w u : componentOrbit V (T : Subgroup G))
    (g : G) (he : (MulAut.conj g) (w : G) = (u : G)) :
    B.centralizerTwoPart w = B.centralizerTwoPart u := by
  have hc := Nat.card_congr
    ((centralizer ({(w : G)} : Set G)).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv
  rw [map_centralizer_singleton, he] at hc
  simp only [centralizerTwoPart, hc]

/-- A pure vector cannot fuse to either of the other two H.9 classes. -/
theorem pure_conjugate_of_centralizerOrders (ho : B.CentralizerOrders)
    (w u : componentOrbit V (T : Subgroup G)) (hw : B.IsPureVector w)
    (g : G) (he : (MulAut.conj g) (w : G) = (u : G)) : B.IsPureVector u := by
  have hu : u ≠ 1 := by
    intro hu
    apply hw.1
    apply Subtype.ext
    apply (MulAut.conj g).injective
    simpa [hu] using he
  refine ⟨hu, ?_⟩
  by_contra hp
  have hp' := not_or.mp hp
  have hc := B.centralizerTwoPart_conj w u g he
  have hwc := ho.pure w hw
  have hq : ∀ q : ZMod 2, q = 0 ∨ q = 1 := by decide
  rcases hq (B.quadratic (Additive.ofMul u)) with hq | hq
  · have huc := ho.diagonal u ⟨hp'.1, hp'.2, hq⟩
    have hpos : 0 < B.centralizerTwoPart w := pow_pos (by decide) _
    omega
  · have huc := ho.nonsingular u hq
    omega

/-- The actual normalizer-fusion conclusion, with the numerical source
premises still displayed separately. -/
theorem pureFusion_of_centralizerOrders (S : B.SourceModel)
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (ho : B.CentralizerOrders) : B.PureFusion := by
  intro w hw hp
  ext y
  constructor
  · rintro ⟨hy, g, hg⟩
    let u : componentOrbit V (T : Subgroup G) := ⟨y, hy⟩
    have hw' : B.IsPureVector w := ⟨hw, Or.inl hp⟩
    have hu := B.pure_conjugate_of_centralizerOrders ho w u hw' g hg
    obtain ⟨m, hm, he⟩ := (S.ambient_orbit_iff w u hw hu.1).mpr (Or.inl ⟨hw', hu⟩)
    exact ⟨m, hNM.symm ▸ hm, he⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨?_, m, rfl⟩
    have hmem := mem_map_of_mem (MulAut.conj m).toMonoidHom w.property
    have heq : (componentOrbit V (T : Subgroup G)).map (MulAut.conj m).toMonoidHom =
        componentOrbit V (T : Subgroup G) := mem_normalizer_iff_map_conj_eq.mp hm
    rwa [heq] at hmem

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
