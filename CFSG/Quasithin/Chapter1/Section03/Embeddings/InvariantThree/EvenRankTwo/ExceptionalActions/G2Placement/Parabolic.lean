module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.GroupTheory.SolvableSmallThreeCore
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint

/-!
# Proper-parabolic containment of the G₂ Sylow three-complement pair

Permutability makes the actual join RS a solvable {2,3}-group. Its three-core
has order at most 27, and its order is divisible by 64 because the G₂ Sylow
two-subgroup has order q⁶. The small-core argument gives O₂(RS) ≠ 1.
Its full normalizer fixes a vertex of the concrete octonion hexagon, placing
RS in a conjugate of one of the two root-defined parabolics.

Both parabolics are proper: they normalize nontrivial two-subgroups, whereas
the model transported from PairInput has trivial two-core. Borel containment
is a separate rank-one argument inside these parabolics.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528). No use is made of A.3.15's restriction p > 3. The concrete
hexagon is from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.EvenLocal.NormalizerCover
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
variable {Q F : Type*} [Group Q] [Finite Q] [Field F] [Finite F] [CharP F 2]
variable {S : Sylow 2 Q} {R : Subgroup Q}

/-- The actual product RS has a nontrivial normal two-subgroup. -/
theorem g2_product_twoCore_ne_bot (h : PairInput S R) (e : Q ≃* Model F) :
    pCore 2 (R ⊔ (S : Subgroup Q) : Subgroup Q) ≠ ⊥ := by
  let H := R ⊔ (S : Subgroup Q)
  have hthree : Nat.card (pCore 3 H) ≤ 27 := by
    have hd := (pCore 3 H).card_subgroup_dvd_card
    change Nat.card (pCore 3 H) ∣ Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q) at hd
    rw [product_card h] at hd
    have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      (pCore 3 H) (S : Subgroup Q) pCore_isPGroup S.isPGroup'
    have hdiv := hcop.dvd_of_dvd_mul_right hd
    have hR : Nat.card R ≤ 27 := by
      rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> decide
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans hR
  have hS : Nat.card S = Nat.card F ^ 6 := by
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hm : Nat.card T = Nat.card S := card_map_of_injective e.injective
    rw [← hm, Nat.card_congr (T.equiv (sylow (F := F))).toEquiv]
    exact card_unipotent
  have h64 : 64 ∣ Nat.card H := by
    change 64 ∣ Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q)
    rw [product_card h, hS]
    apply dvd_mul_of_dvd_right
    obtain ⟨n, hn, hc⟩ := field_card (F := F)
    have hd : 2 ∣ Nat.card F := by
      rw [hc]
      exact dvd_pow_self 2 (by omega : n ≠ 0)
    exact pow_dvd_pow_of_dvd hd 6
  exact twoCore_ne_bot_of_solvable_small_three_core (product_solvable h)
    (fun p hp hd => product_prime_divisors h hp hd) hthree h64

/-- Hexagon geometry places the actual product, with both factors, in a parabolic. -/
theorem g2_product_parabolic (h : PairInput S R) (e : Q ≃* Model F) :
    ∃ e' : Q ≃* Model F,
      (R ⊔ (S : Subgroup Q)).map e'.toMonoidHom ≤ parabolic₁ ∨
      (R ⊔ (S : Subgroup Q)).map e'.toMonoidHom ≤ parabolic₂ := by
  let H := R ⊔ (S : Subgroup Q)
  let N := (pCore 2 H).map H.subtype
  let M := N.map e.toMonoidHom
  have hN : N ≠ ⊥ := by
    intro heq
    exact g2_product_twoCore_ne_bot h e
      (((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp heq)
  have hM : M ≠ ⊥ := by
    intro heq
    exact hN ((N.map_eq_bot_iff_of_injective e.injective).mp heq)
  have hpM : IsPGroup 2 M := (pCore_isPGroup.map H.subtype).map e.toMonoidHom
  have hHN : H ≤ normalizer (N : Set Q) := by
    have hh := (pCore 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hHM : H.map e.toMonoidHom ≤ normalizer (M : Set (Model F)) := by
    simpa only [map_equiv_normalizer_eq] using map_mono (f := e.toMonoidHom) hHN
  obtain ⟨v, hv⟩ := normalizer_fixed_vertex_of_fixed_edge
    OctonionHexagon.hexagonData M hM hpM (exists_fixed_edge M hpM)
  obtain ⟨g, hg | hg⟩ := normalizer_conjugate_le_of_fixed_vertex M v hv
  · refine ⟨e.trans (MulAut.conj g), Or.inl ?_⟩
    change H.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [← map_map]
    exact (map_mono hHM).trans hg
  · refine ⟨e.trans (MulAut.conj g), Or.inr ?_⟩
    change H.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [← map_map]
    exact (map_mono hHM).trans hg


private theorem normalizer_ne_top_of_twoCore_eq_bot {G : Type*} [Group G]
    (hcore : pCore 2 G = ⊥) (N : Subgroup G) (hp : IsPGroup 2 N)
    (hN : Nat.card N ≠ 1) : normalizer (N : Set G) ≠ ⊤ := by
  intro ht
  have hn := normalizer_eq_top_iff.mp ht
  have hle : N ≤ pCore 2 G := le_sSup ⟨hn, hp⟩
  rw [hcore] at hle
  exact hN (by rw [le_bot_iff.mp hle, card_bot])

omit [Finite Q] in
/-- The two standard parabolics are proper for a model satisfying the pair inputs. -/
theorem g2_parabolics_proper (h : PairInput S R) (e : Q ≃* Model F) :
    parabolic₁ (F := F) ≠ ⊤ ∧ parabolic₂ (F := F) ≠ ⊤ := by
  have hcore : pCore 2 (Model F) = ⊥ := by
    rw [← pCore_map_iso 2 e, h.twoCore, Subgroup.map_bot]
  obtain ⟨n, hn, hc⟩ := field_card (F := F)
  have hh : IsPGroup 2 (highestRoot (F := F)) :=
    IsPGroup.of_card (n := n) (by rw [card_highestRoot, hc])
  have hl : IsPGroup 2 (longRootLocal (F := F)) :=
    IsPGroup.of_card (n := n * 2) (by rw [card_longRootLocal, hc, pow_mul])
  constructor
  · rw [← SylowParabolicInvariance.normalizer_highestRoot]
    apply normalizer_ne_top_of_twoCore_eq_bot hcore _ hh
    rw [card_highestRoot]
    exact ne_of_gt Finite.one_lt_card
  · rw [← SylowParabolicInvariance.normalizer_longRootLocal]
    apply normalizer_ne_top_of_twoCore_eq_bot hcore _ hl
    rw [card_longRootLocal]
    exact ne_of_gt (one_lt_pow₀ Finite.one_lt_card (by decide : 2 ≠ 0))

/-- Properness and containment refer to the same actual model parabolic. -/
theorem g2_product_proper_parabolic (h : PairInput S R) (e : Q ≃* Model F) :
    ∃ (e' : Q ≃* Model F) (P : Subgroup (Model F)),
      (P = parabolic₁ ∨ P = parabolic₂) ∧ P ≠ ⊤ ∧
      (R ⊔ (S : Subgroup Q)).map e'.toMonoidHom ≤ P := by
  obtain ⟨e', he | he⟩ := g2_product_parabolic h e
  · exact ⟨e', parabolic₁, Or.inl rfl, (g2_parabolics_proper h e).1, he⟩
  · exact ⟨e', parabolic₂, Or.inr rfl, (g2_parabolics_proper h e).2, he⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
