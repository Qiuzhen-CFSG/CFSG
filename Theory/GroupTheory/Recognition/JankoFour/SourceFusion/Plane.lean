module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Normalizer
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.MarkedPlane

/-!
# The constructed pair plane in the original J4 radical

The three coordinate pairs on {0,1,2} give a concrete plane through t in
the unchanged Todd embedding. Its nonidentity elements belong to t's M-orbit.
The established native normalizer estimates and the exact conditional
intersection theorem therefore apply to this constructed subgroup: its
normalizer quotient has two-rank at most four, projected involutions have
128 fixed radical elements, and every proper overgroup in E has its
normalizer inside C_G(t) contained in C_M(t).

This supplies the inputs immediately preceding AS91's first standard
fixed-coset argument. It does not assume or assert its fixed-coset conclusion.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.3), p.602.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The original Todd embedding of the concrete coordinate triangle. -/
noncomputable def secondPlane (a : LocalData h) : Subgroup G :=
  (MathieuCode.J4Fusion.markedPairPlane.toAddSubgroup.toSubgroup).map a.P.vectorEmbedding

theorem secondPlane_le (a : LocalData h) : secondPlane a ≤ a.P.E := map_le_range _ _

theorem second_mem_secondPlane (a : LocalData h) : second a ∈ secondPlane a :=
  ⟨_,MathieuCode.J4Fusion.markedPairPlane_mem,rfl⟩

theorem secondPlane_card (a : LocalData h) : Nat.card (secondPlane a) = 4 := by
  rw [secondPlane,card_map_of_injective a.P.vectorEmbedding_injective]
  let e : MathieuCode.J4Fusion.markedPairPlane.toAddSubgroup.toSubgroup ≃
      MathieuCode.J4Fusion.markedPairPlane := {
    toFun := fun v => ⟨v.val.toAdd,v.property⟩
    invFun := fun v => ⟨Multiplicative.ofAdd v.val,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,MathieuCode.J4Fusion.markedPairPlane_card]

theorem secondPlane_orbit (a : LocalData h) (u : G) (hu : u ∈ secondPlane a) (hu1 : u ≠ 1) :
    ∃ m ∈ a.P.M, MulAut.conj m (second a) = u := by
  obtain ⟨v,hv,rfl⟩ := hu
  have hv0 : v.toAdd ≠ 0 := by
    intro he
    have hv1 : v=1 := congrArg Multiplicative.ofAdd he
    exact hu1 (hv1 ▸ map_one _)
  obtain ⟨B,hB⟩ := MathieuCode.J4Fusion.markedPairPlane_pairs v.toAdd hv hv0
  obtain ⟨g,hg⟩ := weightTwoOrbit_transitive ⟨{0,1},by decide⟩ B
  obtain ⟨m,hm⟩ := a.projection_surjective g
  refine ⟨m,m.property,?_⟩
  rw [second,vector_conj a.P m,hm,hg,←hB]
  rfl

/-- A constructed witness for every pair-plane input to the first standard
argument: order four, literal quotient rank, fixed centralizers, and the
normalizer barrier for every larger subgroup. Only (6.2)(3) is conditional. -/
theorem secondPlane_normalizer_facts (a : LocalData h) (hi : MarkerIntersection a) :
    secondPlane a ≤ a.P.E ∧ second a ∈ secondPlane a ∧ Nat.card (secondPlane a) = 4 ∧
    (∀ u ∈ secondPlane a, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) ∧
    a.P.E ≤ pairNormalizer a (secondPlane a) ∧
    primeRank 2 (pairNormalizer a (secondPlane a) ⧸
      a.P.E.subgroupOf (pairNormalizer a (secondPlane a))) ≤ 4 ∧
    (∀ m : pairNormalizer a (secondPlane a),
      orderOf (pairNormalizerProjection a (secondPlane a) m) = 2 →
      Nat.card (a.P.E ⊓ centralizer (m : G) : Subgroup G) = 128) ∧
    (∀ V : Subgroup G, secondPlane a < V → V ≤ a.P.E →
      normalizer (V : Set G) ⊓ centralizer (second a) ≤ secondCentralizer a) := by
  have hc : 2 < Nat.card (secondPlane a) := by rw [secondPlane_card]; decide
  exact ⟨secondPlane_le a,second_mem_secondPlane a,secondPlane_card a,secondPlane_orbit a,
    E_le_pairNormalizer a _ (secondPlane_le a),
    pairNormalizer_quotient_rank_le_four a _ (secondPlane_le a) (second_mem_secondPlane a)
      hc (secondPlane_orbit a),
    fun m ho => pairNormalizer_involution_centralizer_card a _ (secondPlane_le a)
      (second_mem_secondPlane a) hc (secondPlane_orbit a) m ho,
    fun V hV hVE => strict_pair_overgroup_normalizer_le a hi _ V hVE hV hc (secondPlane_orbit a)⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
