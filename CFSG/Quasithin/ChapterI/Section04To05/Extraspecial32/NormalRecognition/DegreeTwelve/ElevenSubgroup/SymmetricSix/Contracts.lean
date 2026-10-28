module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.Inputs

/-!
# The two local steps in the marked symmetric-six construction

`CommutingCubicData` is the conclusion of Lemma 4.5, including its final
centralizer-order observation. `CoxeterGluingData` records the remaining local
calculation of Lemma 4.6: the middle reflection joins the two rank-three
parabolics. Neither contract asserts that its witnesses exist.

The consumer proves all other Coxeter relations from the cubic actions,
excludes collapse of the presentation, and constructs the marked isomorphism.
In the source the middle reflection is `au`, where
`⟨a⟩ = C_[A(z),X](u)`. The two braid identities and the generation equality
must be proved from that local geometry; no symmetric-group isomorphism is
part of this input.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.5–4.6, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The commuting cubic and its selected involution, before the construction
of the symmetric subgroup. -/
public structure CommutingCubicData (h : Hypotheses z) (a : SourceGeometry h) where
  u : G
  u_choice : u = a.u ∨ u = a.u * z
  u_order : orderOf u = 2
  u_fused : IsConj z u
  X1 : Subgroup G
  card_X1 : Nat.card X1 = 3
  X1_centralizes_X : X1 ≤ centralizer (cubicInG h : Set G)
  z_inverts_X1 : ∀ x ∈ X1, z * x * z⁻¹ = x⁻¹
  u_centralizes_X1 : ∀ x ∈ X1, u * x = x * u
  centralizer_X_card : Nat.card (centralizer (cubicInG h : Set G)) = 18 ∨
    Nat.card (centralizer (cubicInG h : Set G)) = 54

/-- The five source reflections, indexed in diagram order. -/
@[expose] public def sourceChain (z u x x1 v : G) : Fin 5 → G :=
  ![z, x1 * z, v, u * x, u]

/-- The nonformal local gluing step of 4.6. The cubic generators and the
middle reflection are actual elements of the ambient group. -/
public structure CoxeterGluingData {h : Hypotheses z} {a : SourceGeometry h}
    (c : CommutingCubicData h a) where
  x : G
  x_generator : zpowers x = cubicInG h
  x1 : G
  x1_generator : zpowers x1 = c.X1
  v : G
  v_sq : v * v = 1
  v_commutes_z : Commute v z
  v_commutes_u : Commute v c.u
  left_braid : ((x1 * z) * v) ^ 3 = 1
  right_braid : (v * (c.u * x)) ^ 3 = 1
  generated : closure (Set.range (sourceChain z c.u x x1 v)) =
    fusionCore z ⊔ fusionCore c.u ⊔ cubicInG h ⊔ c.X1

public theorem cubicInG_card (h : Hypotheses z) : Nat.card (cubicInG h) = 3 := by
  rw [cubicInG, card_map_of_injective (Centralizer z).subtype_injective,
    h.sylow_three_card]

public theorem cubicInG_le (h : Hypotheses z) : cubicInG h ≤ Centralizer z :=
  map_subtype_le _

public theorem CommutingCubicData.u_commutes_z {h : Hypotheses z}
    {a : SourceGeometry h} (c : CommutingCubicData h a) : Commute c.u z := by
  have hu : Commute a.u z := mem_centralizer_singleton_iff.mp a.u_centralizes
  rcases c.u_choice with he | he
  · exact he ▸ hu
  · rw [he]
    exact hu.mul_left (Commute.refl z)

public theorem CommutingCubicData.u_inverts_X {h : Hypotheses z}
    {a : SourceGeometry h} (c : CommutingCubicData h a) (x : G)
    (hx : x ∈ cubicInG h) : c.u * x * c.u⁻¹ = x⁻¹ := by
  have ha : a.u * x * a.u⁻¹ = x⁻¹ := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact a.u_inverts_X ⟨y, hy⟩
  have hz : z * x * z⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (cubicInG_le h hx)).symm
  rcases c.u_choice with he | he
  · simpa only [he] using ha
  · rw [he]
    calc
      (a.u * z) * x * (a.u * z)⁻¹ = a.u * (z * x * z⁻¹) * a.u⁻¹ := by group
      _ = x⁻¹ := by rw [hz, ha]

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
