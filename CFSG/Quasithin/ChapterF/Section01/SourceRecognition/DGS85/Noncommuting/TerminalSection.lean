module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.IntersectionIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CriticalFixedLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusSectionGeneration

/-!
# The final fixed-space upper bound

Transport of the radius/core intersection bounds the last radius-one
intersection index by the actual actor image order. The two radius
commutator identities place the mutual commutator in the complementary
neighbor center and the opposite core, whose intersection is trivial.
Literal section coordinates therefore give the fixed-space upper bound;
the radius-two calculation also proves quadraticity for the same actor.

Source: DGS, *Groups and Graphs* (1985), (7.5), printed p.131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_radius_commutator_of_type (h : LocallyRankOneTriple P B)
    {u a : Vertex (family P)} (ht : u.type = a.type)
    (hc : ⁅V (family P) u 1,Q (family P) u⁆ = Z (family P) u) :
    ⁅V (family P) a 1,Q (family P) a⁆ = Z (family P) a := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) u a).mpr ht
  rw [V_translate,Q_translate,Z_translate,←map_commutator,hc]

theorem graph_epsilonTwo_terminal_intersection_centralizes
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t a y x : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hva : (graph (family P)).Adj v a) (hua : u ≠ a)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hb : 4 < b (family P))
    (hty : (graph (family P)).Adj t y) (hyx : (graph (family P)).Adj y x)
    (hdx : (graph (family P)).dist v x + 3 = b (family P)) :
    ⁅V (family P) a 1,V (family P) t 1 ⊓ V (family P) x 1⁆ = ⊥ := by
  have hid := graph_epsilonTwo_critical_centers h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hdu hdt hepsilon hnat₀ hnat₁
  have hdis := graph_epsilonTwo_other_center_disjoint_core h hB L d hstar hodd hdich
    hc hne hvu hva hua hepsilon hnat₀ hid.1
  have hua' : u.type = a.type := by
    have hu := hvu.1
    have ha := hva.1
    cases hv : v.type <;> cases hu' : u.type <;> cases ha' : a.type <;> simp_all
  have htx : t.type = x.type := by
    have ht := hty.1
    have hx := hyx.1
    cases ht' : t.type <;> cases hy : y.type <;> cases hx' : x.type <;> simp_all
  have hAa := graph_radius_commutator_of_type h hua' hid.2.2.1
  have hXx := graph_radius_commutator_of_type h htx hid.2.2.2
  have hav : (graph (family P)).dist a v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hva.symm
  have hax := (connected_graph h).dist_triangle (u := a) (v := v) (w := x)
  have hAX : V (family P) a 1 ≤ Q (family P) x :=
    graph_V_le_Q_of_distance h hS (by omega)
  have hXA : V (family P) x 1 ≤ Q (family P) a :=
    graph_V_le_Q_of_distance h hS (by rw [SimpleGraph.dist_comm]; omega)
  have hxy : (graph (family P)).dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyx.symm
  have hyt : (graph (family P)).dist y t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hty.symm
  have htw : (graph (family P)).dist t w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwt.symm
  have hxw : (graph (family P)).dist x w < b (family P) := by
    have h₁ := (connected_graph h).dist_triangle (u := x) (v := y) (w := t)
    have h₂ := (connected_graph h).dist_triangle (u := x) (v := t) (w := w)
    omega
  apply bot_unique
  rw [←hdis]
  apply le_inf
  · exact (commutator_mono le_rfl (inf_le_right.trans hXA)).trans hAa.le
  · have he : ⁅V (family P) a 1,V (family P) t 1 ⊓ V (family P) x 1⁆ ≤
        Z (family P) x := by
      rw [commutator_comm]
      exact (commutator_mono inf_le_right hAX).trans hXx.le
    exact he.trans (graph_Z_le_Q_of_short h hS hxw)

theorem graph_epsilonTwo_terminal_section_bound
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t a y x : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hva : (graph (family P)).Adj v a) (hua : u ≠ a)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hb : 4 < b (family P))
    (hty : (graph (family P)).Adj t y) (hyx : (graph (family P)).Adj y x)
    (hdx : (graph (family P)).dist v x + 3 = b (family P))
    (hcore : V (family P) v 2 ≤ Q (family P) y)
    [((Q (family P) t).subgroupOf (d t y hty).Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar) W)
    (s : BinaryConjugationSection (d t y hty).Pstar (V (family P) t 1) (Z (family P) t)
      (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar)))) :
    V (family P) a 1 ≤ (d t y hty).Pstar ∧
      IsQuadratic σ (((V (family P) a 1).subgroupOf (d t y hty).Pstar).map
        (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar))) ∧
      Nat.card (W ⧸ fixedSpace σ (((V (family P) a 1).subgroupOf (d t y hty).Pstar).map
        (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar)))) ≤
      Nat.card (((V (family P) a 1).subgroupOf (d t y hty).Pstar).map
        (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar))) := by
  let := finite_endpoints h
  have hVL := (graph_radius_two_quadratic_section h hS hty hdt hb hcore (d t y hty)
    (by rw [hstar]; exact hodd t) σ s).1
  have hAV := graph_V_adjacent_le hva 1
  have hAL := hAV.trans hVL
  let : Finite (V (family P) a 1) := Finite.of_injective
    (inclusion ((graph_V_le_Q_of_short h hS a (by omega : 1 < b (family P))).trans
      (pCoreIn_le 2 (stabilizer (family P) a)))) (inclusion_injective _)
  let : Finite (V (family P) t 1) := Finite.of_injective
    (inclusion ((graph_V_le_Q_of_short h hS t (by omega : 1 < b (family P))).trans
      (pCoreIn_le 2 (stabilizer (family P) t)))) (inclusion_injective _)
  refine ⟨hAL,?_,?_⟩
  · apply isQuadratic_of_triple_commutator_le _ _ _ _ σ _ s
    exact ((commutator_mono hAV (commutator_mono hAV le_rfl)).trans
      (graph_radius_two_triple_commutator h hS hdt hb).le).trans bot_le
  · have hc' := graph_epsilonTwo_terminal_intersection_centralizes h hB hS L hcov d hstar
      hodd hdich hob hc hne hvu hwt hva hua hdu hdt hepsilon hnat₀ hnat₁ hb hty hyx hdx
    have hC : V (family P) t 1 ⊓ V (family P) x 1 ≤
        centralizer (V (family P) a 1 : Set G) := by
      rw [commutator_comm] at hc'
      exact commutator_eq_bot_iff_le_centralizer.mp hc'
    calc
      _ ≤ (centralizer (V (family P) a 1 : Set G)).relIndex (V (family P) t 1) :=
        fixed_quotient_card_le_centralizer_index σ _ s _
      _ ≤ (V (family P) t 1 ⊓ V (family P) x 1).relIndex (V (family P) t 1) :=
        relIndex_le_of_le_left hC index_ne_zero_of_finite
      _ = (V (family P) x 1).relIndex (V (family P) t 1) := inf_relIndex_left _ _
      _ ≤ (Q (family P) t).relIndex (V (family P) a 1) :=
        graph_epsilonTwo_radius_index_comparison h hB hS L hcov d hstar hodd hdich hob
          hc hne hvu hwt hva hua hdu hdt hepsilon hnat₀ hnat₁ hsyl (by omega) hty hyx
      _ = _ := (actor_image_card_eq_relIndex _ _ _ _ (QuotientGroup.ker_mk' _) hAL).symm

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
