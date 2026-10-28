module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Definitions
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.Data.Set.Card
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Counts, local cores and D4 for the actual intersection geometry

For the source configuration, inclusion–exclusion gives thirteen conjugates
of z in Q. The product-order formula proves Q = EF; normalizing E and F
therefore has intersection H. This identifies the chamber with the specified
Sylow subgroup of H. The literal vertex orders then prove the Sylow condition.

The proved trivial two-cores of PSL₃(2) and S₃ × S₃ identify the three vertex
cores. Quotient transport uses the actual inclusions of the normalizers into
L. A normal subgroup in the chamber lies in E ∩ F = ⟨z⟩; if nontrivial, it
would force L to centralize z. The order of N_G(E) excludes this. Thus D4 does
not require recognition of L or an ambient simplicity assumption.

`configuration_system` remains conditional on the configuration construction
and the three parabolic identifications. Their existence is separate work.
Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 3.1–3.2, printed pp.36–37.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

variable {G : Type*} [Group G] [Finite G] {z g : G}

omit [Finite G] in
/-- Relative normality of E in H gives the literal normalizer containment. -/
theorem intersection_centralizer_le_normalizer (d : IntersectionData z g) :
    Centralizer z ≤ normalizer (coreIntersection z g : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    ((coreIntersection_le z g).trans (coreInG_le z))).mp d.normal_in_centralizer

omit [Finite G] in
/-- The elementary-eight kernel and the PSL₃(2) quotient give order 1344. -/
theorem intersection_normalizer_card (d : IntersectionData z g) :
    Nat.card (normalizer (coreIntersection z g : Set G)) = 1344 := by
  rw [card_eq_card_quotient_mul_card_subgroup
    ((coreIntersection z g).subgroupOf (normalizer (coreIntersection z g : Set G))),
    Nat.card_congr d.normalizer_quotient.some.toEquiv, Matrix.PSL3Two.card_PSL,
    Nat.card_congr (subgroupOfEquivOfLe (coreIntersection z g).le_normalizer).toEquiv,
    d.card]

/-- The endpoint normalizer contains elements moving the distinguished involution. -/
theorem intersection_normalizer_not_le (h : Hypotheses z) (d : IntersectionData z g) :
    ¬ normalizer (coreIntersection z g : Set G) ≤ Centralizer z := by
  intro hle
  have hc := card_le_of_le hle
  rw [intersection_normalizer_card d, h.centralizer_card] at hc
  omega

/-- Inclusion–exclusion on E# ∪ F# gives the source fusion count. -/
theorem configuration_fusion_card (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) : Nat.card (CoreFusion z) = 13 := by
  let E := coreIntersection z g
  let F := coreIntersection z c.y
  have hu := Set.ncard_union_add_ncard_inter (E : Set G) (F : Set G)
  change ((E : Set G) ∪ (F : Set G)).ncard + Nat.card (E ⊓ F : Subgroup G) =
    Nat.card E + Nat.card F at hu
  rw [c.endpoint_intersection, Nat.card_zpowers, h.involution, d.card, dy.card] at hu
  have hr := Set.ncard_sdiff_singleton_add_one
    (show (1 : G) ∈ (E : Set G) ∪ (F : Set G) from Or.inl E.one_mem)
  have he : {x : G | x ∈ coreInG z ∧ IsConj z x} =
      ((E : Set G) ∪ (F : Set G)) \ {1} := by
    ext x
    exact c.fusion_union x
  have hc : Nat.card (CoreFusion z) =
      (((E : Set G) ∪ (F : Set G)) \ {1}).ncard :=
    Nat.card_congr (Equiv.setCongr he)
  omega

/-- The two elementary eights generate the original core, by the product-order formula. -/
theorem configuration_endpoint_generate (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) :
    coreIntersection z g ⊔ coreIntersection z c.y = coreInG z := by
  have hn : coreIntersection z c.y ≤ normalizer (coreIntersection z g : Set G) :=
    ((coreIntersection_le z c.y).trans (coreInG_le z)).trans
      (intersection_centralizer_le_normalizer d)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (coreIntersection z g) (coreIntersection z c.y) hn
  rw [d.card, dy.card, c.endpoint_intersection, Nat.card_zpowers, h.involution] at hc
  apply eq_of_le_of_card_ge (sup_le (coreIntersection_le z g) (coreIntersection_le z c.y))
  rw [h.coreInG_card]
  omega

/-- The endpoint overlap is the full original involution centralizer. -/
theorem geometry_endpoint_intersection (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) :
    normalizer (coreIntersection z g : Set G) ⊓
      normalizer (coreIntersection z c.y : Set G) = Centralizer z := by
  apply le_antisymm
  · have hn := normalizer_inf_normalizer_le_normalizer_sup
      (coreIntersection z g) (coreIntersection z c.y)
    rwa [configuration_endpoint_generate h d c dy, h.normalizer_core] at hn
  · exact le_inf (intersection_centralizer_le_normalizer d)
      (intersection_centralizer_le_normalizer dy)

/-- The actual chamber is the given Sylow subgroup of H, embedded in L. -/
theorem geometry_chamber_eq (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) :
    Quasithin.I5.chamberSubgroup (geometryFamily z g c.y c.A) =
      ((c.S : Subgroup (Centralizer z)).map (Centralizer z).subtype).subgroupOf
        (geometryGroup z g c.y) := by
  ext x
  simp only [Quasithin.I5.chamberSubgroup, mem_iInf]
  rw [← c.normalizer_intersection, ← geometry_endpoint_intersection h d c dy]
  constructor
  · intro hx
    exact ⟨⟨hx 0, hx 2⟩, hx 1⟩
  · intro hx i
    fin_cases i
    · exact hx.1.1
    · exact hx.2
    · exact hx.1.2

omit [Finite G] in
/-- The generated subgroup L contains the full ambient centralizer of z. -/
theorem geometry_centralizer_le (d : IntersectionData z g) (y : G) :
    Centralizer z ≤ geometryGroup z g y :=
  (intersection_centralizer_le_normalizer d).trans le_sup_left

omit [Finite G] in
/-- The two endpoint vertices already generate L by its definition. -/
theorem geometry_family_generate (y : G) (A : Subgroup G) :
    (⨆ i, geometryFamily z g y A i) = ⊤ := by
  have he : geometryFamily z g y A 0 ⊔ geometryFamily z g y A 2 = ⊤ := by
    apply map_injective (geometryGroup z g y).subtype_injective
    change ((normalizer (coreIntersection z g : Set G)).subgroupOf (geometryGroup z g y) ⊔
      (normalizer (coreIntersection z y : Set G)).subgroupOf (geometryGroup z g y)).map
        (geometryGroup z g y).subtype = (⊤ : Subgroup (geometryGroup z g y)).map
          (geometryGroup z g y).subtype
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show normalizer (coreIntersection z g : Set G) ≤
      geometryGroup z g y from le_sup_left),
      map_subgroupOf_eq_of_le (show normalizer (coreIntersection z y : Set G) ≤
      geometryGroup z g y from le_sup_right), ← MonoidHom.range_eq_map, range_subtype]
    rfl
  apply top_unique
  rw [← he]
  exact sup_le (le_iSup _ 0) (le_iSup _ 2)

omit [Finite G] in
/-- The elementary-sixteen kernel and S₃ × S₃ quotient give order 576. -/
theorem configuration_normalizer_card (c : A3Configuration z g) :
    Nat.card (normalizer (c.A : Set G)) = 576 := by
  rw [card_eq_card_quotient_mul_card_subgroup (c.A.subgroupOf (normalizer (c.A : Set G))),
    Nat.card_congr c.normalizer_quotient.some.toEquiv, Nat.card_prod,
    Nat.card_perm, Nat.card_fin,
    Nat.card_congr (subgroupOfEquivOfLe c.A.le_normalizer).toEquiv, c.card]
  decide

/-- The chamber has order 64, before any parabolic or recognition argument. -/
theorem geometry_chamber_card (h : Hypotheses z) (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    Nat.card (Quasithin.I5.chamberSubgroup (geometryFamily z g c.y c.A)) = 64 := by
  let L := geometryGroup z g c.y
  have hSL : (c.S : Subgroup (Centralizer z)).map (Centralizer z).subtype ≤ L :=
    (map_subtype_le _).trans (geometry_centralizer_le d c.y)
  rw [geometry_chamber_eq h d c dy,
    Nat.card_congr (subgroupOfEquivOfLe hSL).toEquiv,
    card_map_of_injective (Centralizer z).subtype_injective,
    h.centralizer_sylow_two_card]

/-- The common chamber has the full two-part of every actual vertex order. -/
theorem geometry_sylow (h : Hypotheses z) (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y)
    (hle : normalizer (c.A : Set G) ≤ geometryGroup z g c.y) :
    ∀ i, ∃ S : Sylow 2 (geometryFamily z g c.y c.A i),
      (S : Subgroup (geometryFamily z g c.y c.A i)) =
        (Quasithin.I5.chamberSubgroup (geometryFamily z g c.y c.A)).subgroupOf
          (geometryFamily z g c.y c.A i) := by
  let L := geometryGroup z g c.y
  let V := geometryFamily z g c.y c.A
  let T := Quasithin.I5.chamberSubgroup V
  have hT : ∀ i, T ≤ V i := fun i => iInf_le _ i
  have hcardT : Nat.card T = 64 := geometry_chamber_card h d c dy
  have hc0 : Nat.card (V 0) = 1344 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show normalizer (coreIntersection z g : Set G) ≤
      L from le_sup_left)).toEquiv).trans (intersection_normalizer_card d)
  have hc1 : Nat.card (V 1) = 576 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (configuration_normalizer_card c)
  have hc2 : Nat.card (V 2) = 1344 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show normalizer (coreIntersection z c.y : Set G) ≤
      L from le_sup_right)).toEquiv).trans (intersection_normalizer_card dy)
  intro i
  have hcard : Nat.card (T.subgroupOf (V i)) = 2 ^ (Nat.card (V i)).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hT i)).toEquiv, hcardT]
    fin_cases i
    · change 64 = 2 ^ (Nat.card (V 0)).factorization 2
      rw [hc0]; decide +kernel
    · change 64 = 2 ^ (Nat.card (V 1)).factorization 2
      rw [hc1]; decide +kernel
    · change 64 = 2 ^ (Nat.card (V 2)).factorization 2
      rw [hc2]; decide +kernel
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

private theorem normalizer_core_of_quotient {K : Type*} [Group K] [Finite K]
    (B : Subgroup G) (hp : IsPGroup 2 B)
    (e : (normalizer (B : Set G) ⧸ B.subgroupOf (normalizer (B : Set G))) ≃* K)
    (hc : pCore 2 K = ⊥) :
    pCore 2 (normalizer (B : Set G)) = B.subgroupOf (normalizer (B : Set G)) := by
  have hq : pCore 2 (normalizer (B : Set G) ⧸
      B.subgroupOf (normalizer (B : Set G))) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso, hc, Subgroup.map_bot]
  let q := QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G)))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact hp.of_equiv (subgroupOfEquivOfLe B.le_normalizer).symm
  have he := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk
  rw [hq, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at he
  exact he.symm

omit [Finite G] in
private theorem embedded_normalizer_core (B L : Subgroup G)
    (hle : normalizer (B : Set G) ≤ L)
    (hc : pCore 2 (normalizer (B : Set G)) = B.subgroupOf (normalizer (B : Set G))) :
    ((normalizer (B : Set G)).subgroupOf L).pCoreIn 2 = B.subgroupOf L := by
  let e := subgroupOfEquivOfLe hle
  apply map_injective L.subtype_injective
  rw [pCoreIn, map_map, map_subgroupOf_eq_of_le (B.le_normalizer.trans hle)]
  have he := congrArg (fun R : Subgroup (normalizer (B : Set G)) =>
    R.map (normalizer (B : Set G)).subtype) (pCore_map_iso 2 e)
  rw [hc, map_subgroupOf_eq_of_le B.le_normalizer, map_map] at he
  exact he

/-- The actual endpoint two-core is the embedded elementary eight. -/
theorem intersection_normalizer_core (d : IntersectionData z g) :
    pCore 2 (normalizer (coreIntersection z g : Set G)) =
      (coreIntersection z g).subgroupOf (normalizer (coreIntersection z g : Set G)) :=
  normalizer_core_of_quotient (coreIntersection z g)
    (IsPGroup.of_card (p := 2) (n := 3) d.card)
    d.normalizer_quotient.some Matrix.PSL3Two.pCore_two_PSL_eq_bot

/-- The actual middle two-core is the embedded elementary sixteen. -/
theorem configuration_line_core (c : A3Configuration z g) :
    pCore 2 (normalizer (c.A : Set G)) = c.A.subgroupOf (normalizer (c.A : Set G)) :=
  normalizer_core_of_quotient c.A (IsPGroup.of_card (p := 2) (n := 4) c.card)
    c.normalizer_quotient.some SymmetricThreeProduct.twoCore_eq_bot

/-- The chamber core is trivial, without recognizing L or assuming G simple. -/
theorem geometry_core_free (h : Hypotheses z) (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    (Quasithin.I5.chamberSubgroup (geometryFamily z g c.y c.A)).normalCore = ⊥ := by
  let L := geometryGroup z g c.y
  let V := geometryFamily z g c.y c.A
  let T := Quasithin.I5.chamberSubgroup V
  let N := T.normalCore
  have hT : ∀ i, T ≤ V i := fun i => iInf_le _ i
  have hpT : IsPGroup 2 T :=
    IsPGroup.of_card (p := 2) (n := 6) (geometry_chamber_card h d c dy)
  have hpN : IsPGroup 2 N := hpT.to_le T.normalCore_le
  have hNV : ∀ i, N ≤ (V i).pCoreIn 2 := by
    intro i
    apply le_pCoreIn_of_normalizes hpN (T.normalCore_le.trans (hT i))
    rw [normalizer_eq_top]
    exact le_top
  have hNE : N ≤ (coreIntersection z g).subgroupOf L := (embedded_normalizer_core _ _ le_sup_left
    (intersection_normalizer_core d)) ▸ hNV 0
  have hNF : N ≤ (coreIntersection z c.y).subgroupOf L := (embedded_normalizer_core _ _ le_sup_right
    (intersection_normalizer_core dy)) ▸ hNV 2
  let K : Subgroup G := N.map L.subtype
  have hK : K ≤ zpowers z := by
    rintro x ⟨a, ha, rfl⟩
    rw [← c.endpoint_intersection]
    exact ⟨hNE ha, hNF ha⟩
  have hn : L ≤ normalizer (K : Set G) := by
    have hn := N.le_normalizer_map L.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hdvd : Nat.card K ∣ 2 := by
    have hd := card_dvd_of_le hK
    rwa [Nat.card_zpowers, h.involution] at hd
  have hKbot : K = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hc | hc
    · exact (eq_bot_iff_card K).mpr hc
    · have hKeq : K = zpowers z := eq_of_le_of_card_ge hK (by
        rw [Nat.card_zpowers, h.involution, hc])
      rw [hKeq, normalizer_zpowers_eq_centralizer_of_order_two z
        h.involution] at hn
      exact (intersection_normalizer_not_le h d
        ((show normalizer (coreIntersection z g : Set G) ≤ L from le_sup_left).trans hn)).elim
  apply map_injective L.subtype_injective
  exact hKbot.trans (map_bot L.subtype).symm

omit [Finite G] in
private noncomputable def embedded_normalizer_quotient (B L : Subgroup G)
    (hle : normalizer (B : Set G) ≤ L)
    (hcore : ((normalizer (B : Set G)).subgroupOf L).pCoreIn 2 = B.subgroupOf L) :
    (((normalizer (B : Set G)).subgroupOf L) ⧸
      pCore 2 ((normalizer (B : Set G)).subgroupOf L)) ≃*
        (normalizer (B : Set G) ⧸ B.subgroupOf (normalizer (B : Set G))) := by
  let e := subgroupOfEquivOfLe hle
  apply QuotientGroup.congr _ _ e
  apply map_injective (normalizer (B : Set G)).subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le B.le_normalizer]
  have hm := congrArg (fun K : Subgroup L => K.map L.subtype) hcore
  rw [pCoreIn, map_map, map_subgroupOf_eq_of_le (B.le_normalizer.trans hle)] at hm
  exact hm

/-- Construct every D-system field from the source configuration and its local parabolics. -/
noncomputable def configuration_system (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) (p : A3ParabolicData z g c.y c.A) :
    Quasithin.I5.DSystem .A3 (geometryGroup z g c.y) where
  family := geometryFamily z g c.y c.A
  finite_vertex _ := inferInstance
  point_A3 _ := ⟨(embedded_normalizer_quotient (coreIntersection z g)
    (geometryGroup z g c.y) le_sup_left
    (embedded_normalizer_core _ _ le_sup_left (intersection_normalizer_core d))).trans
      d.normalizer_quotient.some⟩
  point_C3 he := by cases he
  line_quotient := ⟨(embedded_normalizer_quotient c.A
    (geometryGroup z g c.y) p.middle_le
    (embedded_normalizer_core _ _ p.middle_le (configuration_line_core c))).trans
      c.normalizer_quotient.some⟩
  plane_quotient := ⟨(embedded_normalizer_quotient (coreIntersection z c.y)
    (geometryGroup z g c.y) le_sup_right
    (embedded_normalizer_core _ _ le_sup_right (intersection_normalizer_core dy))).trans
      dy.normalizer_quotient.some⟩
  sylow := geometry_sylow h d c dy p.middle_le
  point_parabolics := p.point_parabolics
  line_parabolics := p.line_parabolics
  plane_parabolics := p.plane_parabolics
  generate := geometry_family_generate c.y c.A
  core_free := geometry_core_free h d c dy
  nondegenerate he := by cases he

/-- The constructed system uses exactly the three embedded ambient normalizers. -/
@[simp] theorem configuration_system_family (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) (p : A3ParabolicData z g c.y c.A) :
    (configuration_system h d c dy p).family = geometryFamily z g c.y c.A := by
  rfl

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition

end
