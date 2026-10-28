module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerRegularity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SemilocalCentralizer
public import Theory.GroupAction.CubicTree.ThreeClosed

/-!
# The three-closed exclusion on the literal local normalizer quotient

The base stabilizer in the faithful distance-two quotient action is canonically
isomorphic to the original local normalizer modulo the track fixer. Transport
through this exact quotient identifies the group used by the semilocal
centralizer argument. Regularity length at least four excludes a normal
Sylow three-subgroup and gives the required cubic centralizer divisor.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395. The earlier comparison supplies the regularity lower bound.
-/

public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem local_fixes_normalizerBase (Q : Subgroup G)
    (g : localNormalizer F Q false) :
    (⟨g, g.property.1⟩ : normalizer (Q : Set G)) • normalizerBase F Q =
      normalizerBase F Q := by
  apply Subtype.ext
  change (g : G) • RankTwo.base F false = RankTwo.base F false
  change (g : G) ∈ MulAction.stabilizer G (RankTwo.base F false)
  rw [RankTwo.base, stabilizer_base]
  exact g.property.2

private def localToComponent (Q : Subgroup G) :
    localNormalizer F Q false →* normalizerComponentGroup F Q where
  toFun g := ⟨⟨g, g.property.1⟩,
    ComponentAction.stabilizer_le (normalizerComponent F Q) (normalizerGraphAction F Q)
      (normalizerComponentBase F Q) (local_fixes_normalizerBase Q g)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem localToComponent_fixes (Q : Subgroup G) (g : localNormalizer F Q false) :
    localToComponent Q g • normalizerComponentBase F Q = normalizerComponentBase F Q :=
  Subtype.ext (local_fixes_normalizerBase Q g)

private noncomputable def localToQuotientStabilizer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    letI := normalizerQuotientAction h t ht0
    localNormalizer F (trackFixer t) false →*
      MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t))
        (normalizerComponentBase F (trackFixer t)) := by
  let _ := normalizerQuotientAction h t ht0
  let q := QuotientGroup.mk' (normalizerComponentKernel F (trackFixer t))
  exact {
    toFun g := ⟨q (localToComponent (trackFixer t) g), localToComponent_fixes _ g⟩
    map_one' := Subtype.ext ((q.comp (localToComponent _)).map_one)
    map_mul' g k := Subtype.ext ((q.comp (localToComponent _)).map_mul g k) }

private theorem localToQuotientStabilizer_surjective (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    Function.Surjective (localToQuotientStabilizer h t ht0) := by
  let _ := normalizerQuotientAction h t ht0
  rintro ⟨u, hu⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (normalizerComponentKernel F (trackFixer t)) u
  have ha : a • normalizerComponentBase F (trackFixer t) =
      normalizerComponentBase F (trackFixer t) := hu
  have hv : ((a : normalizer (trackFixer t : Set G)) : G) • RankTwo.base F false =
      RankTwo.base F false := congrArg
        (fun z : normalizerComponent F (trackFixer t) => (z.val : RankTwo.Vertex F)) ha
  have haF : ((a : normalizer (trackFixer t : Set G)) : G) ∈ F false := by
    change ((a : normalizer (trackFixer t : Set G)) : G) ∈
      MulAction.stabilizer G (RankTwo.base F false) at hv
    simpa only [RankTwo.base, stabilizer_base] using hv
  let g : localNormalizer F (trackFixer t) false :=
    ⟨((a : normalizer (trackFixer t : Set G)) : G), a.val.property, haF⟩
  refine ⟨g, Subtype.ext ?_⟩
  change QuotientGroup.mk' _ (localToComponent _ g) = QuotientGroup.mk' _ a
  congr 1

private theorem localToQuotientStabilizer_kernel (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    (localToQuotientStabilizer h t ht0).ker =
      (trackFixer t).subgroupOf (localNormalizer F (trackFixer t) false) := by
  ext g
  change localToQuotientStabilizer h t ht0 g = 1 ↔ (g : G) ∈ trackFixer t
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (localToComponent (trackFixer t) g)

/-- The exact local quotient used in the centralizer argument is the base
point stabilizer of the faithful normalizer quotient action. -/
noncomputable def normalizerBaseStabilizerEquiv (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    letI := normalizerQuotientAction h t ht0
    (localNormalizer F (trackFixer t) false ⧸
      (trackFixer t).subgroupOf (localNormalizer F (trackFixer t) false)) ≃*
      MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t))
        (normalizerComponentBase F (trackFixer t)) :=
  QuotientGroup.liftEquiv _ (localToQuotientStabilizer_surjective h t ht0)
    (localToQuotientStabilizer_kernel h t ht0).symm

/-- The graph-theoretic three-closed exclusion on the original local quotient. -/
theorem normalizerQuotient_not_normal_sylow_three (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (hQ : NormalizerCandidate F (trackFixer t)) (s : ℕ) (hs : 4 ≤ s)
    (hcards : letI := normalizerQuotientAction h t ht0
      ∀ x : normalizerComponent F (trackFixer t),
        Nat.card (MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t)) x) =
          3 * 2 ^ (s - 1))
    (P : Sylow 3 (localNormalizer F (trackFixer t) false ⧸
      (trackFixer t).subgroupOf (localNormalizer F (trackFixer t) false))) :
    ¬ (P : Subgroup (localNormalizer F (trackFixer t) false ⧸
      (trackFixer t).subgroupOf (localNormalizer F (trackFixer t) false))).Normal := by
  let _ := normalizerQuotientAction h t ht0
  let : Finite (localNormalizer F (trackFixer t) false) :=
    h.finite_localNormalizer (trackFixer t) false
  obtain ⟨htree, hcubic, hfaith, hact, hvertex, hlocal, _⟩ :=
    normalizerQuotient_geometry h t ht0 hQ
  let _ : FaithfulSMul (normalizerComponentQuotient F (trackFixer t))
      (normalizerComponent F (trackFixer t)) := hfaith
  let e := normalizerBaseStabilizerEquiv h t ht0
  intro hP
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup (MulAction.stabilizer
      (normalizerComponentQuotient F (trackFixer t))
      (normalizerComponentBase F (trackFixer t)))).Normal :=
    hP.map e.toMonoidHom e.surjective
  exact not_normal_sylow_three_of_regularity_at_least_four hact htree.connected.preconnected
    hcubic hvertex (fun {x y z} => hlocal x y z) s hs hcards
    (normalizerComponentBase F (trackFixer t)) S hS

/-- The normalizer quotient action discharges the three-closed premise of the
semilocal centralizer calculation, retaining the actual track fixer. -/
theorem normalizer_centralizer_three_dvd_of_regularity (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (hQ : NormalizerCandidate F (trackFixer t)) (s : ℕ) (hs : 4 ≤ s)
    (hcards : letI := normalizerQuotientAction h t ht0
      ∀ x : normalizerComponent F (trackFixer t),
        Nat.card (MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t)) x) =
          3 * 2 ^ (s - 1)) :
    3 ∣ Nat.card ((centralizer (trackFixer t : Set G)).subgroupOf (F false)) := by
  let P : Sylow 3 (localNormalizer F (trackFixer t) false ⧸
      (trackFixer t).subgroupOf (localNormalizer F (trackFixer t) false)) := Classical.ofNonempty
  exact hQ.three_dvd_card_centralizer h P
    (normalizerQuotient_not_normal_sylow_three h t ht0 hQ s hs hcards P)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
