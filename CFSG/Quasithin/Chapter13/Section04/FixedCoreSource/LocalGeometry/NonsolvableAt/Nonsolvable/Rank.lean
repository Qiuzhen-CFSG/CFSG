module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.Weights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Rank
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Weights
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.GroupTheory.ElementSubgroupIncidence

/-!
# The rank-three bound and conjugate intersections in 13.4: structure at the original group

Once 13.4.12 gives a unique escaping vector in V∩Ω₁Z(T), all escaping
vectors have its weight. An ambient-centralizer witness U for r(G,V)
therefore has constant nonzero weight and order at most four. Since the
original marked V has order thirty-two, its corank is at least three.

The actual earlier fusion statement 13.4.2(3) also makes every nonidentity
point of a proper returning conjugate escape. Thus the intersection has the
same constant-weight bound, using the literal conjugation map.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/Rank` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace CoreMarking
variable {D : ChosenModule T L V} (m : CoreMarking D)
include m

/-- The genuine source rank parameter is at least three after 13.4.12's
unique-escape result, for either possible weight of the escaping vector. -/
theorem three_le_globalR_of_unique_escape_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z) :
    3 ≤ ChapterE.globalR V := by
  have hzfixed : z.val ∉ centralizer (L : Set G) := by
    intro hf
    exact hzout (fixed_generator_centralizer_at h structural D m ⟨z.property,hf⟩
      (fun he => hz1 (Subtype.ext he))).le
  apply m.three_le_globalR_of_escape_weight (m.weight z) (m.nonfixed_weight z hzfixed)
  intro v hv1 hvout
  apply m.escape_has_unique_weight_at h structural z hz1 hzT hzout hunique v hv1
  rwa [normalizer_component_eq_module_at h structural D m]


/-- The literal conjugate intersection in 13.4.17(6). The fusion input is
13.4.2(3), equivalently the earlier 13.2.2(5) normalizer fusion statement. -/
theorem conjugate_intersection_weight_of_unique_escape_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (g : G) (hg : g ∉ normalizer (L : Set G))
    (v : V) (hv1 : v ≠ 1) (hvg : v.val ∈ V.map (MulAut.conj g).toMonoidHom) :
    m.weight v = m.weight z := by
  apply m.escape_has_unique_weight_at h structural z hz1 hzT hzout hunique v hv1
  intro hc
  obtain ⟨c,hcC,he⟩ := (element_fusion_iff_centralizer_incidence V v.val).mp
    (hfusion v hv1) g hvg
  apply hg
  rw [normalizer_component_eq_module_at h structural D m]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change V.conjBy g = V
  rw [← he]
  exact mem_normalizer_iff_map_conj_eq.mp
    ((normalizer_component_eq_module_at h structural D m) ▸ hc hcC)

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
