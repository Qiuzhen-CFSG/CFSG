module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Weights
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.GroupTheory.ElementSubgroupIncidence

/-!
# The rank-three bound and conjugate intersections in 13.4

Once 13.4.12 gives a unique escaping vector in V∩Ω₁Z(T), all escaping
vectors have its weight. An ambient-centralizer witness U for r(G,V)
therefore has constant nonzero weight and order at most four. Since the
original marked V has order thirty-two, its corank is at least three.

The actual earlier fusion statement 13.4.2(3) also makes every nonidentity
point of a proper returning conjugate escape. Thus the intersection has the
same constant-weight bound, using the literal conjugation map.

These are conditional applications for 13.4.16 and 13.4.17(5–6). The proof
of unique escape, the graph construction selecting weight two, and the
terminal nonsolvable contradiction remain with qt-d-1341-nonsolvable-source.
Earlier fusion and structural inputs are supplied by qt-d-1332-source and
qt-d-1222-source; final recognition belongs to qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith, printed pp.913–915.
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

omit [Finite G] in
theorem card_subgroup_le_four_of_weight (U : Subgroup G) (hUV : U ≤ V)
    (k : ℕ) (hk : k = 2 ∨ k = 4)
    (hw : ∀ x : U, x ≠ 1 → m.weight ⟨x.val,hUV x.property⟩ = k) :
    Nat.card U ≤ 4 := by
  let f : U →* Multiplicative (Full (Fin 6)) :=
    (core (Fin 6)).subtype.toAddMonoidHom.toMultiplicative.comp
      (m.coordinate.toMonoidHom.comp (inclusion hUV))
  apply six_constant_weight_card_le_four_of_injective f ?_ k hk hw
  intro x y he
  apply Subtype.ext
  have hh : m.coordinate ⟨x.val,hUV x.property⟩ = m.coordinate ⟨y.val,hUV y.property⟩ :=
    Multiplicative.toAdd.injective (Subtype.ext (congrArg Multiplicative.toAdd he))
  exact congrArg (fun a : V => a.val) (m.coordinate.injective hh)

omit [Finite G] in
theorem three_le_globalR_of_escape_weight (k : ℕ) (hk : k = 2 ∨ k = 4)
    (hc : ∀ v : V, v ≠ 1 →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (V : Set G) → m.weight v = k) :
    3 ≤ ChapterE.globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV,hU⟩
  have hcard : Nat.card U ≤ 4 := by
    apply m.card_subgroup_le_four_of_weight U hUV k hk
    intro x hx
    apply hc _ (fun he => hx (Subtype.ext (congrArg (fun a : V => a.val) he)))
    intro hh
    apply hU
    apply le_trans ?_ hh
    exact centralizer_le (Set.singleton_subset_iff.mpr x.property)
  have hmul : Nat.card U * U.relIndex V = 32 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv]
    exact (U.subgroupOf V).card_mul_index.trans m.card_module
  have hi : 8 ≤ U.relIndex V := by
    have hb := Nat.mul_le_mul_right (U.relIndex V) hcard
    rw [hmul] at hb
    omega
  have hlog : 3 ≤ ChapterE.subgroupCorank V U :=
    Nat.le_log_of_pow_le (by decide) hi
  exact_mod_cast hlog

/-- The genuine source rank parameter is at least three after 13.4.12's
unique-escape result, for either possible weight of the escaping vector. -/
theorem three_le_globalR_of_unique_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z) :
    3 ≤ ChapterE.globalR V := by
  have hzfixed : z.val ∉ centralizer (L : Set G) := by
    intro hf
    exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hf⟩
      (fun he => hz1 (Subtype.ext he))).le
  apply m.three_le_globalR_of_escape_weight (m.weight z) (m.nonfixed_weight z hzfixed)
  intro v hv1 hvout
  apply m.escape_has_unique_weight h structural z hz1 hzT hzout hunique v hv1
  rwa [normalizer_component_eq_module h structural D m]


/-- The literal conjugate intersection in 13.4.17(6). The fusion input is
13.4.2(3), equivalently the earlier 13.2.2(5) normalizer fusion statement. -/
theorem conjugate_intersection_weight_of_unique_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (g : G) (hg : g ∉ normalizer (L : Set G))
    (v : V) (hv1 : v ≠ 1) (hvg : v.val ∈ V.map (MulAut.conj g).toMonoidHom) :
    m.weight v = m.weight z := by
  apply m.escape_has_unique_weight h structural z hz1 hzT hzout hunique v hv1
  intro hc
  obtain ⟨c,hcC,he⟩ := (element_fusion_iff_centralizer_incidence V v.val).mp
    (hfusion v hv1) g hvg
  apply hg
  rw [normalizer_component_eq_module h structural D m]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change V.conjBy g = V
  rw [← he]
  exact mem_normalizer_iff_map_conj_eq.mp
    ((normalizer_component_eq_module h structural D m) ▸ hc hcC)

/-- In particular every proper returning conjugate meets V in at most four
vectors. This retains the full ambient intersection and its actual conjugator. -/
theorem conjugate_intersection_card_of_unique_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (g : G) (hg : g ∉ normalizer (L : Set G)) :
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 4 := by
  have hzfixed : z.val ∉ centralizer (L : Set G) := by
    intro hf
    exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hf⟩
      (fun he => hz1 (Subtype.ext he))).le
  apply m.card_subgroup_le_four_of_weight _ inf_le_left (m.weight z)
    (m.nonfixed_weight z hzfixed)
  intro x hx
  apply m.conjugate_intersection_weight_of_unique_escape h structural z hz1 hzT hzout
    hunique hfusion g hg _ (fun he => hx (Subtype.ext (congrArg (fun a : V => a.val) he)))
  exact x.property.2

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
