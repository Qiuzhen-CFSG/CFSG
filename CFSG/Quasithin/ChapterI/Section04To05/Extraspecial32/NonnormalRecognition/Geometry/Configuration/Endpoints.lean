module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Assembly
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The two actual endpoint intersections in source Lemma 3.1

The orbit of z under the normalizer of E has size 1344 / 192 = 7,
so it fills E minus the identity. Nonsaturation therefore supplies a
conjugate of z in Q outside E, and hence a genuinely different second
intersection F = Q ∩ Qʸ.

To identify E ∩ F, let the original Sylow three-subgroup act on it.
Its fixed points are precisely ⟨z⟩. Thus its order is 2 modulo 3 and
divides 8. Order 8 would identify E and F, leaving exactly ⟨z⟩.
All maps and relative normalizers are the literal inclusions in G.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), Lemma 3.1(4), printed pp.36–37. The endpoint
splitting and the middle normalizer are separate remaining arguments.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z g : G}

omit [Finite G] in
/-- Self-centralization puts the distinguished involution in every local intersection. -/
theorem distinguished_mem_intersection (d : IntersectionData z g) :
    z ∈ coreIntersection z g := by
  rw [← d.self_centralizing]
  intro x hx
  exact (mem_centralizer_singleton_iff.mp
    (coreInG_le z (coreIntersection_le z g hx)))

/-- The endpoint normalizer fuses every nonidentity element of E to z. -/
theorem intersection_sharp_fused (h : Hypotheses z) (d : IntersectionData z g)
    {x : G} (hx : x ∈ coreIntersection z g) (hx1 : x ≠ 1) : IsConj z x := by
  let E := coreIntersection z g
  let M := normalizer (E : Set G)
  let : MulDistribMulAction M G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp M.subtype)
  let : MulAction M G := (inferInstance : MulDistribMulAction M G).toMulAction
  have hstab : MulAction.stabilizer M z = (Centralizer z).subgroupOf M := by
    ext m
    change (m : G) * z * (m : G)⁻¹ = z ↔ (m : G) ∈ Centralizer z
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hcard : Nat.card (MulAction.orbit M z) = 7 := by
    have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup M z)
    rw [Nat.card_prod, hstab,
      Nat.card_congr (subgroupOfEquivOfLe (intersection_centralizer_le_normalizer d)).toEquiv,
      h.centralizer_card, intersection_normalizer_card d] at he
    omega
  have hsub : MulAction.orbit M z ⊆ (E : Set G) \ {1} := by
    rintro a ⟨m, rfl⟩
    constructor
    · exact ((m.property) z).mp (distinguished_mem_intersection d)
    · change ¬ (m : G) * z * (m : G)⁻¹ = 1
      intro he
      have hz : z = 1 := (MulAut.conj (m : G)).injective (he.trans (map_one _).symm)
      have ho := h.involution
      rw [hz, orderOf_one] at ho
      omega
  have hsame : MulAction.orbit M z = (E : Set G) \ {1} := by
    apply Set.eq_of_subset_of_ncard_le hsub
    change ((E : Set G) \ {1}).ncard ≤ Nat.card (MulAction.orbit M z)
    rw [Set.ncard_sdiff_singleton_of_mem E.one_mem, hcard]
    change Nat.card E - 1 ≤ 7
    rw [d.card]
  obtain ⟨m, hm⟩ := (hsame.symm ▸ (show x ∈ (E : Set G) \ {1} from ⟨hx, hx1⟩))
  exact isConj_iff.mpr ⟨m, hm⟩

/-- Failure of saturation supplies a conjugate of z outside the original intersection. -/
theorem exists_second_intersection (h : Hypotheses z) (d : IntersectionData z g)
    (hs : ¬ FusionSaturated z g) :
    ∃ y : G, y * z * y⁻¹ ∈ coreInG z ∧ y * z * y⁻¹ ∉ coreIntersection z g := by
  classical
  by_contra! he
  apply hs
  intro x
  constructor
  · rintro ⟨hx, hx1⟩
    exact ⟨coreIntersection_le z g hx, intersection_sharp_fused h d hx hx1⟩
  · rintro ⟨hx, hc⟩
    obtain ⟨y, rfl⟩ := isConj_iff.mp hc
    refine ⟨he y hx, ?_⟩
    intro hz
    have heq : z = 1 := (MulAut.conj y).injective (hz.trans (map_one _).symm)
    have ho := h.involution
    rw [heq, orderOf_one] at ho
    omega

/-- Distinct H-normal local intersections meet in precisely the involution line. -/
theorem intersection_inf_eq_line (h : Hypotheses z) (d : IntersectionData z g)
    {y : G} (dy : IntersectionData z y)
    (hne : coreIntersection z g ≠ coreIntersection z y) :
    coreIntersection z g ⊓ coreIntersection z y = zpowers z := by
  let I := coreIntersection z g ⊓ coreIntersection z y
  have hIQ : I ≤ coreInG z := inf_le_left.trans (coreIntersection_le z g)
  have hIH : I ≤ Centralizer z := hIQ.trans (coreInG_le z)
  have hZI : zpowers z ≤ I := zpowers_le.mpr
    ⟨distinguished_mem_intersection d, distinguished_mem_intersection dy⟩
  have hHN : Centralizer z ≤ normalizer (I : Set G) :=
    (le_inf (intersection_centralizer_le_normalizer d)
      (intersection_centralizer_le_normalizer dy)).trans inf_normalizer_le_normalizer_inf
  let action : h.X →* MulAut I := I.normalizerMonoidHom.comp
    ((inclusion hHN).comp (h.X : Subgroup (Centralizer z)).subtype)
  let : MulDistribMulAction h.X I := MulDistribMulAction.compHom I action
  let j : I →* Centralizer z := inclusion hIH
  have hfixed : ∀ u : I, (∀ a : h.X, a • u = u) ↔ (u : G) ∈ zpowers z := by
    intro u
    constructor
    · intro hu
      have hucore : j u ∈ Core z := by
        rw [← coreInG_subgroupOf]
        exact hIQ u.property
      have huC : j u ∈ centralizer (h.X : Set (Centralizer z)) := by
        intro a ha
        apply Subtype.ext
        have he := congrArg (fun v : I => (v : G)) (hu ⟨a, ha⟩)
        change (a : G) * (u : G) * (a : G)⁻¹ = u at he
        exact mul_inv_eq_iff_eq_mul.mp he
      have huz : j u ∈ zpowers (distinguished z) := h.fixed ▸ ⟨hucore, huC⟩
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp huz
      exact mem_zpowers_iff.mpr ⟨n, congrArg (fun v : Centralizer z => (v : G)) hn⟩
    · intro hu a
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hu
      apply Subtype.ext
      change (a.val : G) * (u : G) * (a.val : G)⁻¹ = u
      rw [← hn]
      apply mul_inv_eq_iff_eq_mul.mpr
      exact (show Commute (a.val : G) z from
        mem_centralizer_singleton_iff.mp a.val.property).zpow_right n
  let e : MulAction.fixedPoints h.X I ≃ zpowers z := {
    toFun u := ⟨u.val, (hfixed u.val).mp u.property⟩
    invFun u := ⟨⟨u, hZI u.property⟩, (hfixed _).mpr u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hm := h.X.isPGroup'.card_modEq_card_fixedPoints I
  rw [Nat.card_congr e, Nat.card_zpowers, h.involution] at hm
  have hd : Nat.card I ∣ 2 ^ 3 := by
    have hd := card_dvd_of_le (show I ≤ coreIntersection z g from inf_le_left)
    rwa [d.card] at hd
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hsmall : Nat.card I = 2 := by
    interval_cases n
    · norm_num [hcard, Nat.ModEq] at hm
    · simpa using hcard
    · norm_num [hcard, Nat.ModEq] at hm
    · have hIE : I = coreIntersection z g :=
        eq_of_le_of_card_ge inf_le_left (by norm_num [d.card, hcard])
      have hIF : I = coreIntersection z y :=
        eq_of_le_of_card_ge inf_le_right (by norm_num [dy.card, hcard])
      exact (hne (hIE.symm.trans hIF)).elim
  exact (eq_of_le_of_card_ge hZI (by rw [hsmall, Nat.card_zpowers, h.involution])).symm

/-- Construct the actual second endpoint and its exact overlap from nonsaturation. -/
theorem exists_endpoint_pair (h : Hypotheses z)
    (local_intersections : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      IntersectionData z y)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hs : ¬ FusionSaturated z g) :
    ∃ y : G, y * z * y⁻¹ ∈ coreInG z ∧ y * z * y⁻¹ ≠ z ∧
      coreIntersection z g ⊓ coreIntersection z y = zpowers z := by
  have d := local_intersections g hgQ hg
  obtain ⟨y, hyQ, hyE⟩ := exists_second_intersection h d hs
  have hy : y * z * y⁻¹ ≠ z := by
    intro he
    apply hyE
    rw [he]
    exact distinguished_mem_intersection d
  have dy := local_intersections y hyQ hy
  refine ⟨y, hyQ, hy, intersection_inf_eq_line h d dy ?_⟩
  intro he
  exact hyE (he ▸ conjugate_mem_coreIntersection h y hyQ)
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
