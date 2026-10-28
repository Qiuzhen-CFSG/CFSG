module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourReciprocity
public import Theory.Representation.BinaryPermutation.SixCoreEightHyperplane

/-!
# The remaining returning conjugate in product weak closure

Assume the unique escaping point has weight four, as in the product
alternative. Normalizer fusion gives weight four on every proper returning
intersection, and the existing uniqueness theorem gives r(G,V) at least
three. If A=Vʸ lies in M=N_G(L) and moves V, mutual normalization has
already been excluded. The literal action image of A therefore has order
eight. A transposition in that image has a cyclic preimage B of corank
two in A; the global rank bound puts C_G(B) in Mʸ, while the coordinate
calculation makes C_V(B) a hyperplane. Consequently U=V∩Mʸ is a proper
hyperplane. Applying the weight-four section bound through the inverse
of the same conjugator gives |U:C_U(A)| at most two.

All subgroups of A of corank at most two retain their ambient centralizer
bound in Mʸ. The remaining model step must contradict this entire fixed
space family; these conclusions do not yet prove that W₀(T,V) centralizes
V, nor the product reciprocity theorem or the subsequent graph argument.
The unique-escape premise has its existing universal nonsolvability
producer in EscapingUniqueness; none of its earlier source inputs is
reconstructed here.

Source: Aschbacher–Smith 13.4.16, the weak-closure claim on printed p.913,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A noncentral conjugate contained in M produces the literal corank-two
subgroup and opposite-normalizer hyperplane in the product weak-closure proof. -/
theorem weight_four_returning_hyperplane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hweight : m.weight z = 4)
    (y : G) (hy : V.conjBy y ≤ normalizer (L : Set G))
    (hmove : ⁅V,V.conjBy y⁆ ≠ ⊥) :
    let A := V.conjBy y
    let U := V ⊓ (normalizer (L : Set G)).conjBy y
    (¬ V ≤ (normalizer (L : Set G)).conjBy y) ∧
      (centralizer (V : Set G)).relIndex A = 8 ∧
      U.relIndex V = 2 ∧
      (centralizer (A : Set G)).relIndex U ≤ 2 ∧
      (∀ B : Subgroup G, B ≤ A → ChapterE.subgroupCorank A B ≤ 2 →
        centralizer (B : Set G) ≤ (normalizer (L : Set G)).conjBy y) ∧
      ∃ B : Subgroup G, B ≤ A ∧ ChapterE.subgroupCorank A B = 2 ∧
        centralizer (B : Set G) ≤ (normalizer (L : Set G)).conjBy y ∧
        (centralizer (B : Set G)).relIndex V ≤ 2 := by
  have hinter : ∀ y : G, y ∉ normalizer (L : Set G) → ∀ v : V,
      v ≠ 1 → v.val ∈ V.conjBy y → m.weight v = 4 := by
    intro a ha v hv hvA
    exact (m.conjugate_intersection_weight_of_unique_escape h structural z hz1 hzT hzout
      hunique hfusion a ha v hv hvA).trans hweight
  have hr := m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hunique
  dsimp only
  let A := V.conjBy y
  let U := V ⊓ (normalizer (L : Set G)).conjBy y
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hn := normalizer_component_le_module h structural D m
  have hnot : ¬ V ≤ (normalizer (L : Set G)).conjBy y := fun hh =>
    hmove (weight_four_conjugates_commute_of_mutual_normalization h structural D m hinter y hy hh)
  have hnormal : normalizer (A : Set G) = (normalizer (L : Set G)).conjBy y := by
    rw [normalizer_component_eq_module h structural D m]
    exact (map_equiv_normalizer_eq V (MulAut.conj y)).symm
  have hrA : 3 ≤ ChapterE.globalR A := by
    change 3 ≤ ChapterE.globalR (V.map (MulAut.conj y).toMonoidHom)
    rwa [ChapterE.globalR_map_equiv]
  have hcor : 3 ≤ ChapterE.subgroupCorank A (A ⊓ centralizer (V : Set G)) := by
    have hh := ChapterE.globalR_le_corank (show A ⊓ centralizer (V : Set G) ≤ A from inf_le_left)
      (fun hh => hnot (by
        rw [←hnormal]
        exact (le_centralizer_iff.mpr inf_le_right).trans hh))
    exact_mod_cast hrA.trans hh
  obtain ⟨q,hq,_,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hy)
  have hf (a : A) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨a.val,(hy.trans hn) a.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (f a) (m.coordinate v).toAdd :=
    hq (inclusion hy a) v
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard := model_card_range A V (hy.trans hn)
    (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
    f m.coordinate hf
  rw [inf_relIndex_left] at hcard
  have he : Nat.card f.range = 8 := by
    have hlo : 8 ≤ Nat.card f.range := by
      change 2 ^ 3 ≤ Nat.card f.range
      apply Nat.pow_le_of_le_log Nat.card_pos.ne'
      simpa only [ChapterE.subgroupCorank,inf_relIndex_left,←hcard] using hcor
    have hhi : Nat.card f.range ≤ 8 := hcard.symm ▸ core_elementary_actor_index_le_eight h structural D m A hy
    omega
  obtain ⟨t,ht,hs⟩ := BinaryPermutation.SixCoreWeightFour.eight_contains_swap f.range he.ge
  let B₀ := (zpowers t).comap f
  let B := B₀.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have htcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers,hs.orderOf]
  have htR : zpowers t ≤ f.range := zpowers_le.mpr ht
  have hti : (zpowers t).relIndex f.range = 4 := by
    have hh : Nat.card (zpowers t) * (zpowers t).relIndex f.range = Nat.card f.range := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe htR).toEquiv]
      exact ((zpowers t).subgroupOf f.range).card_mul_index
    rw [htcard,he] at hh
    omega
  have hBi : B.relIndex A = 4 := by
    have heA : A = (⊤ : Subgroup A).map A.subtype := by
      rw [←MonoidHom.range_eq_map,range_subtype]
    change (B₀.map A.subtype).relIndex A = 4
    conv_lhs => arg 2; rw [heA]
    rw [relIndex_map_map_of_injective _ _ A.subtype_injective,relIndex_top_right]
    exact (index_comap _ _).trans hti
  have hBc : ChapterE.subgroupCorank A B = 2 := by rw [ChapterE.subgroupCorank,hBi]; decide
  have hBC : centralizer (B : Set G) ≤ (normalizer (L : Set G)).conjBy y := by
    rw [←hnormal]
    apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hBA
    rw [hBc]
    exact lt_of_lt_of_le (by norm_num) hrA
  let j : B →* A := inclusion hBA
  let fB := f.comp j
  have hfB (b : B) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨b.val,(hBA.trans (hy.trans hn)) b.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (fB b) (m.coordinate v).toAdd := hf (j b) v
  have hBR : fB.range = zpowers t := by
    apply le_antisymm
    · rintro _ ⟨b,rfl⟩
      obtain ⟨a,ha,he⟩ := b.property
      have hj : j b = a := Subtype.ext he.symm
      change f (j b) ∈ zpowers t
      rw [hj]
      exact ha
    · intro a ha
      obtain ⟨b,hb⟩ := htR ha
      refine ⟨⟨b.val,⟨b,?_,rfl⟩⟩,hb⟩
      change f b ∈ zpowers t
      rwa [hb]
  have hsmall : (centralizer (B : Set G)).relIndex V ≤ 2 := by
    rw [model_fixed_index B V (hBA.trans (hy.trans hn))
      (BinaryPermutation.coreRepresentation (Fin 6)) fB m.coordinate hfB,hBR]
    exact Nat.pow_le_pow_right (by decide : 0 < 2)
      (BinaryPermutation.SixCoreWeightFour.swap_fixedCodim_le_one t hs)
  have hUi : U.relIndex V ≤ 2 := by
    have hc : V ⊓ centralizer (B : Set G) ≤ U := inf_le_inf_left V hBC
    have hh := relIndex_le_of_le_left (L := V) hc (by exact index_ne_zero_of_finite)
    apply hh.trans
    simpa only [inf_relIndex_left] using hsmall
  have hUne : U.relIndex V ≠ 1 := fun he => hnot
    ((relIndex_eq_one.mp he).trans inf_le_right)
  have hUpos : U.relIndex V ≠ 0 := index_ne_zero_of_finite
  have hyout : y ∉ normalizer (L : Set G) := by
    intro hh
    apply hnot
    have hconj : V.conjBy y = V := mem_normalizer_iff_map_conj_eq.mp (hn hh)
    rw [←hconj]
    exact map_mono (D.le_sylow.trans D.sylow_normalizes_component)
  have hUy : U.conjBy y⁻¹ ≤ V.conjBy y⁻¹ := map_mono inf_le_left
  have hUM : U.conjBy y⁻¹ ≤ normalizer (L : Set G) := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) (show U ≤ (normalizer (L : Set G)).conjBy y from inf_le_right)
    change U.conjBy y⁻¹ ≤ ((normalizer (L : Set G)).conjBy y).conjBy y⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hVM : V ≤ (normalizer (L : Set G)).conjBy y⁻¹ := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hy
    change (V.conjBy y).conjBy y⁻¹ ≤ (normalizer (L : Set G)).conjBy y⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hsU := weight_four_section_actor_index h structural D m hinter y⁻¹
    (fun hi => hyout (inv_mem_iff.mp hi)) (U.conjBy y⁻¹) hUy hUM hVM
  have hidx : (centralizer (A : Set G)).relIndex U =
      (centralizer (V : Set G)).relIndex (U.conjBy y⁻¹) := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj y).toMonoidHom) (centralizer (V : Set G)) (U.conjBy y⁻¹)
      (MulAut.conj y).injective
    rw [Theory.GroupTheory.map_centralizer_equiv (V : Set G) (MulAut.conj y)] at hh
    change (centralizer (A : Set G)).relIndex ((U.conjBy y⁻¹).conjBy y) = _ at hh
    rwa [conjBy_inv'] at hh
  have hfamily (C : Subgroup G) (hCA : C ≤ A) (hc : ChapterE.subgroupCorank A C ≤ 2) :
      centralizer (C : Set G) ≤ (normalizer (L : Set G)).conjBy y := by
    rw [←hnormal]
    apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hCA
    exact lt_of_lt_of_le (by exact_mod_cast (show ChapterE.subgroupCorank A C < 3 by omega)) hrA
  refine ⟨hnot,hcard.symm.trans he,?_,hidx.symm ▸ hsU,hfamily,B,hBA,hBc,hBC,hsmall⟩
  change U.relIndex V = 2
  omega
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
