module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Marked
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.SourceSet
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ModelFacts
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.Choices
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ActionImage
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Selection
public import CFSG.Quasithin.Chapter16.Section01To02.Local
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
import Mathlib.Tactic

/-!
# Compatible placement and simultaneous marked overgroups for A₆

Recoordinate the supplied product model by conjugation inside LE to place its
marked elementary sixteen-group in the original Sylow subgroup T. This retains
L, z and r, including the required image and cycle type of r.

For each marked generator c, start with a conjugator taking z to c. Sylow
conjugacy inside C_G(c) corrects this conjugator so that the whole elementary
group lies in the corresponding conjugate of T. To obtain containment in the
conjugate of LE, use the actual action on L: its kernel on any subgroup of T
has order at most two, and elementary eight-subgroups of Aut(A₆) lie in the
natural S₆. A Sylow order comparison pulls that containment back to LE.
Thus all four generators lie in one conjugate of LE centered at c.

This proves the geometric construction used in source 16.4.9(2), without
assuming the class-containment assertion in that proof, fusion exclusions,
or any further source premises. The source theorem's contradiction and final
assembly remain separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section

open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter16.Intersections.Six.MarkedPlacement
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- Conjugate the coordinates inside LE while retaining the original L, z and r. -/
def recoordinate (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) : AlternatingProductModel L z r 6 where
  equiv := M.equiv.trans (MulAut.conj (M.equiv a)⁻¹)
  component_iff b := by
    rw [M.component_iff b]
    change _ ↔ ((M.equiv a)⁻¹ * M.equiv b * ((M.equiv a)⁻¹)⁻¹).1 ∈ _ ∧
      ((M.equiv a)⁻¹ * M.equiv b * ((M.equiv a)⁻¹)⁻¹).2 = 1
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, inv_inv]
    rw [show (M.equiv a).2⁻¹ * (M.equiv b).2 * (M.equiv a).2 = (M.equiv b).2 by
      calc
        _ = (M.equiv b).2 * ((M.equiv a).2⁻¹ * (M.equiv a).2) := by ac_rfl
        _ = _ := by rw [inv_mul_cancel, mul_one]]
    apply and_congr _ Iff.rfl
    rw [mem_alternatingGroup, mem_alternatingGroup, map_mul, map_mul, map_inv]
    rw [show (sign (M.equiv a).1)⁻¹ * sign (M.equiv b).1 * sign (M.equiv a).1 =
        sign (M.equiv b).1 by
      calc
        _ = sign (M.equiv b).1 * ((sign (M.equiv a).1)⁻¹ * sign (M.equiv a).1) := by ac_rfl
        _ = _ := by rw [inv_mul_cancel, mul_one]]
  central_image := by
    change (M.equiv a)⁻¹ * M.equiv _ * ((M.equiv a)⁻¹)⁻¹ = _
    rw [M.central_image]
    ext <;> simp [mul_comm, mul_left_comm]
  outer_second := by
    change ((M.equiv a)⁻¹ * M.equiv _ * ((M.equiv a)⁻¹)⁻¹).2 = 1
    simp only [Prod.snd_mul, Prod.snd_inv, M.outer_second, mul_one, mul_inv_cancel]
  outer_cycleType := by
    left
    change (((M.equiv a).1)⁻¹ * outerPermutation M * (((M.equiv a).1)⁻¹)⁻¹).cycleType = {2}
    exact (isConj_iff_cycleType_eq.mp (isConj_iff.mpr ⟨(M.equiv a).1⁻¹, rfl⟩)).symm.trans
      (outerPermutation_cycleType M)

/-- The binary embedding changes by the chosen ambient conjugation. -/
theorem recoordinate_embedding (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) (v : Binary) :
    embedding (recoordinate M a) v = MulAut.conj (a : G) (embedding M v) := by
  change (M.equiv.symm ((MulAut.conj (M.equiv a)⁻¹).symm (coordinateHom v)) : G) = _
  rw [MulAut.conj_symm_apply]
  simp only [inv_inv, map_mul, map_inv, M.equiv.symm_apply_apply]
  rfl

/-- Recoordination conjugates the elementary subgroup inside the same LE. -/
theorem recoordinate_elementary (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) :
    elementary (recoordinate M a) = (elementary M).conjBy (a : G) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨embedding M v, ⟨v, rfl⟩, (recoordinate_embedding M a v).symm⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, recoordinate_embedding M a v⟩

variable [Finite G] {T : Sylow 2 G}

/-- Since T normalizes L and contains r and z, its intersection with LE is Sylow in LE. -/
theorem sylow_intersection (h : StandardSetup T z L) (hr : r ∈ T) :
    SylowIn ((T : Subgroup G) ⊓ AlternatingOvergroup L z r) (AlternatingOvergroup L z r) := by
  let Q := (T : Subgroup G) ⊓ AlternatingOvergroup L z r
  have he : L ⊔ Q = AlternatingOvergroup L z r := by
    apply le_antisymm (sup_le (le_sup_left.trans le_sup_left) inf_le_right)
    apply sup_le
    · apply sup_le le_sup_left
      exact zpowers_le.mpr (mem_sup_right ⟨hr, mem_sup_left (mem_sup_right (mem_zpowers r))⟩)
    · exact zpowers_le.mpr (mem_sup_right ⟨h.mem_sylow, mem_sup_right (mem_zpowers z)⟩)
  obtain ⟨P, hP⟩ := h.toCentralComponentSetup.exists_component_sylow
  have hS : SylowIn Q (L ⊔ Q) := IsPGroup.exists_sylow_sup_of_coprime_index L Q
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans h.sylow_normalizes)
    (P : Subgroup L) P.not_dvd_index (by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨?_, mem_sup_left (mem_sup_left a.property)⟩
      change a ∈ (T : Subgroup G).subgroupOf L
      rwa [← hP])
  rw [he] at hS
  exact hS

/-- Place the marked elementary subgroup in the supplied T without replacing L. -/
theorem exists_placement (h : StandardSetup T z L) (hr : r ∈ T)
    (M : AlternatingProductModel L z r 6) :
    ∃ M' : AlternatingProductModel L z r 6, elementary M' ≤ T := by
  obtain ⟨a, ha, hA⟩ := (sylow_intersection h hr).exists_conjugate_le
    (IsElementaryAbelian.isPGroup 2 (elementary M)) (elementary_le M)
  refine ⟨recoordinate M ⟨a, ha⟩, ?_⟩
  rw [recoordinate_elementary]
  exact hA.trans inf_le_left
open AlternatingSix.ShadowLocal

private noncomputable def restrictedAction (M : AlternatingProductModel L z r 6)
    {Q : Subgroup G} (hQ : Q ≤ normalizer (L : Set G)) : Q →* AutA6 :=
  (modelNormalizerAction M).comp (inclusion hQ)

omit [Finite G] in
private theorem restrictedAction_ker (M : AlternatingProductModel L z r 6)
    {Q : Subgroup G} (hQ : Q ≤ normalizer (L : Set G)) :
    (restrictedAction M hQ).ker = (centralizer (L : Set G)).subgroupOf Q := by
  ext a
  change (MulAut.congr (modelComponentEquiv M)) (L.normalizerMonoidHom
    ⟨a, hQ a.property⟩) = 1 ↔ (a : G) ∈ centralizer (L : Set G)
  rw [← map_one (MulAut.congr (modelComponentEquiv M)),
    (MulAut.congr (modelComponentEquiv M)).injective.eq_iff]
  change ⟨a, hQ a.property⟩ ∈ L.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

private theorem restrictedAction_ker_card_le (h : StandardSetup T z L)
    (hTC : commutingSylow T L = zpowers z) (M : AlternatingProductModel L z r 6)
    {Q : Subgroup G} (hQ : Q ≤ (T : Subgroup G)) :
    Nat.card (restrictedAction M (hQ.trans h.sylow_normalizes)).ker ≤ 2 := by
  rw [restrictedAction_ker]
  have hle : ((centralizer (L : Set G)).subgroupOf Q).map Q.subtype ≤ zpowers z := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hTC]
    exact ⟨hQ a.property, ha⟩
  have hc := card_le_of_le hle
  rw [card_map_of_injective Q.subtype_injective, Nat.card_zpowers, h.involution] at hc
  exact hc

private theorem natural_pgroup_card_le {Q : Subgroup AutA6}
    (hp : IsPGroup 2 Q) (hQ : Q ≤ natural) : Nat.card Q ≤ 16 := by
  obtain ⟨S, hS⟩ := (hp.of_equiv (subgroupOfEquivOfLe hQ).symm).exists_le_sylow
  have hc := card_le_of_le hS
  have he : Nat.card (Q.subgroupOf natural) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv
  rw [he, S.card_eq_multiplicity, card_natural] at hc
  rw [show 720 = 2 ^ 4 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)] at hc
  exact hc

/-- The supplied S₆ × C₂ model gives a Sylow intersection of order 32. -/
theorem sylow_intersection_card (h : StandardSetup T z L) (hr : r ∈ T)
    (M : AlternatingProductModel L z r 6) :
    Nat.card ((T : Subgroup G) ⊓ AlternatingOvergroup L z r : Subgroup G) = 32 := by
  obtain ⟨S, hS⟩ := sylow_intersection h hr
  rw [← hS, card_map_of_injective (AlternatingOvergroup L z r).subtype_injective,
    S.card_eq_multiplicity, Nat.card_congr M.equiv.toEquiv]
  have hc : Nat.card Product = 1440 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial, Nat.card_eq_fintype_card]
  change 2 ^ (Nat.card Product).factorization 2 = 32
  rw [hc]
  rw [show 1440 = 2 ^ 5 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rfl

private theorem natural_preimage_le (h : StandardSetup T z L)
    (hTC : commutingSylow T L = zpowers z) (hr : r ∈ T)
    (M : AlternatingProductModel L z r 6) :
    (natural.comap (restrictedAction M h.sylow_normalizes)).map
      (T : Subgroup G).subtype ≤ AlternatingOvergroup L z r := by
  let P := natural.comap (restrictedAction M h.sylow_normalizes)
  let Q := P.map (T : Subgroup G).subtype
  have hQT : Q ≤ (T : Subgroup G) := map_subtype_le P
  let f := restrictedAction M (hQT.trans h.sylow_normalizes)
  have hrange : f.range ≤ natural := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb, hab⟩ := a.property
    have he : (⟨a, hQT a.property⟩ : T) = b := Subtype.ext hab.symm
    change restrictedAction M h.sylow_normalizes ⟨a, hQT a.property⟩ ∈ natural
    rw [he]
    exact hb
  have hpr : IsPGroup 2 f.range :=
    (T.isPGroup'.to_le hQT).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hrc := natural_pgroup_card_le hpr hrange
  have hkc := restrictedAction_ker_card_le h hTC M hQT
  have hcard : Nat.card Q ≤ 32 := by
    have hc := f.ker.card_mul_index
    rw [index_ker] at hc
    nlinarith
  have hle : (T : Subgroup G) ⊓ AlternatingOvergroup L z r ≤ Q := by
    intro a ha
    refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
    change modelNormalizerAction M ⟨a, h.sylow_normalizes ha.1⟩ ∈ natural
    rw [modelNormalizerAction_on_overgroup M ⟨a, ha.2⟩]
    exact ⟨_, rfl⟩
  have he : (T : Subgroup G) ⊓ AlternatingOvergroup L z r = Q :=
    eq_of_le_of_card_ge hle (hcard.trans (sylow_intersection_card h hr M).symm.le)
  change Q ≤ _
  rw [← he]
  exact inf_le_right

/-- Every elementary sixteen-subgroup of T lies in the actual product overgroup LE. -/
theorem elementary_sixteen_le_overgroup (h : StandardSetup T z L)
    (hTC : commutingSylow T L = zpowers z) (hr : r ∈ T)
    (M : AlternatingProductModel L z r 6) {Q : Subgroup G}
    [IsElementaryAbelian 2 Q] (hQ : Q ≤ (T : Subgroup G)) (hc : Nat.card Q = 16) :
    Q ≤ AlternatingOvergroup L z r := by
  let f := restrictedAction M (hQ.trans h.sylow_normalizes)
  have hkc := restrictedAction_ker_card_le h hTC M hQ
  have hrc : 8 ≤ Nat.card f.range := by
    have he := f.ker.card_mul_index
    rw [index_ker, hc] at he
    nlinarith
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hf := elementary_le_natural_of_eight_le f.range hrc
  intro a ha
  apply natural_preimage_le h hTC hr M
  refine ⟨⟨a, hQ ha⟩, ?_, rfl⟩
  exact hf ⟨⟨a, ha⟩, rfl⟩

open scoped IsMulCommutative

/-- Correct the conjugator at each marked point so one conjugate of LE contains all four points. -/
theorem marked_overgroups (h : StandardSetup T z L)
    (hTC : commutingSylow T L = zpowers z) (hr : r ∈ T)
    (M : AlternatingProductModel L z r 6) (hconj : IsConj z r) :
    MarkedOvergroups M := by
  classical
  intro k
  have hc : IsConj z (generator M k) :=
    (alpha_subset_beta M hconj (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)).2
  obtain ⟨a, ha⟩ := isConj_iff.mp hc
  have ha' : MulAut.conj a z = generator M k := ha
  have hainv : MulAut.conj a⁻¹ (generator M k) = z := by
    rw [← ha']
    simp [MulAut.conj_apply, mul_assoc]
  let Q := (elementary M).conjBy a⁻¹
  have hQC : Q ≤ involutionCentralizer z := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hainv]
    have hcomm : Commute (generator M k) b :=
      congrArg Subtype.val (mul_comm (⟨generator M k, generator_mem M k⟩ : elementary M) ⟨b, hb⟩)
    exact (hcomm.map (MulAut.conj a⁻¹).toMonoidHom).symm
  have hSyl : SylowIn (T : Subgroup G) (involutionCentralizer z) :=
    ⟨T.subtype h.sylow_centralizes, map_subgroupOf_eq_of_le h.sylow_centralizes⟩
  obtain ⟨b, hb, hQT⟩ := hSyl.exists_conjugate_le
    ((IsElementaryAbelian.isPGroup 2 (elementary M)).map (MulAut.conj a⁻¹).toMonoidHom) hQC
  let y := b * a⁻¹
  have hAT : (elementary M).conjBy y ≤ (T : Subgroup G) := by
    change ((elementary M).conjBy a⁻¹).conjBy b ≤ (T : Subgroup G) at hQT
    simpa only [conjBy_conjBy] using hQT
  let : IsElementaryAbelian 2 ((elementary M).conjBy y) :=
    IsElementaryAbelian.map (MulAut.conj y).toMonoidHom
  have hcard : Nat.card ((elementary M).conjBy y) = 16 := by
    rw [conjBy, card_map_of_injective (MulAut.conj y).injective, elementary_card]
  have hALE := elementary_sixteen_le_overgroup h hTC hr M hAT hcard
  have hA : elementary M ≤ (AlternatingOvergroup L z r).conjBy y⁻¹ := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hALE
    change ((elementary M).conjBy y).conjBy y⁻¹ ≤
      (AlternatingOvergroup L z r).conjBy y⁻¹ at hh
    rwa [conjBy_inv] at hh
  refine ⟨y⁻¹, ?_, component_central_conj_relIndex M y⁻¹, fun i => hA (generator_mem M i)⟩
  have hbz : MulAut.conj b z = z := by
    have hb' := mem_centralizer_singleton_iff.mp hb
    change b * z * b⁻¹ = z
    rw [hb', mul_inv_cancel_right]
  have hy : MulAut.conj y (generator M k) = z := by
    calc
      _ = MulAut.conj b (MulAut.conj a⁻¹ (generator M k)) := by
        simp only [y, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
      _ = z := by rw [hainv, hbz]
  have hi := congrArg (MulAut.conj y⁻¹) hy
  simpa [MulAut.conj_apply, mul_assoc] using hi.symm

/-- Compatible marked placement for the A₆ branch of source 16.4.9(2).
All containments retain the original ambient group, component and Sylow subgroup. -/
theorem exists_marked_placement {g : G} {R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hTC : commutingSylow T L = zpowers z) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (M : AlternatingProductModel L z r 6) :
    ∃ M' : AlternatingProductModel L z r 6,
      elementary M' ≤ (T : Subgroup G) ∧ MarkedOvergroups M' := by
  obtain ⟨M', hM'⟩ := exists_placement h.toStandardSetup (h.le_sylow hr) M
  exact ⟨M', hM', marked_overgroups h.toStandardSetup hTC (h.le_sylow hr) M'
    (conjugate_outer h hTC hr hr2)⟩

end CFSG.Quasithin.Chapter16.Intersections.Six.MarkedPlacement
