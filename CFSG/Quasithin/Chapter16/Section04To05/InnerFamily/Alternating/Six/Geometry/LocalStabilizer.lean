module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Marked
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.SourceSet
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Action
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ModelFacts
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ActionImage
import Mathlib.Tactic

/-!
# The order-six stabilizer in the marked A₆ action

Tight embedding puts C_G(z) in N_G(L). The product exclusions restrict each
image of a mark to the four marks and their total product. Products of two
noncentral marks lie in L, whereas the total product times any mark does not.
Thus an actual normalizer actor fixing z permutes the other three marks.
Their action is faithful because the four marks generate the elementary group.

Conversely, permuting the three disjoint coordinate pairs gives even
permutations of six letters. Lifting through the supplied product model gives
actors in L normalizing the elementary subgroup and fixing z. They realize
all of S₃, so the stabilizer in the faithful action on β has order six.

The theorem is conditional on the actual marked model, z ∼ r, and the pair
and triple exclusions. The source assembly owns those inputs. No fusion of
the total product, five-point cardinality, or transitivity is needed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209). As in `Six.Marked`, β is
the corrected set zᴳ ∩ A.
-/

open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six
namespace LocalStabilizer

private def pairPerm (p : Perm (Fin 3)) : Perm (Fin 6) :=
  finProdFinEquiv.permCongr (Equiv.prodCongr p (Equiv.refl (Fin 2)))

private def markPerm (p : Perm (Fin 3)) : Perm (Fin 4) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr p (Equiv.refl (Fin 1)))

private theorem pairPerm_even (p : Perm (Fin 3)) : pairPerm p ∈ alternatingGroup (Fin 6) := by
  rw [mem_alternatingGroup]
  revert p; decide +kernel

private theorem pairPerm_conjugation (p : Perm (Fin 3)) (i : Fin 4) :
    MulAut.conj (pairPerm p, (1 : Multiplicative (ZMod 2))) (coordinateHom (basis i)) =
      coordinateHom (basis (markPerm p i)) := by
  revert p i; decide +kernel

private theorem markPerm_three (p : Perm (Fin 3)) : markPerm p 3 = 3 := by
  revert p; decide +kernel

private theorem markPerm_castSucc (p : Perm (Fin 3)) (i : Fin 3) :
    markPerm p i.castSucc = (p i).castSucc := by
  revert p i; decide +kernel

private theorem coordinate_pair_component (i j : Fin 3) :
    (coordinateHom (basis i.castSucc * basis j.castSucc)).1 ∈ alternatingGroup (Fin 6) ∧
      (coordinateHom (basis i.castSucc * basis j.castSucc)).2 = 1 := by
  simp only [mem_alternatingGroup]
  revert i j; decide +kernel

private theorem coordinate_total_pair_not_component (i : Fin 4) :
    ¬ ((coordinateHom (totalVector * basis i)).1 ∈ alternatingGroup (Fin 6) ∧
      (coordinateHom (totalVector * basis i)).2 = 1) := by
  simp only [mem_alternatingGroup]
  revert i; decide +kernel


variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

private theorem generator_pair_component (M : AlternatingProductModel L z r 6) (i j : Fin 3) :
    generator M i.castSucc * generator M j.castSucc ∈ L := by
  change (embedding M (basis i.castSucc)) * (embedding M (basis j.castSucc)) ∈ L
  rw [← map_mul]
  exact (M.component_iff _).mpr (by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, M.equiv.apply_symm_apply]
    exact coordinate_pair_component i j)

private theorem total_mul_generator_not_component (M : AlternatingProductModel L z r 6) (i : Fin 4) :
    total M * generator M i ∉ L := by
  change embedding M totalVector * embedding M (basis i) ∉ L
  rw [← map_mul]
  intro hh
  have hc := (M.component_iff _).mp hh
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, M.equiv.apply_symm_apply] at hc
  exact coordinate_total_pair_not_component i hc

private theorem conjugate_generator (M : AlternatingProductModel L z r 6)
    (hr : IsConj z r) (hex : ProductExclusions M)
    (n : normalizer (elementary M : Set G)) (hnL : (n : G) ∈ normalizer (L : Set G))
    (hz : MulAut.conj (n : G) z = z) (i : Fin 3) :
    ∃ j : Fin 3, MulAut.conj (n : G) (generator M i.castSucc) = generator M j.castSucc := by
  classical
  have hb (k : Fin 3) : MulAut.conj (n : G) (generator M k.castSucc) ∈ beta M :=
    (conjugate_mem_beta_iff M n _).mpr
      (alpha_subset_beta M hr (Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩))
  have ha : MulAut.conj (n : G) (generator M i.castSucc) ∈ alpha M := by
    rcases beta_subset M hex.1 hex.2 (hb i) with ha | ht
    · exact ha
    · change MulAut.conj (n : G) (generator M i.castSucc) = total M at ht
      obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j :=
        (by decide : ∀ i : Fin 3, ∃ j : Fin 3, i ≠ j) i
      have hprod : MulAut.conj (n : G) (generator M i.castSucc) *
          MulAut.conj (n : G) (generator M j.castSucc) ∈ L := by
        rw [← map_mul]
        exact (hnL _).mp (generator_pair_component M i j)
      rcases beta_subset M hex.1 hex.2 (hb j) with hj | hj
      · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
        rw [ht, ← hk] at hprod
        exact (total_mul_generator_not_component M k hprod).elim
      · have he : generator M i.castSucc = generator M j.castSucc :=
          (MulAut.conj (n : G)).injective (ht.trans hj.symm)
        exact (hij (Fin.castSucc_injective 3 (generator_injective M he))).elim
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
  have hj3 : j ≠ 3 := by
    intro he
    have hji : generator M i.castSucc = generator M 3 := by
      apply (MulAut.conj (n : G)).injective
      rw [generator_three, hz, ← hj, he, generator_three]
    have hf := generator_injective M hji
    exact Fin.castSucc_ne_last i hf
  have hjlt : j.val < 3 := by omega
  refine ⟨⟨j.val, hjlt⟩, ?_⟩
  simpa only [Fin.castSucc_mk] using hj.symm

private def point (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (i : Fin 3) : beta M :=
  ⟨generator M i.castSucc,
    alpha_subset_beta M hr (by
      classical
      exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩)⟩

private theorem stabilizer_lift (M : AlternatingProductModel L z r 6)
    (s : normalizerStabilizer M) :
    ∃ n : normalizer (elementary M : Set G), normalizerAction M n = s.val.val ∧
      MulAut.conj (n : G) z = z := by
  obtain ⟨n, hn⟩ := s.val.property
  refine ⟨n, hn, ?_⟩
  have hs : s.val.val (markedPoint M) = markedPoint M := s.property
  rw [← hn] at hs
  exact congrArg Subtype.val hs

private theorem centralizer_normalizes [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, h.involution, pow_one])
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hzC : z ∈ centralizer (L : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hn := h.tight.normalizer_le hp (zpowers_ne_bot.mpr hz1) (zpowers_le.mpr hzC)
  rwa [h.normalizers_eq, normalizer_zpowers_eq_centralizer_of_order_two z h.involution] at hn

private theorem stabilizer_preserves [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (s : normalizerStabilizer M) (i : Fin 3) :
    ∃ j : Fin 3, (s.val.val (point M hr i) : G) = generator M j.castSucc := by
  obtain ⟨n, hn, hz⟩ := stabilizer_lift M s
  rw [← hn]
  apply conjugate_generator M hr hex n _ hz i
  apply centralizer_normalizes h
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz)

private theorem point_injective (M : AlternatingProductModel L z r 6) (hr : IsConj z r) :
    Function.Injective (point M hr) := by
  intro i j he
  exact Fin.castSucc_injective 3 (generator_injective M (congrArg (fun a : beta M => (a : G)) he))

private noncomputable def indexMap [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (s : normalizerStabilizer M) (i : Fin 3) : Fin 3 :=
  Classical.choose (stabilizer_preserves h M hr hex s i)

private theorem indexMap_spec [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (s : normalizerStabilizer M) (i : Fin 3) :
    s.val.val (point M hr i) = point M hr (indexMap h M hr hex s i) :=
  Subtype.ext (Classical.choose_spec (stabilizer_preserves h M hr hex s i))

private theorem indexMap_injective [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (s : normalizerStabilizer M) : Function.Injective (indexMap h M hr hex s) := by
  intro i j hij
  apply point_injective M hr
  apply s.val.val.injective
  rw [indexMap_spec h M hr hex, indexMap_spec h M hr hex, hij]

private noncomputable def restriction [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (s : normalizerStabilizer M) : Perm (Fin 3) :=
  Equiv.ofBijective (indexMap h M hr hex s)
    ⟨indexMap_injective h M hr hex s,
      Finite.surjective_of_injective (indexMap_injective h M hr hex s)⟩

private theorem restriction_spec [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (s : normalizerStabilizer M) (i : Fin 3) :
    s.val.val (point M hr i) = point M hr (restriction h M hr hex s i) :=
  indexMap_spec h M hr hex s i

private theorem restriction_injective [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M) :
    Function.Injective (restriction h M hr hex) := by
  intro s t hst
  obtain ⟨n, hn, hnz⟩ := stabilizer_lift M s
  obtain ⟨m, hm, hmz⟩ := stabilizer_lift M t
  have hg (i : Fin 4) : MulAut.conj (n : G) (generator M i) =
      MulAut.conj (m : G) (generator M i) := by
    by_cases hi : i = 3
    · rw [hi, generator_three, hnz, hmz]
    · have hil : i.val < 3 := by omega
      let j : Fin 3 := ⟨i.val, hil⟩
      have hj : j.castSucc = i := rfl
      have he : s.val.val (point M hr j) = t.val.val (point M hr j) := by
        rw [restriction_spec h M hr hex, restriction_spec h M hr hex, hst]
      rw [← hn, ← hm] at he
      simpa only [normalizerAction_apply, point, hj] using congrArg Subtype.val he
  have he : Set.EqOn (MulAut.conj (n : G)).toMonoidHom
      (MulAut.conj (m : G)).toMonoidHom (alpha M : Set G) := by
    classical
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hg i
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [← hn, ← hm]
  apply MonoidHom.eqOn_closure he
  rw [← elementary_eq_closure]
  exact a.property.1

private def actor (M : AlternatingProductModel L z r 6) (p : Perm (Fin 3)) : L :=
  ⟨lift M (pairPerm p, 1), lift_even_mem M (pairPerm p) (pairPerm_even p)⟩

private theorem actor_conjugation (M : AlternatingProductModel L z r 6)
    (p : Perm (Fin 3)) (i : Fin 4) :
    MulAut.conj (actor M p : G) (generator M i) = generator M (markPerm p i) := by
  change lift M (pairPerm p, 1) * lift M (coordinateHom (basis i)) *
    (lift M (pairPerm p, 1))⁻¹ = lift M (coordinateHom (basis (markPerm p i)))
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg (lift M) (pairPerm_conjugation p i)

private theorem actor_normalizes (M : AlternatingProductModel L z r 6) (p : Perm (Fin 3)) :
    (actor M p : G) ∈ normalizer (elementary M : Set G) := by
  classical
  rw [elementary_eq_closure]
  apply normalizer_le_normalizer_closure
  apply mem_normalizer_iff_conj_image_eq.mpr
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    rw [actor_conjugation]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨generator M ((markPerm p).symm i),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [actor_conjugation, (markPerm p).apply_symm_apply]

private theorem actor_fixes (M : AlternatingProductModel L z r 6) (p : Perm (Fin 3)) :
    MulAut.conj (actor M p : G) z = z := by
  simpa only [markPerm_three, generator_three] using actor_conjugation M p 3

private def actorStabilizer (M : AlternatingProductModel L z r 6) (p : Perm (Fin 3)) :
    normalizerStabilizer M :=
  ⟨⟨normalizerAction M ⟨(actor M p : G), actor_normalizes M p⟩,
      ⟨⟨(actor M p : G), actor_normalizes M p⟩, rfl⟩⟩,
    show normalizerAction M ⟨(actor M p : G), actor_normalizes M p⟩ (markedPoint M) =
      markedPoint M from Subtype.ext (actor_fixes M p)⟩

private theorem restriction_actor [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M)
    (p : Perm (Fin 3)) : restriction h M hr hex (actorStabilizer M p) = p := by
  apply Equiv.ext
  intro i
  apply point_injective M hr
  rw [← restriction_spec]
  apply Subtype.ext
  change MulAut.conj (actor M p : G) (generator M i.castSucc) = generator M (p i).castSucc
  rw [actor_conjugation, markPerm_castSucc]

end LocalStabilizer

variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- The actual faithful point stabilizer has order six. Tight embedding and the
product exclusions force its action on the three noncentral marks; permutations
of their coordinate pairs realize all six possibilities inside the component. -/
public theorem normalizerStabilizer_card [Finite G] {T : Sylow 2 G} (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 6) (hr : IsConj z r) (hex : ProductExclusions M) :
    Nat.card (normalizerStabilizer M) = 6 := by
  have hs : Function.Surjective (LocalStabilizer.restriction h M hr hex) :=
    fun p => ⟨LocalStabilizer.actorStabilizer M p, LocalStabilizer.restriction_actor h M hr hex p⟩
  rw [Nat.card_congr (Equiv.ofBijective (LocalStabilizer.restriction h M hr hex)
    ⟨LocalStabilizer.restriction_injective h M hr hex, hs⟩), Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

end CFSG.Quasithin.Chapter16.Intersections.Six
