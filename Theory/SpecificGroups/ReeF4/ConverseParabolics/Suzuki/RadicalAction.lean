module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.RadicalAction.SeedAndTorus
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Self-centralization of the radical in the full Suzuki Ree parabolic

Let Q be the actual root radical and L the full fixed middle-node Levi.
Conjugation on Q modulo its own commutator subgroup has a normal kernel K
in L. The simple Suzuki seed acts nontrivially, by the explicit middle-torus
actor, so K meets that seed trivially. The complementary torus is detected
by its scalar on the fixed end-root curve.

The seed and complementary torus commute and intersect trivially because
the Suzuki group has trivial center. Their product embeds in L. A supplied
injective homomorphism from L to Suzuki matrices times field units bounds
its cardinality, making this product surjective. Normality then forces K
to centralize the seed, hence lie in the complementary torus, where it is
trivial. The radical–Levi centralizer reduction proves the relative bound.

The representation is deliberately an explicit premise; its independent
construction belongs to the full-Levi representation owner. No compatibility
with the factor maps, Ree order formula, or Ree simplicity premise is needed.
This establishes the conditional contract consumed by the full-parabolic
assembly, not all clauses of the cited source theorems.

Source: GLS3, Theorem 2.6.5(e,g) and §3.2, and the Suzuki local factor in
Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

open Subgroup
open scoped commutatorElement
namespace ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
noncomputable section
attribute [local instance] suzuki_intrinsicRadical_normal

/-- Kernel of the full Levi action on the radical modulo its commutator. -/
private def actionKernel (m : ℕ) : Subgroup (fullLevi m) :=
  let Q := intrinsicRadical m .suzuki
  let f := QuotientGroup.mk' ⁅Q, Q⁆
  (centralizer (Q.map f : Set (parabolic m .suzuki ⧸ ⁅Q, Q⁆))).comap
    (f.comp (Subgroup.inclusion (suzuki_fullLevi_le_parabolic m)))

private instance actionKernel_normal (m : ℕ) : (actionKernel m).Normal := by
  let Q := intrinsicRadical m .suzuki
  let f := QuotientGroup.mk' ⁅Q, Q⁆
  have : (Q.map f).Normal := Subgroup.Normal.map inferInstance f
    (QuotientGroup.mk'_surjective _)
  exact Subgroup.Normal.comap inferInstance _

private theorem intrinsic_commutator_mem_iff (m : ℕ) (x : parabolic m .suzuki) :
    x ∈ ⁅intrinsicRadical m .suzuki, intrinsicRadical m .suzuki⁆ ↔
      x.val ∈ ⁅radical m .suzuki, radical m .suzuki⁆ := by
  let Q := intrinsicRadical m .suzuki
  have he : (⁅Q, Q⁆).map (parabolic m .suzuki).subtype =
      ⁅radical m .suzuki, radical m .suzuki⁆ := by
    rw [map_commutator]
    have hq : Q.map (parabolic m .suzuki).subtype = radical m .suzuki :=
      map_subgroupOf_eq_of_le (radical_le_parabolic m .suzuki)
    rw [hq]
  rw [← he]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy

private theorem mem_actionKernel_iff (m : ℕ) (l : fullLevi m) :
    l ∈ actionKernel m ↔ ActsTriviallyOnRadicalAbelianization m l.val := by
  let Q := intrinsicRadical m .suzuki
  let f := QuotientGroup.mk' ⁅Q, Q⁆
  change f (Subgroup.inclusion (suzuki_fullLevi_le_parabolic m) l) ∈ centralizer (Q.map f : Set _) ↔ _
  rw [mem_centralizer_iff]
  constructor
  · intro h q hq
    let qP : parabolic m .suzuki := ⟨q, radical_le_parabolic m .suzuki hq⟩
    have he := h (f qP) (mem_map_of_mem f (show qP ∈ Q from hq))
    have hc : f ⁅Subgroup.inclusion (suzuki_fullLevi_le_parabolic m) l, qP⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact he.symm
    exact (intrinsic_commutator_mem_iff m _).mp ((QuotientGroup.eq_one_iff _).mp hc)
  · rintro h _ ⟨q, hq, rfl⟩
    have hc := (intrinsic_commutator_mem_iff m ⁅Subgroup.inclusion (suzuki_fullLevi_le_parabolic m) l, q⁆).mpr
      (h q.val hq)
    have he : f ⁅Subgroup.inclusion (suzuki_fullLevi_le_parabolic m) l, q⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at he
    exact he.symm

end
end ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction

open Subgroup
open scoped commutatorElement
namespace ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction

variable {S T L : Type*} [Group S] [Group T] [Group L] [Finite S] [Finite T] [Finite L]

theorem normal_eq_bot_of_two_factors
    (i : S →* L) (j : T →* L) (hi : Function.Injective i) (hj : Function.Injective j)
    (hcomm : ∀ s t, Commute (i s) (j t)) (hcenter : center S = ⊥)
    (ρ : L →* S × T) (hρ : Function.Injective ρ)
    (K : Subgroup L) [K.Normal]
    (hKS : ∀ s, i s ∈ K → s = 1) (hKT : ∀ t, j t ∈ K → t = 1) : K = ⊥ := by
  have hdisj : Disjoint i.range j.range := by
    apply Subgroup.disjoint_def.mpr
    rintro g ⟨s, rfl⟩ ⟨t, ht⟩
    have hs : s ∈ center S := by
      rw [mem_center_iff]
      intro a
      apply hi
      simp only [map_mul]
      rw [← ht]
      exact (hcomm a t).eq
    have hs1 : s = 1 := mem_bot.mp (hcenter ▸ hs)
    rw [hs1, map_one]
  let f := i.noncommCoprod j hcomm
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨hi, hj, hdisj⟩
  have hfs : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective ρ hρ)).2
  apply eq_bot_iff.mpr
  intro k hk
  obtain ⟨⟨s, t⟩, rfl⟩ := hfs k
  have he : f (s, t) = i s * j t := rfl
  have hs : s ∈ center S := by
    rw [mem_center_iff]
    intro a
    have hc : ⁅f (s, t), i a⁆ ∈ K :=
      (commutator_le_left K ⊤)
        (commutator_mem_commutator hk (mem_top _))
    have hec : ⁅f (s, t), i a⁆ = i ⁅s, a⁆ := by
      rw [he, commutatorElement_mul_left_eq_conj_mul,
        (commutatorElement_eq_one_iff_mul_comm).mpr (hcomm a t).symm.eq]
      simp only [mul_one, mul_inv_cancel, one_mul, map_commutatorElement]
    rw [hec] at hc
    exact ((commutatorElement_eq_one_iff_mul_comm).mp (hKS _ hc)).symm
  have hs1 : s = 1 := mem_bot.mp (hcenter ▸ hs)
  have hkt : j t ∈ K := by
    change i s * j t ∈ K at hk
    simpa only [hs1, map_one, one_mul] using hk
  have ht1 := hKT t hkt
  change i s * j t = 1
  rw [hs1, ht1, map_one, map_one, mul_one]

end ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction

namespace ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
open Subgroup LargeLocalSeeds BenderSuzuki.MatrixGroups
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
noncomputable section
variable {m : ℕ}

private def suzukiHom (m : ℕ) : SuzukiMatrixGroup m →* fullLevi m :=
  (seedHom m).comp (SuzukiLeviProjection.fixedLeviEquivSuzuki
    (canonicalLocalBlockInput m)).symm.toMonoidHom

set_option maxHeartbeats 800000 in
/-- The whole fixed Levi acts faithfully on the actual radical abelianization,
given the permitted injective Suzuki-times-units representation. -/
public theorem fullLevi_action_faithful (hm : 1 ≤ m)
    (ρ : fullLevi m →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ) (l : Model m) (hl : l ∈ fullLevi m)
    (ha : ActsTriviallyOnRadicalAbelianization m l) : l = 1 := by
  let e := SuzukiLeviProjection.fixedLeviEquivSuzuki (canonicalLocalBlockInput m)
  let i := suzukiHom m
  let j := complementHom m
  let K := actionKernel m
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  have hi : Function.Injective i := (seedHom_injective m).comp e.symm.injective
  have hj : Function.Injective j := complementHom_injective m
  have hcomm (s : SuzukiMatrixGroup m) (t : (CoefficientField m)ˣ) :
      Commute (i s) (j t) := seed_commutes_complement (e.symm s) t
  have hcenter : center (SuzukiMatrixGroup m) = ⊥ := by
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · apply False.elim
      apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
      apply IsSimpleGroup.comm_iff_isSolvable.mp
      intro x y
      have hx : x ∈ center (SuzukiMatrixGroup m) := by rw [h]; trivial
      exact (mem_center_iff.mp hx y).symm
  have hKS : ∀ s, i s ∈ K → s = 1 := by
    have hn : (K.comap i).Normal := inferInstance
    rcases hn.eq_bot_or_eq_top with h | h
    · intro s hs
      exact mem_bot.mp (h ▸ hs)
    · obtain ⟨s, hs⟩ := exists_seed_mover hm
      have hmemb : i (e s) ∈ K := by
        change e s ∈ K.comap i
        rw [h]
        trivial
      have he : i (e s) = seedHom m s := by
        change seedHom m (e.symm (e s)) = _
        rw [e.symm_apply_apply]
      rw [he] at hmemb
      exact (hs ((mem_actionKernel_iff m _).mp hmemb)).elim
  have hKT : ∀ t, j t ∈ K → t = 1 := by
    intro t ht
    have h := (mem_actionKernel_iff m _).mp ht
    rw [complementHom_val] at h
    exact torus_first_character_eq_one t 1 h
  have hK := normal_eq_bot_of_two_factors i j hi hj hcomm hcenter ρ hρ K hKS hKT
  have hmem : (⟨l, hl⟩ : fullLevi m) ∈ K := (mem_actionKernel_iff m _).mpr ha
  have he := mem_bot.mp (hK ▸ hmem)
  exact congrArg Subtype.val he

/-- The radical centralizer inside the full Suzuki parabolic lies in the radical.
The only additional premise is an injective representation of the actual full Levi. -/
public theorem centralizer_le_radical_of_injective_representation (hm : 1 ≤ m)
    (ρ : fullLevi m →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ) :
    centralizer (intrinsicRadical m .suzuki : Set (parabolic m .suzuki)) ≤
      intrinsicRadical m .suzuki :=
  centralizer_le_radical_of_faithful_fullLevi m (fullLevi_action_faithful hm ρ hρ)

end
end ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
