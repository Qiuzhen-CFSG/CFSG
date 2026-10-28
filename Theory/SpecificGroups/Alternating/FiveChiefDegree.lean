module

public import Theory.PGroupCore
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Minimum order of a binary section for a two-perfect A₅ extension

Let J = O²(J) with an actual isomorphism J/O₂(J) ≃ A₅. Every nontrivial
homomorphic image of J has order divisible by five: simplicity forces every
proper normal subgroup into O₂(J), and the first isomorphism theorem then
supplies a surjection from the image onto A₅. Cauchy's theorem gives an
order-five subgroup of any nontrivial automorphism image. Orbit counting for
that subgroup forces every finite two-group it moves to have order at least 16.

Apply this to the literal conjugation action on B/(A ∩ B). No chiefness,
elementary abelianness, or assertion that O₂(J) acts trivially is needed.
In particular the result applies to every noncentral binary chief factor.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 14.7.68(2), printed pp.1071–1072: the chief-factor obstruction in
the A₇ block alternative. The remaining filtration argument is independent.
-/

public section

namespace alternatingGroup.FiveChiefDegree

open Subgroup

private theorem normal_le_of_simple_quotient
    {G : Type*} [Group G] {p : ℕ}
    (Q : Subgroup G) [Q.Normal] [IsSimpleGroup (G ⧸ Q)]
    (hQ : IsPGroup p Q) (hp : IsPPerfect p G)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊤) : N ≤ Q := by
  let q := QuotientGroup.mk' Q
  have hnmap : (N.map q).Normal :=
    (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective Q)
  rcases hnmap.eq_bot_or_eq_top with hz | ht
  · simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
  · exfalso
    apply hN
    apply hp N inferInstance
    let f := (QuotientGroup.mk' N).comp Q.subtype
    apply hQ.of_surjective f
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨n, hn, he⟩ := mem_map.mp (show q x ∈ N.map q by rw [ht]; trivial)
    have hnx : n⁻¹ * x ∈ Q := QuotientGroup.eq.mp he
    refine ⟨⟨n⁻¹ * x, hnx⟩, ?_⟩
    change QuotientGroup.mk' N (n⁻¹ * x) = QuotientGroup.mk' N x
    have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, map_inv, hn', inv_one, one_mul]

/-- Every nontrivial image of the marked two-perfect extension has order divisible by five. -/
theorem five_dvd_card_range {J H : Type*} [Group J] [Finite J] [Group H]
    (hp : IsPPerfect 2 J) (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (f : J →* H) (hf : f ≠ 1) : 5 ∣ Nat.card f.range := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  have hker : f.ker ≠ ⊤ := by
    intro h
    apply hf
    ext x
    exact MonoidHom.mem_ker.mp (h ▸ mem_top x)
  have hle : f.ker ≤ pCore 2 J :=
    normal_le_of_simple_quotient (pCore 2 J) pCore_isPGroup hp f.ker hker
  let q := QuotientGroup.map f.ker (pCore 2 J) (MonoidHom.id J) hle
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective f.ker (pCore 2 J) (MonoidHom.id J)
      (QuotientGroup.mk'_surjective (pCore 2 J)) hle
  have hd : Nat.card (J ⧸ pCore 2 J) ∣ Nat.card f.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact card_dvd_of_surjective q hq
  have hc : Nat.card (J ⧸ pCore 2 J) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hd
  exact dvd_trans (by decide : 5 ∣ 60) hd

/-- A two-group moved by the marked two-perfect extension has at least sixteen elements. -/
theorem sixteen_le_card_of_nontrivial_action
    {J V : Type*} [Group J] [Finite J] [Group V] [Finite V]
    (hp : IsPPerfect 2 J) (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (ρ : J →* MulAut V) (hρ : ρ ≠ 1) (hV : IsPGroup 2 V) :
    16 ≤ Nat.card V := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ρ.range) 5
    (five_dvd_card_range hp e ρ hρ)
  let B := zpowers a
  have hB : Nat.card B = 5 := (Nat.card_zpowers a).trans ha
  have hnot : FixedPoints.subgroup B V ≠ ⊤ := by
    intro htop
    have he : a = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      have hv : v ∈ FixedPoints.subgroup B V := htop ▸ mem_top v
      exact hv ⟨a, mem_zpowers a⟩
    simp [he] at ha
  exact Theory.GroupAction.sixteen_le_card_of_five_action_nontrivial hB hV hnot

open NoncentralChiefRefinement

/-- The bound on the actual relative quotient, with its ambient conjugation action.
This applies in particular to every noncentral two-chief interval. -/
theorem section_card_ge_sixteen
    {J : Type*} [Group J] [Finite J]
    (hp : IsPPerfect 2 J) (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (A B : NormalNode J) (h : IsNoncentralTwo A B) :
    16 ≤ Nat.card (Section A B) := by
  apply sixteen_le_card_of_nontrivial_action hp e (sectionAction A B) _ h.1
  intro he
  apply h.2
  rw [isCentral_iff_action]
  intro j x
  rw [he]
  rfl

end alternatingGroup.FiveChiefDegree
