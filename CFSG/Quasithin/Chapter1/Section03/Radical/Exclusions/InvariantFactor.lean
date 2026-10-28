module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockContract
public import Mathlib.GroupTheory.IndexNormal

/-!
# The final invariant-factor obstruction in the radical argument

A two-perfect group cannot move a point in an orbit of size at most two:
its stabilizer has index one or two, and the latter would give a nontrivial
two-group quotient. Applied to a factor pair, this gives normalization by L.
The actual N_L(P)-action then forces the trace on P either into Φ(P) or to
be all of P. This proves the final contradiction once the block argument
has constructed the pair and checked its trace.

No Krull–Schmidt or decomposition assertion is assumed to hold universally
here. Those are separate proof obligations for the binary-block configuration.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.514, final paragraph.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions

private theorem stabilizer_eq_top_of_twoPerfect_pair
    {D Ω : Type*} [Group D] [Finite D] [MulAction D Ω]
    (hD : IsPPerfect 2 D) (a b : Ω) (hpair : ∀ d : D, d • a = a ∨ d • a = b) :
    MulAction.stabilizer D a = ⊤ := by
  have horbit : MulAction.orbit D a ⊆ ({a, b} : Set Ω) := by
    rintro y ⟨d, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair d
  have hindex : (MulAction.stabilizer D a).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard horbit).trans (by simpa using Set.ncard_insert_le a {b})
  have hpos := (MulAction.stabilizer D a).index_ne_zero_of_finite
  have hc : (MulAction.stabilizer D a).index = 1 ∨
      (MulAction.stabilizer D a).index = 2 := by omega
  rcases hc with hc | hc
  · exact index_eq_one.mp hc
  · let _ := (MulAction.stabilizer D a).normal_of_index_eq_two hc
    apply hD _ inferInstance
    apply IsPGroup.of_card (n := 1)
    simpa only [← index_eq_card, pow_one] using hc

/-- A two-perfect subgroup fixes each of a pair of subgroups it permutes. -/
theorem normalizes_of_twoPerfect_pair {G : Type*} [Group G] [Finite G]
    (D A B : Subgroup G) (hD : IsPPerfect 2 D)
    (hpair : ∀ d ∈ D, A.conjBy d = A ∨ A.conjBy d = B) :
    D ≤ normalizer A := by
  let _ : MulAction D (Subgroup G) := {
    smul := fun d C => C.conjBy d
    one_smul := fun C => conjBy_one C
    mul_smul := fun d e C => conjBy_mul C d e }
  have hs : MulAction.stabilizer D A = ⊤ :=
    stabilizer_eq_top_of_twoPerfect_pair hD A B (fun d => hpair d d.property)
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (show (⟨d, hd⟩ : D) ∈ MulAction.stabilizer D A by rw [hs]; trivial)

variable {G : Type*} [Group G]

/-- The maximal local component is two-perfect because it is perfect. -/
theorem Configuration.local_twoPerfect [Finite G] {p : ℕ} {T X P L₀ M : Subgroup G}
    (h : Configuration p T X P L₀ M) : IsPPerfect 2 L₀ := by
  let _ := mem_L_isPerfect h.maximal_local.1
  intro N hN hp
  let _ := hN
  have hs : Subsingleton (L₀ ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (L₀ ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The actual Frattini action preserves the image of an invariant subgroup. -/
theorem frattini_image_invariant {P S A : Subgroup G}
    (hSP : S ≤ normalizer P) (hSA : S ≤ normalizer A)
    (s : S) (a : P ⧸ frattini P)
    (ha : a ∈ (A.subgroupOf P).map (QuotientGroup.mk' (frattini P))) :
    frattiniConjugationAction S P hSP s a ∈
      (A.subgroupOf P).map (QuotientGroup.mk' (frattini P)) := by
  obtain ⟨b, hb, rfl⟩ := ha
  let _ := conjMulDistribMulActionOfLeNormalizer S P hSP
  refine mem_map.mpr ⟨s • b, ?_, ?_⟩
  · change ((s • b : P) : G) ∈ A
    change (s : G) * (b : G) * (s : G)⁻¹ ∈ A
    exact (mem_normalizer_iff.mp (hSA s.property) b).mp hb
  · simp only [frattiniConjugationAction, MonoidHom.comp_apply, quotientAut_apply_mk,
      MulDistribMulAction.toMulAut_apply]
    rfl

/-- An L-invariant subgroup either contains P or has only Frattini intersection
with P. This uses the specified N_L(P)-action, not the N_T(P)-action. -/
theorem Configuration.invariant_subgroup_dichotomy [Finite G] {p : ℕ}
    {T X P L₀ M : Subgroup G} (h : Configuration p T X P L₀ M)
    (A : Subgroup G) (hLA : L₀ ≤ normalizer A) :
    P ⊓ A ≤ (frattini P).map P.subtype ∨ P ≤ A := by
  let q := QuotientGroup.mk' (frattini P)
  rcases h.irreducible ((A.subgroupOf P).map q)
    (frattini_image_invariant inf_le_right (inf_le_left.trans hLA)) with hz | ht
  · left
    have hk : A.subgroupOf P ≤ frattini P := by
      simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
    intro g hg
    exact mem_map.mpr ⟨⟨g, hg.1⟩, hk hg.2, rfl⟩
  · right
    apply subgroupOf_eq_top.mp
    apply frattini_nongenerating
    have he := congrArg (comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he

/-- The last irreducibility contradiction, once the factor pair is constructed.
The trace hypotheses still have to be proved from the binary block model. -/
theorem Configuration.no_invariant_factor_pair [Finite G] {p : ℕ}
    {T X P L₀ M : Subgroup G} (h : Configuration p T X P L₀ M)
    (A B : Subgroup G)
    (hpair : ∀ d ∈ L₀, A.conjBy d = A ∨ A.conjBy d = B)
    (hproper : ¬ P ≤ A) (htrace : ¬ P ⊓ A ≤ (frattini P).map P.subtype) : False := by
  have hn := normalizes_of_twoPerfect_pair L₀ A B h.local_twoPerfect hpair
  exact (h.invariant_subgroup_dichotomy A hn).elim htrace hproper

end CFSG.Quasithin.Chapter1.RadicalExclusions
