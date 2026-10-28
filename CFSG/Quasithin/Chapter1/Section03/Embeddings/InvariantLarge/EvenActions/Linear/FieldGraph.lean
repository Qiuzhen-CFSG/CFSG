module

public import Theory.SpecificGroups.PSL3.CartanActions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.FieldPowers

/-!
# Field–graph actions on a Cartan subgroup and its Frattini quotient

A finite binary field automorphism acts by one power on the whole torus.
If an actor has a graph contribution, its preservation of B and the inverse
field power prove that the adjusted graph preserves B. Only then do we
restrict the graph and descend it to B/Φ(B). If every actor is a field action,
the identity supplies the involution. An actual group equivalence transports
the construction to the original group and its actual Frattini quotient.

The realization by field or field–graph maps remains an explicit hypothesis.
Source Cartan alignment and the linear kernel of its Borel normalizer must
supply it in the application to A.3.15(5) and Proposition 1.3.4.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.50–51 and p.511.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The same Frobenius power acts on every torus element. -/
theorem field_torus_power (σ : F ≃+* F) :
    ∃ k : ℕ, ∀ x ∈ torus F, fieldAction F σ x = x ^ (2 ^ k) := by
  obtain ⟨k,hk⟩ := binary_field_power σ
  exact ⟨k, field_torus_power_of F σ (2^k) hk⟩

/-- Every subgroup of the torus is stable under field automorphisms. -/
theorem field_preserves_subgroup (σ : F ≃+* F)
    (B : Subgroup PSL(3,F)) (hB : B ≤ torus F) :
    B.map (fieldAction F σ).toMonoidHom = B := by
  obtain ⟨k,hk⟩ := field_torus_power F σ
  obtain ⟨l,hl⟩ := field_torus_power F σ⁻¹
  apply le_antisymm
  · rintro _ ⟨b,hb,rfl⟩
    change fieldAction F σ b ∈ B
    rw [hk b (hB hb)]
    exact B.pow_mem hb _
  · intro b hb
    refine ⟨fieldAction F σ⁻¹ b, ?_, ?_⟩
    · rw [hl b (hB hb)]
      exact B.pow_mem hb _
    · change (fieldAction F σ * fieldAction F σ⁻¹) b = b
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl

private def restrictedGraph (B : Subgroup PSL(3,F))
    (hB : ∀ b ∈ B, oppositionGraph F b ∈ B) : MulAut B where
  toFun b := ⟨oppositionGraph F b, hB b b.property⟩
  invFun b := ⟨oppositionGraph F b, hB b b.property⟩
  left_inv b := Subtype.ext (DFunLike.congr_fun (oppositionGraph_sq F) (b : PSL(3,F)))
  right_inv b := Subtype.ext (DFunLike.congr_fun (oppositionGraph_sq F) (b : PSL(3,F)))
  map_mul' b c := Subtype.ext (map_mul (oppositionGraph F) (b : PSL(3,F)) (c : PSL(3,F)))

omit [Finite F] in
private theorem restrictedGraph_sq (B : Subgroup PSL(3,F))
    (hB : ∀ b ∈ B, oppositionGraph F b ∈ B) : restrictedGraph F B hB ^ 2 = 1 := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  exact DFunLike.congr_fun (oppositionGraph_sq F) (b : PSL(3,F))

/-- A genuine field–graph actor forces graph stability of the subgroup. -/
theorem graph_stable_of_field_graph_actor (B : Subgroup PSL(3,F))
    (hB : B ≤ torus F) (a : MulAut B) (σ : F ≃+* F)
    (ha : ∀ b : B, (a b : PSL(3,F)) = fieldAction F σ (oppositionGraph F b)) :
    ∀ b ∈ B, oppositionGraph F b ∈ B := by
  intro b hb
  have hm : fieldAction F σ⁻¹ (a ⟨b,hb⟩ : PSL(3,F)) ∈ B := by
    exact (field_preserves_subgroup F σ⁻¹ B hB).le
      (mem_map_of_mem _ (a ⟨b,hb⟩).property)
  rw [ha] at hm
  have he : fieldAction F σ⁻¹ (fieldAction F σ (oppositionGraph F b)) = oppositionGraph F b := by
    change (fieldAction F σ⁻¹ * fieldAction F σ) (oppositionGraph F b) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rwa [he] at hm

/-- Construct the Frattini involution from the specified actual torus action. -/
theorem frattini_of_torus_action {A : Type*} [Group A]
    (B : Subgroup PSL(3,F)) (hB : B ≤ torus F) (ρ : A →* MulAut B)
    (hρ : ∀ s : A, ∃ σ : F ≃+* F,
      (∀ b : B, (ρ s b : PSL(3,F)) = fieldAction F σ b) ∨
      (∀ b : B, (ρ s b : PSL(3,F)) = fieldAction F σ (oppositionGraph F b))) :
    ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ (s : A) (v : B ⧸ frattini B),
        quotientAut (frattini B) (ρ s) v ∈ zpowers v ∨
        quotientAut (frattini B) (ρ s) v ∈ zpowers (g v) := by
  classical
  by_cases hgraph : ∃ (s : A) (σ : F ≃+* F),
      ∀ b : B, (ρ s b : PSL(3,F)) = fieldAction F σ (oppositionGraph F b)
  · obtain ⟨t,τ,ht⟩ := hgraph
    have hstable := graph_stable_of_field_graph_actor F B hB (ρ t) τ ht
    let γ := restrictedGraph F B hstable
    let g := quotientAut (frattini B) γ
    refine ⟨g, ?_, ?_⟩
    · change quotientAut (frattini B) γ ^ 2 = 1
      rw [← map_pow, restrictedGraph_sq, map_one]
    · intro s v
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (frattini B) v
      obtain ⟨σ,hs⟩ := hρ s
      obtain ⟨k,hk⟩ := field_torus_power F σ
      rcases hs with hs | hs
      · left
        have he : ρ s b = b ^ (2^k) := Subtype.ext ((hs b).trans (hk b (hB b.property)))
        rw [quotientAut_apply_mk (frattini B) (ρ s) b, he, map_pow]
        exact pow_mem (mem_zpowers _) _
      · right
        have he : ρ s b = γ b ^ (2^k) :=
          Subtype.ext ((hs b).trans (hk _ (hB (hstable b b.property))))
        rw [quotientAut_apply_mk (frattini B) (ρ s) b, he, map_pow]
        change (QuotientGroup.mk' (frattini B) (γ b)) ^ (2^k) ∈
          zpowers (quotientAut (frattini B) γ (QuotientGroup.mk' (frattini B) b))
        rw [quotientAut_apply_mk]
        exact pow_mem (mem_zpowers _) _
  · refine ⟨1, by simp, ?_⟩
    intro s v
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (frattini B) v
    obtain ⟨σ,hs⟩ := hρ s
    rcases hs with hs | hs
    · left
      obtain ⟨k,hk⟩ := field_torus_power F σ
      have he : ρ s b = b ^ (2^k) := Subtype.ext ((hs b).trans (hk b (hB b.property)))
      rw [quotientAut_apply_mk (frattini B) (ρ s) b, he, map_pow]
      exact pow_mem (mem_zpowers _) _
    · exact False.elim (hgraph ⟨s,σ,hs⟩)

/-- Transport the constructed involution through a genuine group equivalence. -/
theorem frattini_of_torus_realization {A V : Type*} [Group A] [Group V]
    (B : Subgroup PSL(3,F)) (hB : B ≤ torus F) (e : V ≃* B)
    (ρ : A →* MulAut V)
    (hρ : ∀ s : A, ∃ σ : F ≃+* F,
      (∀ b : V, (e (ρ s b) : PSL(3,F)) = fieldAction F σ (e b)) ∨
      (∀ b : V, (e (ρ s b) : PSL(3,F)) = fieldAction F σ (oppositionGraph F (e b)))) :
    ∃ g : MulAut (V ⧸ frattini V), g ^ 2 = 1 ∧
      ∀ (s : A) (v : V ⧸ frattini V),
        quotientAut (frattini V) (ρ s) v ∈ zpowers v ∨
        quotientAut (frattini V) (ρ s) v ∈ zpowers (g v) := by
  let ρ' := (MulAut.congr e).toMonoidHom.comp ρ
  have hρ' : ∀ s : A, ∃ σ : F ≃+* F,
      (∀ b : B, (ρ' s b : PSL(3,F)) = fieldAction F σ b) ∨
      (∀ b : B, (ρ' s b : PSL(3,F)) = fieldAction F σ (oppositionGraph F b)) := by
    intro s
    obtain ⟨σ,hs⟩ := hρ s
    refine ⟨σ, ?_⟩
    rcases hs with hs | hs
    · left
      intro b
      simpa [ρ', MulAut.congr_apply] using hs (e.symm b)
    · right
      intro b
      simpa [ρ', MulAut.congr_apply] using hs (e.symm b)
  obtain ⟨g,hg,ha⟩ := frattini_of_torus_action F B hB ρ' hρ'
  have hΦ : (frattini V).map (e : V →* B) = frattini B := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective (φ := (e : V →* B)) e.surjective)
    · intro x hx
      exact ⟨e.symm x, frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hx,
        e.apply_symm_apply x⟩
  let q := QuotientGroup.congr (frattini V) (frattini B) e hΦ
  have hq (s : A) (v : V ⧸ frattini V) :
      q (quotientAut (frattini V) (ρ s) v) = quotientAut (frattini B) (ρ' s) (q v) := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (frattini V) v
    dsimp only [q]
    rw [quotientAut_apply_mk, QuotientGroup.congr_mk', QuotientGroup.congr_mk',
      quotientAut_apply_mk]
    simp [ρ', MulAut.congr_apply]
  refine ⟨MulAut.congr q.symm g, ?_, ?_⟩
  · rw [← map_pow, hg, map_one]
  · intro s v
    rcases ha s (q v) with h | h
    · left
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp h
      exact mem_zpowers_iff.mpr ⟨k, q.injective (by rw [map_zpow, hq]; exact hk)⟩
    · right
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp h
      apply mem_zpowers_iff.mpr
      refine ⟨k,q.injective ?_⟩
      simpa [map_zpow, MulAut.congr_apply, hq] using hk

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
