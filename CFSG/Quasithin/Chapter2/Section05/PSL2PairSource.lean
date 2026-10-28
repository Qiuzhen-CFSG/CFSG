module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.ActionCases
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.MixedFrattini
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.Rank

/-!
# The complete PSL₂ crossing-pair implication of source 2.5.21

From the earlier source bundle, this family constructs centralizer containment,
faithful actions, C_G(t) = KS, the exact two-residual, both Sylow rank witnesses
and internal factor fusion. The action cases exclude factor swapping and every
outer action. In the mixed case, conjugation inside Kˣ aligns its inner action
with the original t before the marked Frattini calculation. The outer fixed
subgroup is constructed from the actual prime-field PGL₂ reflected torus.

`marked_class_eq` identifies tᴳ ∩ M₊ with the involutions in K ∪ Kˣ, and
`marked_fusion` realizes that fusion inside the original M₊. The theorem
`false_of_prime_crossing_pair` applies ShadowPair with all these local inputs
discharged. `false_of_prime_crossing_pair_of_theoremZD` also discharges its
Asc75 Lemma 3.4 premise, leaving exact Theorem ZD as the independent universal
input. Earlier conditional interfaces are retained below.

This completes the pair implication from `Incoming`, not all of Section 2.5.
The section assembly must still construct the crossing identities and
commutation from the earlier paragraphs, finish the quaternion case and the
actual Aut(A₆) conjugation quotient, and discharge the terminal A₆ inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.5.21, printed pp.566–567.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure
namespace CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

omit [Finite G] in
private theorem orderOf_of_conjugate {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (MulAut.conj g).orderOf_eq a

/-- The remaining marked-class exclusion feeds the literal ShadowPair
consumer. Centralizer containment, internal fusion, component structure,
and both actual Sylow-rank witnesses are all discharged here. The premise
`hexclude` isolates the action-case argument of pp.566–567. The final
application below discharges it using the complete action-case family. -/
theorem false_of_class_exclusion (d : Incoming κ G p)
    (hexclude : ∀ a : G, IsConj d.t a →
      a ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) →
      a ∈ (d.K : Set G) ∪ conjugate d.K d.x)
    (asc75 : ∀ (P : Sylow 2 G) (A B : Subgroup G),
      Asc75.Hypotheses P A B → Asc75.Conclusion A B) : False := by
  let : IsSimpleGroup G := d.ambient.simple
  let : Theory.GroupTheory.IsQuasisimple d.K := d.factor_quasisimple
  have hclass : {a : G | IsConj d.t a ∧
      a ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)} =
      {a : G | orderOf a = 2 ∧ a ∈ (d.K : Set G) ∪ conjugate d.K d.x} := by
    ext a
    constructor
    · rintro ⟨hc, hm⟩
      exact ⟨(orderOf_of_conjugate hc).trans d.t_order, hexclude a hc hm⟩
    · rintro ⟨ha, hmem⟩
      obtain ⟨m, hm, he⟩ := d.factor_involution_conjugate ha hmem
      have htM : d.t ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) :=
        (d.K ⊔ conjugate d.K d.x).le_normalizer (mem_sup_right d.mark_mem)
      refine ⟨isConj_iff.mpr ⟨m, he⟩, ?_⟩
      rw [← he]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm htM) (Subgroup.inv_mem _ hm)
  have hfusion : ∀ g : G,
      g * d.t * g⁻¹ ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) →
      ∃ m ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G),
        g * d.t * g⁻¹ = m * d.t * m⁻¹ := by
    intro g hg
    have hc : IsConj d.t (g * d.t * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    obtain ⟨m, hm, he⟩ := d.factor_involution_conjugate
      ((orderOf_of_conjugate hc).trans d.t_order) (hexclude _ hc hg)
    exact ⟨m, hm, he.symm⟩
  exact ShadowPair.false_of_marked_crossing_pair d.T d.K d.x d.t
    d.commuting d.factor_center_eq_bot (d.s_le_t d.t_mem)
    d.centralizer_le_pair_normalizer hfusion hclass d.left_sylow_rank
    d.right_sylow_rank asc75

/-- The diagonal exclusion reduces the remaining marked-class argument to
conjugates outside the actual pair. -/
theorem false_of_no_marked_outside_pair (d : Incoming κ G p)
    (houtside : ∀ a : G, IsConj d.t a →
      a ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) →
      a ∈ d.K ⊔ conjugate d.K d.x)
    (asc75 : ∀ (P : Sylow 2 G) (A B : Subgroup G),
      Asc75.Hypotheses P A B → Asc75.Conclusion A B) : False :=
  d.false_of_class_exclusion
    (fun a ha hm => d.class_exclusion_in_pair ha (houtside a ha hm)) asc75

/-- A precise assembly interface for the remaining action-case analysis.
Once the factor-swapping and outer/outer cases have been excluded and the
mixed case has been put in these actual model coordinates, the new mixed
calculation and diagonal exclusion discharge ShadowPair's marked-class
premise. The complete application below discharges case coverage directly. -/
theorem false_of_pair_or_mixed_models (d : Incoming κ G p)
    (hmodels : ∀ g : G,
      g⁻¹ * d.t * g ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) →
      g⁻¹ * d.t * g ∈ d.K ⊔ conjugate d.K d.x ∨
      ∃ h : G, ∃ n : ℕ, Odd n ∧ n ≠ 1 ∧
        Nonempty ((d.K ⊓ centralizer ({h⁻¹ * d.t * h} : Set G) : Subgroup G) ≃*
          DihedralGroup n) ∧
        ∃ hiL : h⁻¹ * d.t * h ∈ normalizer (conjugate d.K d.x : Set G),
          (conjugate d.K d.x).normalizerMonoidHom ⟨h⁻¹ * d.t * h, hiL⟩ =
            MulAut.conj (⟨d.t, d.mark_mem⟩ : conjugate d.K d.x) ∧
          h⁻¹ * d.t * h ∉ centralizer (d.K : Set G))
    (asc75 : ∀ (P : Sylow 2 G) (A B : Subgroup G),
      Asc75.Hypotheses P A B → Asc75.Conclusion A B) : False := by
  apply d.false_of_no_marked_outside_pair _ asc75
  intro a ha hm
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  have hh := hmodels g⁻¹ (by simpa only [inv_inv] using hm)
  rcases hh with hh | ⟨h, n, hn, hne, ⟨e⟩, hiL, haction, hnc⟩
  · simpa only [inv_inv] using hh
  · exact (d.false_of_mixed_aligned_inner_action h hn hne e hiL haction hnc).elim

/-- The full marked-class equality in the original M₊. -/
theorem marked_class_eq (d : Incoming κ G p) :
    {a : G | IsConj d.t a ∧
      a ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)} =
    {a : G | orderOf a = 2 ∧ a ∈ (d.K : Set G) ∪ conjugate d.K d.x} := by
  ext a
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨?_, d.marked_class_exclusion a hc hm⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    exact ((MulAut.conj g).orderOf_eq d.t).trans d.t_order
  · rintro ⟨ha, hmem⟩
    obtain ⟨m, _, he⟩ := d.factor_involution_conjugate ha hmem
    refine ⟨isConj_iff.mpr ⟨m, he⟩, (d.K ⊔ conjugate d.K d.x).le_normalizer ?_⟩
    exact hmem.elim mem_sup_left mem_sup_right

/-- Every returning conjugate of t is fused with t inside the original M₊. -/
theorem marked_fusion (d : Incoming κ G p) (g : G)
    (hg : g * d.t * g⁻¹ ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)) :
    ∃ m ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G),
      g * d.t * g⁻¹ = m * d.t * m⁻¹ := by
  have hc : IsConj d.t (g * d.t * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨m, hm, he⟩ := d.factor_involution_conjugate
    (((MulAut.conj g).orderOf_eq d.t).trans d.t_order) (d.marked_class_exclusion _ hc hg)
  exact ⟨m, hm, he.symm⟩

/-- The complete PSL₂-pair implication of 2.5.21 from its earlier source
bundle. Every local centralizer, action, marked-class, fusion and Sylow-rank
input of ShadowPair is proved. The only independent universal input is the
genuine Asc75 Lemma 3.4; constructing Incoming from earlier paragraphs and
finishing the other Section 2.5 branches remain with the section assembly. -/
theorem false_of_prime_crossing_pair (d : Incoming κ G p)
    (asc75 : ∀ (P : Sylow 2 G) (A B : Subgroup G),
      Asc75.Hypotheses P A B → Asc75.Conclusion A B) : False := by
  let : IsSimpleGroup G := d.ambient.simple
  let : IsQuasisimple d.K := d.factor_quasisimple
  exact ShadowPair.false_of_marked_crossing_pair d.T d.K d.x d.t
    d.commuting d.factor_center_eq_bot (d.s_le_t d.t_mem)
    d.centralizer_le_pair_normalizer d.marked_fusion d.marked_class_eq
    d.left_sylow_rank d.right_sylow_rank asc75

/-- The source PSL₂ crossing pair is impossible under exact Theorem ZD.
The full proved Asc75 lemma supplies the universal implication needed above;
the section assembly still constructs Incoming from the earlier paragraphs. -/
theorem false_of_prime_crossing_pair_of_theoremZD (d : Incoming κ G p)
    (zd : Asc75.TheoremZD.{u}) : False :=
  d.false_of_prime_crossing_pair (Asc75.lemma_3_4 zd)

end CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming

end
