module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.FieldGraph
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.NormalizerForm
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.SourceAlignment
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The linear Cartan action step for invariant Ξ embeddings

From the raw A.3.15(5) configuration, simultaneous Sylow and Cartan alignment
places B in the diagonal torus and S ∩ D in the upper unipotent subgroup.
Actual conjugation by N_S(B) preserves both groups. Standard automorphism
coverage and the linear Borel kernel give a uniform field or field–graph
formula for each actor. The three matrix compatibility identities are supplied
by the concrete standard outer automorphism calculation.

The graph representative includes the Weyl reversal preserving the upper
unipotent subgroup. If a graph-containing actor occurs, the field-power
formula proves graph stability of B before restriction and Frattini descent;
otherwise the identity suffices. Transport gives one involution on the actual
B/Φ(B), with every N_S(B) action in the required two power orbits.

The reusable alignment helper retains explicit standard coverage. The source
specialization derives characteristic two and coverage from |E| = 2^n, n > 1;
it requires no additional alignment, compatibility or coverage premise.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.15(5),
printed pp.50–51, and Proposition 1.3.4, printed p.511.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The actual normalizer action has the required two power orbits once its
Cartan alignment and field–graph formula have been proved. -/
theorem frattini_of_aligned_normalizer {J : Type*} [Group J]
    (B S : Subgroup J) (hSB : S ≤ normalizer B)
    (C : Subgroup PSL(3,F)) (hC : C ≤ torus F) (e : B ≃* C)
    (hact : ∀ s : S, ∃ σ : F ≃+* F,
      (∀ b : B, (e (B.normalizerMonoidHom (inclusion hSB s) b) : PSL(3,F)) =
        fieldAction F σ (e b)) ∨
      (∀ b : B, (e (B.normalizerMonoidHom (inclusion hSB s) b) : PSL(3,F)) =
        fieldAction F σ (oppositionGraph F (e b)))) :
    ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ (s : S) (v : B ⧸ frattini B),
        frattiniConjugationAction S B hSB s v ∈ zpowers v ∨
        frattiniConjugationAction S B hSB s v ∈ zpowers (g v) := by
  let ρ := B.normalizerMonoidHom.comp (inclusion hSB)
  have he : frattiniConjugationAction S B hSB = (quotientAut (frattini B)).comp ρ := by
    apply MonoidHom.ext
    intro s
    apply MulEquiv.ext
    intro v
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (frattini B) v
    rfl
  rw [he]
  exact frattini_of_torus_realization F C hC e ρ hact

section SourceAssembly

private theorem mapped_conjugation_preserves {J M : Type*} [Group J] [Group M]
    (D Q : Subgroup J) [D.Normal] (e : D ≃* M)
    {s : J} (hs : s ∈ normalizer Q) :
    ((Q.subgroupOf D).map e.toMonoidHom).map
        (MulAut.congr e (MulAut.conjNormal s)).toMonoidHom =
      (Q.subgroupOf D).map e.toMonoidHom := by
  have he (x : D) : MulAut.congr e (MulAut.conjNormal s) (e x) =
      e (MulAut.conjNormal s x) := by simp [MulAut.congr_apply]
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change MulAut.congr e (MulAut.conjNormal s) (e x) ∈ _
    rw [he]
    apply mem_map_of_mem
    exact (mem_normalizer_iff.mp hs x).mp hx
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨e (MulAut.conjNormal s⁻¹ x), ?_, ?_⟩
    · apply mem_map_of_mem
      exact (mem_normalizer_iff.mp ((normalizer (Q : Set J)).inv_mem hs) (x : J)).mp hx
    · change MulAut.congr e (MulAut.conjNormal s) (e (MulAut.conjNormal s⁻¹ x)) = e x
      rw [he]
      congr 1
      apply Subtype.ext
      change s * (s⁻¹ * (x : J) * (s⁻¹)⁻¹) * s⁻¹ = x
      group

variable (E : Type*) [Field E] [Finite E] [CharP E 2]

/-- Actual normalizer conjugation has two power orbits after simultaneous
Sylow/Cartan alignment. Standard coverage is the only automorphism input;
the matrix compatibility identities and linear kernel are discharged here. -/
theorem frattini_of_alignment {J : Type*} [Group J]
    (D B S : Subgroup J) [D.Normal] (hBD : B ≤ D)
    (hcover : standard E = ⊤) (e : D ≃* PSL(3,E))
    (hU : (S.subgroupOf D).map e.toMonoidHom = unipotent E)
    (hB : (B.subgroupOf D).map e.toMonoidHom ≤ torus E) :
    ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ (s : (S ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
        frattiniConjugationAction (S ⊓ normalizer B) B inf_le_right s v ∈ zpowers v ∨
        frattiniConjugationAction (S ⊓ normalizer B) B inf_le_right s v ∈ zpowers (g v) := by
  let C := (B.subgroupOf D).map e.toMonoidHom
  let eB : B ≃* C := (subgroupOfEquivOfLe hBD).symm.trans
    ((B.subgroupOf D).equivMapOfInjective e.toMonoidHom e.injective)
  apply frattini_of_aligned_normalizer E B (S ⊓ normalizer B) inf_le_right C hB eB
  intro s
  let a : MulAut PSL(3,E) := MulAut.congr e (MulAut.conjNormal (H := D) (s : J))
  have ha : a ∈ standard E := by rw [hcover]; exact mem_top a
  have haU : (unipotent E).map a.toMonoidHom = unipotent E := by
    rw [← hU]
    exact mapped_conjugation_preserves D S e (S.le_normalizer s.property.1)
  have haB : C.map a.toMonoidHom = C :=
    mapped_conjugation_preserves D B e s.property.2
  obtain ⟨σ, hs⟩ := standard_normalizer_action E
    (field_linearConj (F := E)) (graph_linearConj_exists (F := E))
    (field_commute_graph (F := E))
    C hB a ha haU haB
  have he (b : B) :
      (eB (B.normalizerMonoidHom (inclusion inf_le_right s) b) : PSL(3,E)) = a (eB b) := by
    change e (⟨(s : J) * (b : J) * (s : J)⁻¹, _⟩ : D) =
      MulAut.congr e (MulAut.conjNormal (H := D) (s : J)) (e (⟨b, hBD b.property⟩ : D))
    simp [MulAut.congr_apply]
    rfl
  refine ⟨σ, hs.elim (fun hs => Or.inl ?_) (fun hs => Or.inr ?_)⟩
  · exact fun b => (he b).trans (hs (eB b) (eB b).property)
  · exact fun b => (he b).trans (hs (eB b) (eB b).property)

omit [CharP E 2] in
/-- The A₂ action step of Proposition 1.3.4 from the full raw A.3.15(5)
configuration: one square-one automorphism of the actual Frattini quotient
controls every element of N_S(B). All geometric and coverage premises of
the reusable action helpers are discharged from the source inputs. -/
theorem frattini_of_raw_configuration {J : Type*} [Group J] [Finite J]
    {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p n : ℕ}
    (h : SourceAlignment.AmbientInput κ D B S p)
    (c : SourceAlignment.RawConfiguration E n
      ((S : Subgroup J).subgroupOf D) (B.subgroupOf D)) :
    ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
        frattiniConjugationAction ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈
          zpowers v ∨
        frattiniConjugationAction ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈
          zpowers (g v) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using c.field_card)
  let : D.Normal := by rw [← h.fitting]; infer_instance
  obtain ⟨e, hU, hB⟩ := SourceAlignment.exists_alignment E h c
  exact frattini_of_alignment E D B S h.inside
    (standard_eq_top_of_two_power_card E (by have := c.degree; omega) c.field_card)
    e hU hB

end SourceAssembly

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
