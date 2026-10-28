module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Action
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.FieldCartan
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.AutomorphismCartan
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.RawCartan

/-!
# The G₂ action from the raw field–Cartan configuration

The raw A.3.15(5) configuration implies that B normalizes S ∩ D: the verified
root-character calculation makes the Cartan action inner, and the cyclic field
subgroup admits common coefficient coordinates. The actual Sylow intersection
can then be aligned with the standard unipotent subgroup, with B simultaneously
placed in the split torus. Inner–field coverage realizes every element of S by
a Borel–field automorphism. The Borel kernel and field power formula show that
each element of N_S(B) acts by one Frobenius power on all of B. This descends
to the asserted power action on the actual B/Φ(B).

`frattini_power_of_raw_cartan` assembles this G₂ action from the full raw input.
Its only additional mathematical premise is universal inner–field coverage,
stated exactly as surjectivity of `semilinearAction`. The field finiteness and
characteristic-two instances follow from |E| = 2^n. The source factors F, H
and I live in Aut(D), as permitted by the source. The earlier adapters for
concretely realized factors, including the specialization inside J, remain
available below.

The raw setup retains SQTK, F*(J) = D nonabelian simple, p > 3,
BS = SB, |E| = 2^n with n > 1, cyclic F of order dividing n, F-invariance of H,
H a Cartan of N_I(S ∩ D), and FBD = HBD. This module proves the action in that
alternative, without asserting the existence of the alternative in A.3.15.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.50–51
(A.3.15(5)) and p.511 (the G₂ branch of Proposition 1.3.4).
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source

private theorem binary_field_conditions {E : Type*} [Field E] {n : ℕ}
    (hcard : Nat.card E = 2 ^ n) (hn : 0 < n) : Finite E ∧ CharP E 2 := by
  let : Finite E := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (by decide))
  let : Fintype E := Fintype.ofFinite E
  refine ⟨inferInstance, ringChar.of_eq ?_⟩
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hcard]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))

section Raw

variable {J E : Type*} [Group J] [Finite J] [Field E]
    (D : Subgroup J) [D.Normal] {κ : GroupClass} {e : D ≃* Model E}
    {S : Sylow 2 J} {B : Subgroup J} {p n f : ℕ}
    {F H I : Subgroup (MulAut D)}

/-- The raw source factors give simultaneous Sylow/torus coordinates in which
the actual ambient Sylow action is realized by Borel–field automorphisms. -/
theorem aligned_borel_field_action_of_raw_cartan
    (h : RawCartan.Input D κ e S B p n f F H I)
    (hcover : Function.Surjective (semilinearAction (F := E))) :
    ∃ e' : D ≃* Model E,
      ((S : Subgroup J).subgroupOf D).map e'.toMonoidHom = unipotent ∧
      (B.subgroupOf D).map e'.toMonoidHom ≤ splitTorus ∧
      ∀ s : S, ∃ (d : Model E) (σ : E ≃+* E), d ∈ borel ∧
        modelAction D e' s = MulAut.conj d * fieldEquiv σ := by
  obtain ⟨hfinite, hchar⟩ := binary_field_conditions h.field_card
    (lt_trans Nat.zero_lt_one h.exponent_large)
  let : Finite E := hfinite
  let : CharP E 2 := hchar
  let : Fact p.Prime := ⟨h.prime⟩
  exact aligned_borel_field_action D e hcover S B h.p_group (by have := h.large; omega)
    (RawCartan.normalizes_sylow D h)

/-- Each element of N_S(B) acts on B by a single Frobenius power, with the
normalization and Borel realization derived from the raw source factors. -/
theorem normalizer_conjugation_power_of_raw_cartan
    (h : RawCartan.Input D κ e S B p n f F H I)
    (hcover : Function.Surjective (semilinearAction (F := E))) :
    ∀ s : ↥((S : Subgroup J) ⊓ normalizer B), ∃ k : ℕ, ∀ b : B,
      (s : J) * (b : J) * (s : J)⁻¹ = (b : J) ^ (2 ^ k) := by
  obtain ⟨hfinite, hchar⟩ := binary_field_conditions h.field_card
    (lt_trans Nat.zero_lt_one h.exponent_large)
  let : Finite E := hfinite
  let : CharP E 2 := hchar
  let : Fact p.Prime := ⟨h.prime⟩
  exact normalizer_conjugation_power D e hcover S B h.inside h.p_group
    (by have := h.large; omega) (RawCartan.normalizes_sylow D h)

/-- The G₂ branch's actual Frattini conjugation action from A.3.15(5).
Universal inner–field coverage is the sole input beyond the raw configuration. -/
theorem frattini_power_of_raw_cartan
    (h : RawCartan.Input D κ e S B p n f F H I)
    (hcover : Function.Surjective (semilinearAction (F := E))) :
    ∀ (s : ↥((S : Subgroup J) ⊓ normalizer B)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  apply frattini_action_pow B ((S : Subgroup J) ⊓ normalizer B) inf_le_right
  intro s
  obtain ⟨k, hk⟩ := normalizer_conjugation_power_of_raw_cartan D h hcover s
  exact ⟨2 ^ k, hk⟩

end Raw

/-- The source-facing reduction with F and H in the automorphism overgroup.
The coefficient and inner realizations remain explicit proof obligations. -/
theorem frattini_power_of_automorphism_cartan
    {J E : Type*} [Group J] [Finite J] [Field E] [Finite E] [CharP E 2]
    (D : Subgroup J) [D.Normal] (e : D ≃* Model E)
    (hcover : Function.Surjective (semilinearAction (F := E)))
    (S : Sylow 2 J) (B : Subgroup J) (hBD : B ≤ D)
    {p : ℕ} [Fact p.Prime] (hB : IsPGroup p B) (hp : p ≠ 2)
    (F H : Subgroup (MulAut (Model E)))
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, modelAction D e b = f * h)
    (hF : F ≤ (fieldAction (F := E)).range)
    (hH : H ≤ (MulAut.conj : Model E →* MulAut (Model E)).range)
    (hHN : ∀ h ∈ H,
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom).map h.toMonoidHom =
        ((S : Subgroup J).subgroupOf D).map e.toMonoidHom) :
    ∀ (s : ↥((S : Subgroup J) ⊓ normalizer B)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v :=
  frattini_power_of_normalizes_sylow D e hcover S B hBD hB hp
    (normalizes_sylow_of_automorphism_cartan D e S B F H hprod hF hH hHN)

/-- The actual Frattini action, conditional on concrete realizations of the
field and Cartan factors inside J. The source-facing form above also permits
these factors to lie outside J. -/
theorem frattini_power_of_field_cartan
    {J E : Type*} [Group J] [Finite J] [Field E] [Finite E] [CharP E 2]
    (D : Subgroup J) [D.Normal] (e : D ≃* Model E)
    (hcover : Function.Surjective (semilinearAction (F := E)))
    (S : Sylow 2 J) (B F H : Subgroup J) (hBD : B ≤ D)
    {p : ℕ} [Fact p.Prime] (hB : IsPGroup p B) (hp : p ≠ 2)
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, b = f * h)
    (hHN : H ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J))
    (hF : ∀ f ∈ F, ∃ σ : E ≃+* E, modelAction D e f = fieldAction σ)
    (hH : ∀ h ∈ H, ∃ d : Model E, modelAction D e h = MulAut.conj d) :
    ∀ (s : ↥((S : Subgroup J) ⊓ normalizer B)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v :=
  frattini_power_of_normalizes_sylow D e hcover S B hBD hB hp
    (normalizes_sylow_of_field_cartan D e S B F H hBD hprod hHN hF hH)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
