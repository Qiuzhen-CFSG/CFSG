module

public import CFSG.Quasithin.Chapter6.SourceDefs

/-!
# Elementary consequences of the source setup in §6.1

Relative normality, the Sylow condition and elementary abelianness put the
initial module in `T`, and its commutator layer in both `V` and `L`.
The actual equivariant natural-module model gives normalization and order
`2^(2n)`. The weak-closure lemmas expose its generators and the centralizer
duality used in the last paragraph of Proposition 6.1.15.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.663, 669–672. These are elementary supporting lemmas; the local analysis
of 6.1.4–6 and the two branches of 6.1.15 remain separate proof obligations.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter6.Source

open Subgroup

universe u
variable {G : Type u} [Group G]

theorem reduced_normalizes {H V : Subgroup G} (hV : V ∈ reducedFamily H) :
    H ≤ normalizer (V : Set G) :=
  (normal_subgroupOf_iff_le_normalizer hV.1).mp hV.2.2.choose

/-- A reduced module lies in the actual two-core of its local overgroup. -/
theorem reduced_le_core {H V : Subgroup G} (hV : V ∈ reducedFamily H) :
    V ≤ H.pCoreIn 2 := by
  let := hV.2.1
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    hV.1 (reduced_normalizes hV)

theorem reduced_le_reducedSubgroup {H V : Subgroup G}
    (hV : V ∈ reducedFamily H) : V ≤ reducedSubgroup H := le_sSup hV

theorem layer_le_reduced_layer {H L V : Subgroup G}
    (hV : V ∈ reducedFamily H) : layer L V ≤ ⁅reducedSubgroup H, L⁆ :=
  Subgroup.commutator_mono (reduced_le_reducedSubgroup hV) le_rfl

namespace Hypothesis611

variable [Finite G] {K : GroupClass.{u}} {T : Sylow 2 G}
  {L M V : Subgroup G} {n : ℕ} (h : Hypothesis611 K T L M V n)

include h

theorem V_le_T : V ≤ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := h.local_mem.1.prop.2.1
  exact (reduced_le_core h.V_mem).trans ((pCoreIn_le_sylow _ S).trans_eq hS)

theorem layer_le_V : layer L V ≤ V :=
  (le_normalizer_iff_commutator_le_left).mp
    (le_sup_left.trans (reduced_normalizes h.V_mem))

theorem layer_le_L : layer L V ≤ L := by
  have hML : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  exact le_normalizer_iff_commutator_le_right.mp
    ((h.V_le_T.trans h.sylow_le).trans hML)

theorem layer_le_T : layer L V ≤ (T : Subgroup G) :=
  h.layer_le_V.trans h.V_le_T

theorem ZS_le_T : ZS (T : Subgroup G) L V ≤ (T : Subgroup G) :=
  inf_le_left.trans h.layer_le_T

end Hypothesis611

/-- Normalization follows from the actual equivariance equation, not from an
unrelated isomorphism of the underlying groups. -/
theorem IsConjugationModel.normalizes {L V : Subgroup G}
    {A X k : Type*} [Group A] [AddCommGroup X] [Semiring k] [Module k X]
    {ρ : Representation k A X} (h : IsConjugationModel L V ρ) :
    L ≤ normalizer (V : Set G) := by
  obtain ⟨e, f, hf⟩ := h
  apply le_normalizer_iff.mpr
  intro l hl v hv
  rw [← hf ⟨l, hl⟩ ⟨v, hv⟩]
  exact (f.symm _).property

theorem IsConjugationModel.card {L V : Subgroup G}
    {A X k : Type*} [Group A] [AddCommGroup X] [Semiring k] [Module k X]
    {ρ : Representation k A X} (h : IsConjugationModel L V ρ) :
    Nat.card V = Nat.card X := by
  obtain ⟨_, f, _⟩ := h
  exact Nat.card_congr f.toEquiv

/-- The order bound used in the final paragraph of 6.1.27. -/
theorem IsNaturalModule.card {L V : Subgroup G} {n : ℕ}
    (h : IsNaturalModule L V n) : Nat.card V = 2 ^ (n * 2) := by
  obtain ⟨F, _, _, _, hF, hmodel⟩ := h
  rw [hmodel.card, Nat.card_fun, Nat.card_fin, hF, pow_mul]

/-- Every weak closure is contained in the group in which it is formed. -/
theorem W_le (V X : Subgroup G) (i : ℕ) : W V X i ≤ X :=
  sSup_le fun _ h => h.2

/-- In particular `W₀(T,V) ≤ M` whenever `T ≤ M`. Thus the normalizer
in 6.1.27(4) cannot be omitted. -/
theorem W_le_of_le (V : Subgroup G) {X M : Subgroup G}
    (hXM : X ≤ M) (i : ℕ) : W V X i ≤ M := (W_le V X i).trans hXM

/-- At index one the generators are whole conjugates, as required in the
first branch of the proof of 6.1.15. -/
theorem W_zero_le_iff (V X Y : Subgroup G) :
    W V X 0 ≤ Y ↔ ∀ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ X →
      V.map (MulAut.conj g).toMonoidHom ≤ Y := by
  constructor
  · intro h g hg
    have hgen : V.map (MulAut.conj g).toMonoidHom ≤ W V X 0 :=
      le_sSup ⟨⟨g, le_rfl, by simp⟩, hg⟩
    exact hgen.trans h
  · intro h
    apply sSup_le
    rintro A ⟨⟨g, hAg, hi⟩, hAX⟩
    have heq : A = V.map (MulAut.conj g).toMonoidHom :=
      le_antisymm hAg (Subgroup.relIndex_eq_one.mp (by simpa using hi))
    subst A
    exact h g hAX

theorem self_le_W_zero {V X : Subgroup G} (hVX : V ≤ X) : V ≤ W V X 0 := by
  have hconj : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  have h := (W_zero_le_iff V X (W V X 0)).mp le_rfl 1
  simpa only [hconj, Subgroup.map_id] using
    h (by simpa only [hconj, Subgroup.map_id] using hVX)

/-- Centralizer symmetry is the exact bridge used to turn failure of
`Z_S ≤ C₁(T,V)` into failure of `W₁(T,V) ≤ C_T(Z_S)`. -/
theorem le_C_iff {V X Z : Subgroup G} (hZX : Z ≤ X) (i : ℕ) :
    Z ≤ C V X i ↔ W V X i ≤ X ⊓ centralizer (Z : Set G) := by
  constructor
  · intro h
    exact le_inf (W_le V X i) (le_centralizer_iff.mp (h.trans inf_le_right))
  · intro h
    exact le_inf hZX (le_centralizer_iff.mp (h.trans inf_le_right))

end CFSG.Quasithin.Chapter6.Source
