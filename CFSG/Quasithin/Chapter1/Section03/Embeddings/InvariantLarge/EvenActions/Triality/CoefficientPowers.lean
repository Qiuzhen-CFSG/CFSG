module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.Coordinates
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.FieldPowers
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Coefficient power actions and central-quotient descent

Every automorphism of the full cubic binary coefficient field is a uniform
Frobenius power. The actual diagonal coordinates of the coroot-generated
torus turn this entrywise action into the same group power. The identity
passes through elementary graph-field fixed points and their own central
quotient, with no assumption that this quotient is injective on the torus.
Every subgroup of the resulting torus is therefore coefficient invariant.
The positive-root subgroup and its finite image are coefficient invariant too.

The coefficient group here includes the order-three contribution termed a
graph automorphism by Aschbacher–Smith, Notation A.2.5, p.33. It is not
identified with the source field subgroup F of A.3.15(5).

Source: GLS3 §§2.5–2.6, `refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith,
combined 1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511.
-/

@[expose] public section

noncomputable section
open Matrix Subgroup
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.OuterOdd
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions
namespace Triality.Standard.CartanAction
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

lemma coefficientSplit_matrix (P : Parameters) (σ : CoefficientAut P) (g : SplitGroup P) :
    (coefficientSplit P σ g).val.val = g.val.val.map σ := rfl

lemma coefficientSplit_torus_power (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) :
    ∃ k : ℕ, ∀ t ∈ splitTorus P, coefficientSplit P σ t = t ^ (2 ^ k) := by
  let := rankOneExtensionCharTwo P hp
  obtain ⟨k, hk⟩ := binary_field_power σ
  refine ⟨k, fun t ht => ?_⟩
  have hd := (mem_splitDiagonal_iff P t).mp (splitTorus_le_diagonal P hp ht)
  apply Subtype.ext
  apply Units.ext
  change (coefficientSplit P σ t).val.val = t.val.val ^ (2 ^ k)
  rw [coefficientSplit_matrix, ← hd.diagonal_diag, Matrix.diagonal_pow]
  ext r s
  by_cases hrs : r = s
  · subst s
    simpa only [Matrix.map_apply, Matrix.diagonal_apply_eq, Pi.pow_apply] using hk _
  · simp only [Matrix.map_apply, Matrix.diagonal_apply_ne _ hrs, map_zero]

private lemma power_descends {G L K : Type*} [Group G] [Group L] [Group K]
    (i : L →* G) (hi : Function.Injective i) (q : L →* K)
    (a : G ≃* G) (b : L ≃* L) (c : K ≃* K)
    (hib : ∀ x, i (b x) = a (i x)) (hqb : ∀ x, q (b x) = c (q x))
    (T : Subgroup G) (m : ℕ) (hpow : ∀ t ∈ T, a t = t ^ m)
    {x : K} (hx : x ∈ (T.comap i).map q) : c x = x ^ m := by
  obtain ⟨x, hx, rfl⟩ := hx
  rw [← hqb, ← map_pow]
  apply congrArg q
  apply hi
  rw [hib, map_pow, hpow _ hx]

lemma coefficient_torus_power (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) :
    ∃ k : ℕ, ∀ t ∈ torus P, coefficientAction P σ t = t ^ (2 ^ k) := by
  obtain ⟨k, hk⟩ := coefficientSplit_torus_power P hp σ
  refine ⟨k, fun t ht => ?_⟩
  exact power_descends (elementaryInclusion P)
    ((fixedSubgroup P).subtype_injective.comp (elementarySubgroup P).subtype_injective)
    (toCarrier P) (coefficientSplit P σ) (coefficientElementary P σ)
    (coefficientAction P σ) (fun _ => rfl) (fun _ => rfl) (splitTorus P) (2 ^ k) hk ht

private lemma invariant_of_power_and_inverse {G : Type*} [Group G]
    (a : G ≃* G) (B : Subgroup G)
    (ha : ∀ b ∈ B, ∃ n : ℕ, a b = b ^ n)
    (hai : ∀ b ∈ B, ∃ n : ℕ, a⁻¹ b = b ^ n) : B.map a.toMonoidHom = B := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨n, hn⟩ := ha c hc
    exact hn.symm ▸ B.pow_mem hc n
  · intro hb
    refine ⟨a⁻¹ b, ?_, a.apply_symm_apply b⟩
    obtain ⟨n, hn⟩ := hai b hb
    exact hn.symm ▸ B.pow_mem hb n

lemma coefficient_preserves_torus_subgroup (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) (B : Subgroup (Carrier P)) (hB : B ≤ torus P) :
    B.map (coefficientAction P σ).toMonoidHom = B := by
  obtain ⟨k, hk⟩ := coefficient_torus_power P hp σ
  obtain ⟨l, hl⟩ := coefficient_torus_power P hp σ⁻¹
  apply invariant_of_power_and_inverse
  · exact fun b hb => ⟨2 ^ k, hk b (hB hb)⟩
  · intro b hb
    refine ⟨2 ^ l, ?_⟩
    rw [← map_inv]
    exact hl b (hB hb)

lemma coefficientSplit_preserves_positive (P : Parameters) (σ : CoefficientAut P) :
    (positiveSubgroup P).map (coefficientSplit P σ).toMonoidHom = positiveSubgroup P := by
  rw [positiveSubgroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨g, ⟨i, t, rfl⟩, rfl⟩
    exact ⟨i, σ t, coefficientSplit_positive P σ _ t⟩
  · rintro ⟨i, t, rfl⟩
    refine ⟨positiveRoot P i (σ.symm t), ⟨i, σ.symm t, rfl⟩, ?_⟩
    change coefficientSplit P σ (positiveRoot P i (σ.symm t)) = positiveRoot P i t
    simp only [positiveRoot, coefficientSplit_positive, σ.apply_symm_apply]

private lemma equiv_mem_iff_of_map_eq {G : Type*} [Group G] (H : Subgroup G)
    (a : G ≃* G) (ha : H.map a.toMonoidHom = H) (x : G) : a x ∈ H ↔ x ∈ H := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := ha.ge hx
    exact a.injective he ▸ hy
  · intro hx
    exact ha.le ⟨x, hx, rfl⟩

private lemma invariant_descends {G L K : Type*} [Group G] [Group L] [Group K]
    (i : L →* G) (q : L →* K)
    (a : G ≃* G) (b : L ≃* L) (c : K ≃* K)
    (hib : ∀ x, i (b x) = a (i x)) (hqb : ∀ x, q (b x) = c (q x))
    (T : Subgroup G) (hT : T.map a.toMonoidHom = T) :
    ((T.comap i).map q).map c.toMonoidHom = (T.comap i).map q := by
  ext x
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨b y, ?_, hqb y⟩
    change i (b y) ∈ T
    rw [hib]
    exact (equiv_mem_iff_of_map_eq T a hT _).mpr hy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨q (b.symm y), ⟨b.symm y, ?_, rfl⟩, ?_⟩
    · change i (b.symm y) ∈ T
      apply (equiv_mem_iff_of_map_eq T a hT _).mp
      rw [← hib, b.apply_symm_apply]
      exact hy
    · change c (q (b.symm y)) = q y
      rw [← hqb, b.apply_symm_apply]

lemma coefficient_preserves_unipotent (P : Parameters) (σ : CoefficientAut P) :
    (unipotent P).map (coefficientAction P σ).toMonoidHom = unipotent P :=
  invariant_descends (elementaryInclusion P) (toCarrier P)
    (coefficientSplit P σ) (coefficientElementary P σ) (coefficientAction P σ)
    (fun _ => rfl) (fun _ => rfl) (positiveSubgroup P)
    (coefficientSplit_preserves_positive P σ)

end Triality.Standard.CartanAction
