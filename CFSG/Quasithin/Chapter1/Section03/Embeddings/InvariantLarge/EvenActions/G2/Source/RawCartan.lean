module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.RawCartan.FieldCoordinates
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.RootDiagonal
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source

/-!
# Sylow normalization from the raw G₂ field–Cartan configuration

`Input` retains the prime-subgroup hypotheses of A.3.15 and every clause of its
fifth alternative, with an actual equivalence D ≃ G₂(E). The field subgroup F,
Cartan H and inner-diagonal part I are subgroups of Aut(D), including when they
do not lie in J. The Cartan clauses describe its abelian complement to the
inner image of U = S ∩ D in N_I(U). Products of subgroups are recorded as
products of their underlying sets. Normality of D, used to form the ambient
conjugation map, follows from `OddCartan.AmbientInput.normal` and F*(J) = D.
The finite-field and characteristic-two instances are derived from |E| = 2ⁿ.

The proof first chooses common coefficient coordinates for the cyclic field
subgroup. The verified root-diagonal theorem shows that I, hence H, acts by
inner automorphisms in any such coordinates. An element of B ∩ D is inner,
so the coefficient field factor in its FH decomposition is trivial by the
field-outerness trace test. Its remaining H factor preserves U. Transporting
that equality back to D gives B.subgroupOf D ≤ N_D(U).

No universal inner–field coverage, target normalization, containment B ≤ H,
or assumed inner realization of H enters the input. The later Borel and
Frattini-action arguments remain in the existing Source modules.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5), printed
pp.50–51, and Proposition 1.3.4's G₂ branch on p.511; GLS III, §§2.5.8–2.5.13,
for the root-diagonal and conjugate-field conventions.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source.RawCartan
variable {K E : Type*} [Group K] [Field E]

/-- The split Cartan clauses in the normalizer of U inside I. The last clause
is the actual unipotent–Cartan product, not merely generation by these factors. -/
structure IsCartan (I : Subgroup (MulAut K)) (U : Subgroup K)
    (H : Subgroup (MulAut K)) : Prop where
  inside : H ≤ I
  preserves : ∀ h ∈ H, U.map h.toMonoidHom = U
  abelian : IsMulCommutative H
  disjoint : Disjoint (U.map (MulAut.conj : K →* MulAut K)) H
  factorization : ∀ a ∈ I, U.map a.toMonoidHom = U ↔
    ∃ u ∈ U, ∃ h ∈ H, a = MulAut.conj u * h

variable {J : Type*} [Group J] (D : Subgroup J) [D.Normal]

/-- The full raw configuration of A.3.15(5), specialized to the actual G₂ model.
All three auxiliary factors live in Aut(D). The inner-diagonal part uses the
root-character action definition; no inner realization of H is assumed. -/
structure Input (κ : GroupClass) (e : D ≃* Model E) (S : Sylow 2 J)
    (B : Subgroup J) (p n f : ℕ) (F H I : Subgroup (MulAut D)) : Prop
    extends OddCartan.AmbientInput κ D B S p where
  nonabelian : ∃ x y : D, x * y ≠ y * x
  field_card : Nat.card E = 2 ^ n
  exponent_large : 1 < n
  field_cyclic : IsCyclic F
  field_order : Nat.card F = f
  field_divides : f ∣ n
  field_type : ∀ a ∈ F, IsField e a
  cartan : IsCartan I ((S : Subgroup J).subgroupOf D) H
  invariant : ∀ a ∈ F, H.map (MulAut.conj a).toMonoidHom = H
  contained : ∀ b ∈ B, ∃ a ∈ F, ∃ h ∈ H, MulAut.conjNormal b = a * h
  product : (F : Set (MulAut D)) * (B.map (MulAut.conjNormal (H := D)) : Set (MulAut D)) *
      ((MulAut.conj : D →* MulAut D).range : Set (MulAut D)) =
    (H : Set (MulAut D)) * (B.map (MulAut.conjNormal (H := D)) : Set (MulAut D)) *
      ((MulAut.conj : D →* MulAut D).range : Set (MulAut D))
  inner_diagonal : I =
    (F ⊔ B.map (MulAut.conjNormal (H := D)) ⊔ (MulAut.conj : D →* MulAut D).range) ⊓
      (RootDiagonal.innerDiagonal (E := E)).comap (MulAut.congr e).toMonoidHom

/-- The actual inner-diagonal condition supplies inner containment of the Cartan. -/
theorem cartan_inner {κ : GroupClass} {e : D ≃* Model E} {S : Sylow 2 J}
    {B : Subgroup J} {p n f : ℕ} {F H I : Subgroup (MulAut D)}
    (h : Input D κ e S B p n f F H I) :
    H.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : Model E →* MulAut (Model E)).range := by
  rintro _ ⟨a, ha, rfl⟩
  have hi := h.cartan.inside ha
  rw [h.inner_diagonal] at hi
  have hd := hi.2
  change MulAut.congr e a ∈ RootDiagonal.innerDiagonal at hd
  rwa [RootDiagonal.innerDiagonal_eq_inner] at hd

/-- The raw source factors imply the intrinsic normalization used by the
G₂ Frattini-action assembly. -/
theorem normalizes_sylow [Finite J]
    {κ : GroupClass} {e : D ≃* Model E} {S : Sylow 2 J}
    {B : Subgroup J} {p n f : ℕ} {F H I : Subgroup (MulAut D)}
    (h : Input D κ e S B p n f F H I) :
    B.subgroupOf D ≤ normalizer (((S : Subgroup J).subgroupOf D) : Set D) := by
  let : Finite E := Nat.finite_of_card_ne_zero (by
    rw [h.field_card]
    exact pow_ne_zero _ (by decide))
  let : Fintype E := Fintype.ofFinite E
  have hchar : ringChar E = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, h.field_card]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by have := h.exponent_large; omega)))
  let : CharP E 2 := ringChar.of_eq hchar
  obtain ⟨e', hF⟩ := common_field_coordinates e F h.field_cyclic h.field_type
  have hH := inner_in_any_coordinates e e' H (cartan_inner D h)
  apply normalizes_sylow_of_automorphism_cartan D e' S B
    (F.map (MulAut.congr e').toMonoidHom) (H.map (MulAut.congr e').toMonoidHom)
    ?_ hF hH ?_
  · intro b hb
    obtain ⟨a, ha, c, hc, he⟩ := h.contained b hb
    refine ⟨MulAut.congr e' a, mem_map_of_mem _ ha,
      MulAut.congr e' c, mem_map_of_mem _ hc, ?_⟩
    change MulAut.congr e' (MulAut.conjNormal b) = _
    rw [he, map_mul]
  · rintro _ ⟨a, ha, rfl⟩
    exact map_preserved e' _ a (h.cartan.preserves a ha)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source.RawCartan
