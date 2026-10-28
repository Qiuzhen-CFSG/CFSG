module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Alignment
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Ambient

/-!
# Borel–field realization and the ambient Frattini action

For a normal G₂ subgroup D, suppose B ≤ D is an odd-prime subgroup normalizing
S ∩ D, where S is Sylow in the ambient group. Simultaneous Sylow/torus placement
and inner–field coverage then realize every element of S by a Borel–field
automorphism. The already proved Borel kernel gives a uniform Frobenius power
for each element of N_S(B). This identity is transported back to B itself and
then descended through the actual Frattini quotient.

The containment B ≤ N_D(S ∩ D) remains explicit here. FieldCartan supplies it
from concrete field and inner actions of the source factors; the raw source
interpretation of those factors is a separate obligation.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5), printed
pp.50–51, and the G₂ branch of Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {J E : Type*} [Group J] [Finite J] [Field E] [Finite E] [CharP E 2]
variable (D : Subgroup J) [D.Normal] {p : ℕ} [Fact p.Prime]

omit [Finite J] [Finite E] [CharP E 2] in
theorem modelAction_preserves_subgroup (e : D ≃* Model E)
    (Q : Subgroup J) {s : J} (hs : s ∈ normalizer Q) :
    ((Q.subgroupOf D).map e.toMonoidHom).map (modelAction D e s).toMonoidHom =
      (Q.subgroupOf D).map e.toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change modelAction D e s (e x) ∈ _
    rw [modelAction_apply]
    apply mem_map_of_mem
    exact (mem_normalizer_iff.mp hs x).mp hx
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨e (MulAut.conjNormal s⁻¹ x), ?_, ?_⟩
    · apply mem_map_of_mem
      change s⁻¹ * (x : J) * (s⁻¹)⁻¹ ∈ Q
      exact (mem_normalizer_iff.mp ((normalizer (Q : Set J)).inv_mem hs) (x : J)).mp hx
    · change modelAction D e s (e (MulAut.conjNormal s⁻¹ x)) = e x
      rw [modelAction_apply]
      congr 1
      apply Subtype.ext
      change s * (s⁻¹ * (x : J) * (s⁻¹)⁻¹) * s⁻¹ = x
      group

theorem aligned_borel_field_action (e : D ≃* Model E)
    (hcover : Function.Surjective (semilinearAction (F := E)))
    (S : Sylow 2 J) (B : Subgroup J) (hB : IsPGroup p B) (hp : p ≠ 2)
    (hBN : B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D)) :
    ∃ e' : D ≃* Model E,
      ((S : Subgroup J).subgroupOf D).map e'.toMonoidHom = unipotent ∧
      (B.subgroupOf D).map e'.toMonoidHom ≤ splitTorus ∧
      ∀ s : S, ∃ (d : Model E) (σ : E ≃+* E), d ∈ borel ∧
        modelAction D e' s = MulAut.conj d * fieldEquiv σ := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal D
  obtain ⟨e', hS, hT⟩ := sylow_torus_alignment e R (B.subgroupOf D)
    hB.comap_subtype hp (by
      change B.subgroupOf D ≤ normalizer ((R : Subgroup D) : Set D)
      rwa [hR])
  rw [hR] at hS
  refine ⟨e', hS, hT, fun s => ?_⟩
  apply borel_field_of_preserves_unipotent hcover
  rw [← hS]
  exact modelAction_preserves_intersection D e' S s

theorem normalizer_conjugation_power (e : D ≃* Model E)
    (hcover : Function.Surjective (semilinearAction (F := E)))
    (S : Sylow 2 J) (B : Subgroup J) (hBD : B ≤ D)
    (hB : IsPGroup p B) (hp : p ≠ 2)
    (hBN : B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D)) :
    ∀ s : ↥((S : Subgroup J) ⊓ normalizer B), ∃ k : ℕ, ∀ b : B,
      (s : J) * (b : J) * (s : J)⁻¹ = (b : J) ^ (2 ^ k) := by
  obtain ⟨e', hS, hT, ha⟩ := aligned_borel_field_action D e hcover S B hB hp hBN
  intro s
  obtain ⟨d, σ, hd, he⟩ := ha ⟨s, s.property.1⟩
  obtain ⟨k, hk⟩ := borel_field_power _ hT (modelAction D e' s)
    (modelAction_preserves_subgroup D e' B s.property.2) d hd σ he
  refine ⟨k, fun b => ?_⟩
  let bD : D := ⟨b, hBD b.property⟩
  have ht := hk (e' bD) (mem_map_of_mem e'.toMonoidHom
    (show bD ∈ B.subgroupOf D from b.property))
  rw [modelAction_apply, ← map_pow] at ht
  exact congrArg Subtype.val (e'.injective ht)

theorem frattini_power_of_normalizes_sylow (e : D ≃* Model E)
    (hcover : Function.Surjective (semilinearAction (F := E)))
    (S : Sylow 2 J) (B : Subgroup J) (hBD : B ≤ D)
    (hB : IsPGroup p B) (hp : p ≠ 2)
    (hBN : B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D)) :
    ∀ (s : ↥((S : Subgroup J) ⊓ normalizer B)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  apply frattini_action_pow B ((S : Subgroup J) ⊓ normalizer B) inf_le_right
  intro s
  obtain ⟨k, hk⟩ := normalizer_conjugation_power D e hcover S B hBD hB hp hBN s
  exact ⟨2 ^ k, hk⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
