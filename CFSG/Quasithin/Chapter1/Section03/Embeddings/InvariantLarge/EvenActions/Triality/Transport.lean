module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.BorelReduction
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Transport to the ambient normalizer and its actual Frattini action

A common isomorphism of the normal component places B in the constructed
torus and S ∩ D in the constructed positive subgroup. Conjugation by
N_S(B) then preserves both groups. The Borel/coverage reduction gives a
uniform power identity, which is transported back along that isomorphism
and passed to the actual conjugation action on B/Φ(B).

The Cartan alignment and Borel geometry remain explicit geometric inputs;
this file does not derive them from raw A.3.15(5). The separate coverage
premise is exactly on the genuine BinaryCarrier n hn, with full cubic
coefficient automorphisms. No auxiliary triality model is used.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5),
printed pp.50–51, and the triality branch of Proposition 1.3.4, p.511.
-/

@[expose] public section

noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.OuterOdd
open Triality.Standard.CartanAction
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality

/-- An actual common choice of Sylow and Cartan coordinates. -/
def HasCartanAlignment {J : Type*} [Group J] (D B S : Subgroup J) (P : Parameters) : Prop :=
  ∃ e : D ≃* Carrier P,
    (B.subgroupOf D).map e.toMonoidHom ≤ torus P ∧
    (S.subgroupOf D).map e.toMonoidHom = unipotent P

private lemma conjugation_preserves_subgroupOf {J : Type*} [Group J]
    (D B : Subgroup J) [D.Normal] (s : J) (hs : s ∈ normalizer B) :
    (B.subgroupOf D).map (MulAut.conjNormal (H := D) s).toMonoidHom = B.subgroupOf D := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    change (MulAut.conjNormal s c : J) ∈ B
    rw [MulAut.conjNormal_apply]
    exact (mem_normalizer_iff.mp hs _).mp hc
  · intro hb
    refine ⟨(MulAut.conjNormal s).symm b, ?_, (MulAut.conjNormal s).apply_symm_apply b⟩
    change ((MulAut.conjNormal s).symm b : J) ∈ B
    rw [MulAut.conjNormal_symm_apply]
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (B : Set J)).inv_mem hs) (b : J)).mp
        (show (b : J) ∈ B from hb)

private lemma map_congr_invariant {G M : Type*} [Group G] [Group M]
    (e : G ≃* M) (a : MulAut G) (B : Subgroup G) (h : B.map a.toMonoidHom = B) :
    (B.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = B.map e.toMonoidHom := by
  calc
    _ = (B.map a.toMonoidHom).map e.toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext x
      simp [MulAut.congr]
    _ = _ := by rw [h]

lemma conjugation_power_of_alignment {J : Type*} [Group J]
    (D B S : Subgroup J) [D.Normal] (hBD : B ≤ D)
    (P : Parameters) (n : ℕ) (hn : 0 < n) (hq : P.q = 2 ^ n)
    (hG : BorelGeometry P)
    (hcover : ∀ a : MulAut (BinaryCarrier n hn), ∃ d : BinaryCarrier n hn,
      ∃ σ : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj d * coefficientAction (binaryParameters n hn) σ)
    (hAlign : HasCartanAlignment D B S P) :
    ∀ s : (S ⊓ normalizer B : Subgroup J), ∃ k : ℕ,
      ∀ b : B, (s : J) * (b : J) * (s : J)⁻¹ = (b : J) ^ (2 ^ k) := by
  obtain ⟨e, hBT, hSU⟩ := hAlign
  intro s
  let a : MulAut (Carrier P) := MulAut.congr e (MulAut.conjNormal (H := D) (s : J))
  have haB : ((B.subgroupOf D).map e.toMonoidHom).map a.toMonoidHom =
      (B.subgroupOf D).map e.toMonoidHom :=
    map_congr_invariant e _ _ (conjugation_preserves_subgroupOf D B s s.property.2)
  have haU : (unipotent P).map a.toMonoidHom = unipotent P := by
    rw [← hSU]
    exact map_congr_invariant e _ _
      (conjugation_preserves_subgroupOf D S s (S.le_normalizer s.property.1))
  obtain ⟨k, hk⟩ := normalizer_power_of_binary_coverage P n hn hq hG hcover
    ((B.subgroupOf D).map e.toMonoidHom) hBT a haB haU
  refine ⟨k, fun b => ?_⟩
  let d : D := ⟨b, hBD b.property⟩
  have hd : e d ∈ (B.subgroupOf D).map e.toMonoidHom := ⟨d, b.property, rfl⟩
  have he : MulAut.conjNormal (H := D) (s : J) d = d ^ (2 ^ k) := by
    apply e.injective
    have hx := hk (e d) hd
    simpa only [a, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, map_pow] using hx
  exact congrArg Subtype.val he

lemma frattini_power_of_alignment {J : Type*} [Group J]
    (D B S : Subgroup J) [D.Normal] (hBD : B ≤ D)
    (P : Parameters) (n : ℕ) (hn : 0 < n) (hq : P.q = 2 ^ n)
    (hG : BorelGeometry P)
    (hcover : ∀ a : MulAut (BinaryCarrier n hn), ∃ d : BinaryCarrier n hn,
      ∃ σ : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj d * coefficientAction (binaryParameters n hn) σ)
    (hAlign : HasCartanAlignment D B S P) :
    ∀ (s : (S ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        (S ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  apply frattini_action_pow
  intro s
  obtain ⟨k, hk⟩ := conjugation_power_of_alignment D B S hBD P n hn hq hG hcover hAlign s
  exact ⟨2 ^ k, hk⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality
