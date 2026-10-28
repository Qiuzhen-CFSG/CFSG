module
public import Theory.Representation.HexacodeAction.CoverComparison
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.Exceptional
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Compatible comparisons of triple covers of A₆

Schur uniqueness compares two central triple covers over any prescribed
A₆ automorphism, with the projection equation retained. Exceptional
involutions are conjugate in Aut(A₆). Adjusting the projection by that
conjugator and using uniqueness of maps from a perfect group to a central
extension therefore intertwines the actual lifted involutions.

The source J₂ normalizer comparison uses this to compare the literal
centralizers and extend the map across their involutory complements.
No group recognition follows merely from orders or abstract family labels.

Sources: GLS, volume 3, Theorem 5.2.3 and Proposition 5.2.7(a);
Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup Theory.GroupTheory GLS3.Chapter5
open AlternatingSix.ShadowLocal
namespace AlternatingSix.TripleCoverComparison
variable {L M : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [Group M] [Finite M] [IsQuasisimple M]

/-- Compare the actual covers over the specified automorphism of their base. -/
theorem equiv_over (f : Covering L A6) (g : Covering M A6)
    (hf : Nat.card f.toMonoidHom.ker = 3) (hg : Nat.card g.toMonoidHom.ker = 3)
    (a : MulAut A6) :
    ∃ e : L ≃* M, ∀ x, g (e x) = a (f x) := by
  let fa : Covering L A6 := (Covering.ofMulEquiv a).comp f
  have hfa : Nat.card fa.toMonoidHom.ker = 3 := by
    have he : fa.toMonoidHom.ker = f.toMonoidHom.ker := by
      ext x
      change a (f x) = 1 ↔ f x = 1
      exact a.map_eq_one_iff
    rw [he, hf]
  obtain ⟨u, hu⟩ := Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate fa hfa
  obtain ⟨v, hv⟩ := Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate g hg
  refine ⟨u.trans v.symm, fun x => ?_⟩
  have h₁ := DFunLike.congr_fun hu x
  have h₂ := DFunLike.congr_fun hv (v.symm (u x))
  change Atlas.Codes.hexEvenCoordinate (v (v.symm (u x))) = g (v.symm (u x)) at h₂
  rw [v.apply_symm_apply] at h₂
  exact h₂.symm.trans h₁

private theorem exceptional_coordinates (b : AutA6) (hb : b ^ 2 = 1)
    (hn : b ∉ natural) : ∃ a : MulAut A6, a ∈ natural ∧
      b = MulAut.congr a canonicalExceptionalAut := by
  obtain ⟨σ, hσ⟩ := exceptionalAut_eq_twist b hn
  obtain ⟨τ, hτ⟩ := exceptionalTwistAut_conjugate_canonical σ (hσ ▸ hb)
  refine ⟨MulAut.conjNormal τ, ⟨τ, rfl⟩, ?_⟩
  rw [hσ, hτ]
  ext x
  rfl

/-- The intertwining comparison can use natural symmetric-group coordinates
on A₆, retaining the projection equation for subsequent local markings. -/
theorem equiv_intertwining_over_natural (f : Covering L A6) (g : Covering M A6)
    (hf : Nat.card f.toMonoidHom.ker = 3) (hg : Nat.card g.toMonoidHom.ker = 3)
    (s : MulAut L) (t : MulAut M) (b c : AutA6)
    (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hbn : b ∉ natural) (hcn : c ∉ natural)
    (hs : ∀ x, f (s x) = b (f x)) (ht : ∀ x, g (t x) = c (g x)) :
    ∃ (k : AutA6) (e : L ≃* M), k ∈ natural ∧
      (∀ x, g (e x) = k (f x)) ∧ (∀ x, e (s x) = t (e x)) := by
  obtain ⟨a, haN, ha⟩ := exceptional_coordinates b hb hbn
  obtain ⟨d, hdN, hd⟩ := exceptional_coordinates c hc hcn
  let k : MulAut A6 := a.symm.trans d
  have hk (x : A6) : k (b x) = c (k x) := by
    rw [ha, hd]
    simp only [k, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  obtain ⟨e, he⟩ := equiv_over f g hf hg k
  have heq : e.toMonoidHom.comp s.toMonoidHom = t.toMonoidHom.comp e.toMonoidHom := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq g.toMonoidHom g.ker_le_center
    apply MonoidHom.ext
    intro x
    change g (e (s x)) = g (t (e x))
    rw [he, hs, hk, ht, he]
  refine ⟨k, e, ?_, he, fun x => DFunLike.congr_fun heq x⟩
  change d * a⁻¹ ∈ natural
  exact natural.mul_mem hdN (natural.inv_mem haN)
/-- Exceptional involution lifts are intertwined by an actual cover isomorphism. -/
theorem equiv_intertwining (f : Covering L A6) (g : Covering M A6)
    (hf : Nat.card f.toMonoidHom.ker = 3) (hg : Nat.card g.toMonoidHom.ker = 3)
    (s : MulAut L) (t : MulAut M) (b c : AutA6)
    (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hbn : b ∉ natural) (hcn : c ∉ natural)
    (hs : ∀ x, f (s x) = b (f x)) (ht : ∀ x, g (t x) = c (g x)) :
    ∃ e : L ≃* M, ∀ x, e (s x) = t (e x) := by
  obtain ⟨_, e, _, _, he⟩ := equiv_intertwining_over_natural f g hf hg s t b c hb hc hbn hcn hs ht
  exact ⟨e, he⟩
end AlternatingSix.TripleCoverComparison
