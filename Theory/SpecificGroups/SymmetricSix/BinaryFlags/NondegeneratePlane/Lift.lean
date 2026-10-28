module

public import Theory.GroupTheory.CoprimeQuotientSubgroups.MarkedPair
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Action

/-!
# Native cubic axes lifted through a two-group kernel

For a finite group mapping onto the actual A₆ inside S₆ with two-group
kernel, the two cubic axes of any nondegenerate binary plane lift together
to commuting order-three subgroups. Their join is elementary of order nine.
Every action conclusion retains the literal image under the original map:
the moving spaces are the prescribed plane and its perpendicular, each
axis fixes the opposite plane, and the actual plane stabilizer normalizes
both image axes.

Source: Aschbacher--Smith, Lemma 13.5.6, printed p.917. This is the subgroup
lift consumed by the original two-A₃ construction; the ambient block
recognition and normality arguments are separate source conclusions.
-/

public section

open Subgroup BinaryPermutation Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
open NaturalGeometry NaturalPairing Representation.BinaryOffender

/-- Lift the two native cubic axes through the original map with two-group
kernel, retaining all moving-space and cross-fixedness identities on its images. -/
theorem exists_lifted_cubic_decomposition
    {H : Type*} [Group H] [Finite H] (f : H →* S)
    (hrange : f.range=alternatingGroup Ω) (hker : IsPGroup 2 f.ker)
    (W : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) W=2)
    (hn : ¬∀ x∈W,∀ y∈W,form x y=0) :
    ∃ P Q : Subgroup H,
      Nat.card P=3 ∧ Nat.card Q=3 ∧ Disjoint P Q ∧
      (∀ a∈P,∀ b∈Q,Commute a b) ∧
      IsElementaryAbelian 3 (P⊔Q : Subgroup H) ∧ Nat.card (P⊔Q : Subgroup H)=9 ∧
      (P⊔Q).map f ≤ flagStabilizer W ∧
      flagStabilizer W ≤ normalizer (P.map f : Set S) ∧
      flagStabilizer W ≤ normalizer (Q.map f : Set S) ∧
      movedSpace (P.map f)=W ∧ movedSpace (Q.map f)=form.orthogonal W ∧
      (∀ a∈P.map f,∀ v∈form.orthogonal W,naturalRepresentation Ω a v=v) ∧
      (∀ b∈Q.map f,∀ v∈W,naturalRepresentation Ω b v=v) := by
  obtain ⟨A,B,hA,hB,hdis,hcomm,hle,heven,hcard,hE,hNA,hNB,hmA,hmB,hfA,hfB⟩ :=
    exists_cubic_decomposition W hd hn
  let _ := hE
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hker.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hr : A⊔B ≤ f.range := by rw [hrange];exact heven
  obtain ⟨P,Q,hP,hQ,hcP,hcQ,hdPQ,hPQ,hEPQ,hcPQ⟩ :=
    exists_elementary_pair_lift f hc A B hr hdis
  refine ⟨P,Q,hcP.trans hA,hcQ.trans hB,hdPQ,hPQ,hEPQ,hcPQ.trans hcard,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · rwa [Subgroup.map_sup,hP,hQ]
  · rwa [hP]
  · rwa [hQ]
  · rwa [hP]
  · rwa [hQ]
  · rwa [hP]
  · rwa [hQ]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
