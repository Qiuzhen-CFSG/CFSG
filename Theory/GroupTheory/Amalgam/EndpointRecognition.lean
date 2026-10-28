module

public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Recovering the overlap isomorphism from the endpoints

For two amalgams whose embeddings have Sylow images, an isomorphism of
the left endpoints identifies their Sylow subgroups after conjugation.
Restricting it constructs an isomorphism of the entire middle groups.
Consequently endpoint isomorphisms suffice for parabolic equivalence;
no independently chosen overlap isomorphism is needed.

This is the Sylow-conjugacy step in the distinction between parabolic
equivalence and amalgam equivalence in Aschbacher--Smith F.1.11, p.262.
It applies without a finite ambient completion or a finite graph.
-/

public section
namespace Theory.GroupTheory.RankTwoAmalgam

variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']

/-- Sylow conjugacy supplies the whole middle group from the two endpoints. -/
theorem parabolicEquiv_of_endpoints {p : ℕ} [Fact p.Prime] [Finite L']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (hα : SylowEmbedded p α) (hβ : SylowEmbedded p β)
    (eL : L ≃* L') (eR : R ≃* R') : Nonempty (ParabolicEquiv α β) := by
  obtain ⟨P, hP⟩ := hα.left_sylow
  obtain ⟨Q, hQ⟩ := hβ.left_sylow
  obtain ⟨f, u, _⟩ := exists_normalized_endpoint α.left β.left
    hα.left_injective hβ.left_injective P hP Q hQ eL
  exact ⟨⟨f, u, eR⟩⟩

end Theory.GroupTheory.RankTwoAmalgam
