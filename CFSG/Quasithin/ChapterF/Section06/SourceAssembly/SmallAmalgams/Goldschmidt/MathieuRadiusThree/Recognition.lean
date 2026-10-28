module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.Contracts
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.MathieuTwelve

/-!
# Compatible M₁₂ marking from the two endpoint identifications

The primitive source amalgam already embeds its overlap as a Sylow subgroup
of each endpoint. Sylow conjugacy constructs the missing middle isomorphism
from the first endpoint isomorphism. The proved M₁₂ faithful-twist theorem
then aligns both inclusion maps. Reversing the source orientation transports
the literal intersection, so no compatibility premise is imposed on the
independent local-group calculation.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
the recognition at the end of (6.12), p.406, and (3.8).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup Theory.GroupTheory RankTwoAmalgam
open GreenBook

private theorem swap_primitive {G : Type*} [Group G] {A B : Subgroup G}
    (h : PrimitiveCubic (inclusionAmalgam A B)) :
    PrimitiveCubic (inclusionAmalgam B A) := by
  have hs : SylowEmbedded 2
      (ofSubgroups B (A ⊓ B) A inf_le_right inf_le_left) :=
    ⟨h.sylow.right_injective, h.sylow.left_injective,
      h.sylow.right_sylow, h.sylow.left_sylow⟩
  have hf : Faithful (ofSubgroups B (A ⊓ B) A inf_le_right inf_le_left) :=
    fun N hB hA => h.faithful N hA hB
  have hp : PrimitiveCubic (ofSubgroups B (A ⊓ B) A inf_le_right inf_le_left) :=
    ⟨hs, hf, h.right_index, h.left_index⟩
  have transport (D : Subgroup G) (hD : D = A ⊓ B)
      (h₁ : D ≤ B) (h₂ : D ≤ A) : PrimitiveCubic (ofSubgroups B D A h₁ h₂) := by
    subst D
    exact hp
  exact transport (B ⊓ A) (inf_comm B A) inf_le_left inf_le_right

/-- Endpoint isomorphisms suffice because source Sylow embeddings and
faithfulness allow the existing overlap rigidity to supply both squares. -/
theorem marked_of_endpoint_equivs {G : Type*} [Group G] {A B : Subgroup G}
    (h : PrimitiveCubic (inclusionAmalgam A B))
    (eA : A ≃* MathieuTwelve.P 0) (eB : B ≃* MathieuTwelve.P 1) :
    MathieuTwelve.IsM12Amalgam (inclusionAmalgam A B) := by
  obtain ⟨Pi, hPi⟩ := h.sylow.left_sylow
  obtain ⟨Pj, hPj⟩ := MathieuTwistRigidity.m12_sylow.left_sylow
  obtain ⟨_, eD, _⟩ := exists_normalized_endpoint
    (inclusionAmalgam A B).left MathieuTwelve.amalgam.left
    h.sylow.left_injective MathieuTwistRigidity.m12_sylow.left_injective
    Pi hPi Pj hPj eA
  exact MathieuTwistRigidity.m12_iso h.sylow h.faithful ⟨eA, eD, eB⟩

/-- The two local-group calculations feed the exact marked-base contract,
including either original orientation and both common-overlap maps. -/
theorem marked_of_endpointTypes {G : Type*} [Group G] {F : Bool → Subgroup G}
    {s : ℕ} (h : LargeTreeSource F s) (d : CanonicalLabelSetup F s)
    (e : EndpointTypes d) : MathieuMarkedBase F := by
  obtain ⟨⟨eA⟩, ⟨eB⟩⟩ := e
  have oriented (i : Bool) (eL : F i ≃* MathieuTwelve.P 0)
      (eR : F (!i) ≃* MathieuTwelve.P 1) : MathieuMarkedBase F := by
    cases i
    · exact Or.inl (marked_of_endpoint_equivs h.action.primitive eL eR)
    · exact Or.inr (marked_of_endpoint_equivs (swap_primitive h.action.primitive) eL eR)
  exact oriented d.side eA eB

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
