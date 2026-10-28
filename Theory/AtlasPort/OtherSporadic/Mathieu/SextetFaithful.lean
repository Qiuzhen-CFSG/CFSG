/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24Simplicity

/-!
# Faithful action on unordered sextets

The permutation representation of the Golay automorphism group on
unordered sextets is injective. Simplicity forces its kernel to be trivial
or total; transitivity and the count of 1771 sextets exclude the total case.

Source: `Atlas/Mathieu/SextetFaithful.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def mathieuSextetRepresentation : Mathieu24CodeModel →* Equiv.Perm UnorderedSextet :=
  MulAction.toPermHom _ _

theorem mathieuSextetRepresentation_injective :
    Function.Injective mathieuSextetRepresentation := by
  let : IsSimpleGroup Mathieu24CodeModel := mathieu24_simple
  rcases (inferInstance : mathieuSextetRepresentation.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact (MonoidHom.ker_eq_bot_iff _).mp hb
  · have he (g : Mathieu24CodeModel) : mathieuSextetRepresentation g = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [ht]
      trivial
    have hs (S : UnorderedSextet) : S = distinguishedUnorderedSextet := by
      obtain ⟨g,hg⟩ := sextet_from_distinguished S
      have hh := congrArg (fun p : Equiv.Perm UnorderedSextet => p distinguishedUnorderedSextet) (he g)
      change g • distinguishedUnorderedSextet = distinguishedUnorderedSextet at hh
      exact hg.symm.trans hh
    let : Subsingleton UnorderedSextet := ⟨fun S T => (hs S).trans (hs T).symm⟩
    have hc := Nat.card_of_subsingleton distinguishedUnorderedSextet
    rw [unordered_sextets_card] at hc
    omega

theorem mathieu_eq_one_of_fixes_sextets (g : Mathieu24CodeModel)
    (hg : ∀ S : UnorderedSextet, g • S = S) : g = 1 := by
  apply mathieuSextetRepresentation_injective
  apply Equiv.ext; intro S
  change g • S = (1 : Mathieu24CodeModel) • S
  simpa using hg S

end Atlas.Codes
