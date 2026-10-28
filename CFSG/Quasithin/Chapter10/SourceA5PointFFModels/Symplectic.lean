module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticImage

/-!
# Literal symplectic placement in the point-component FF action

Apply the local-section sieve to the original subgroup L inside the point
component I, through its specified action quotient map. The original A₅
marking is transported through subgroup restriction and the restricted
two-kernel. Both the field-four conclusion and conjugate parabolic placement
refer to that same map. Representation-block identification and movement on
the original abelian module remain separate source steps.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter10
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {G : Type*} [Group G] [Finite G] {L I : Subgroup G}

private def restrictedFiveEquiv (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) ≃* alternatingGroup (Fin 5) := by
  let a := subgroupOfEquivOfLe hLI
  have hk : IsPGroup 2 a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    exact IsPGroup.of_subsingleton 2 _
  exact (a.toMonoidHom.quotientPCoreEquivOfSurjective a.surjective hk).trans e

theorem source_a5_point_symplectic_ff_placement
    (hLI : L ≤ I) (S : Sylow 2 I)
    (hlocal : L.subgroupOf I ∈ localCComponents S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : I →* Sp F) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker)
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : Sp F,
      ((L.subgroupOf I).map f).map (MulAut.conj g).toMonoidHom = pointLocal ∨
      ((L.subgroupOf I).map f).map (MulAut.conj g).toMonoidHom = planeLocal :=
  symplectic_five_section_image hF hn f hf hks S (L.subgroupOf I) hlocal hk
    hproper (restrictedFiveEquiv hLI e)
end
end CFSG.Quasithin.Chapter10
