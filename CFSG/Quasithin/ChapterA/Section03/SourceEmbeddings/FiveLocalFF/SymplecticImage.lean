module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic

/-!
# The literal symplectic image of a local A₅ section

A solvable global kernel transports the local C-component condition at the
image of the original full Sylow. A two-group restricted kernel preserves
the A₅ two-core quotient and its given marking elementwise. The intrinsic
symplectic placement theorem then supplies field order four and the actual
conjugate point or plane residual. No faithfulness of the original actor on
its abelian module is asserted.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

def imageFiveEquiv (f : G →* Sp F) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ((L.map f) ⧸ pCore 2 (L.map f)) ≃* alternatingGroup (Fin 5) :=
  ((f.subgroupMap L).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective L) hk).symm.trans e

omit [CharP F 2] in
theorem imageFiveEquiv_apply (f : G →* Sp F) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (l : L) :
    imageFiveEquiv f L hk e
      (QuotientGroup.mk' (pCore 2 (L.map f)) (f.subgroupMap L l)) =
        e (QuotientGroup.mk' (pCore 2 L) l) := by
  change e (((f.subgroupMap L).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective L) hk).symm
    (QuotientGroup.mk' (pCore 2 (L.map f)) (f.subgroupMap L l))) = _
  rw [← MonoidHom.quotientPCoreEquivOfSurjective_mk
    (f.subgroupMap L) (f.subgroupMap_surjective L) hk l, MulEquiv.symm_apply_apply]

theorem symplectic_five_section_image {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : G →* Sp F) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (hproper : L.map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : Sp F,
      (L.map f).map (MulAut.conj g).toMonoidHom = pointLocal ∨
      (L.map f).map (MulAut.conj g).toMonoidHom = planeLocal := by
  let := hks
  exact symplectic_five_section_placement hF hn
    (S.mapSurjective hf) (L.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hL f)
    hproper (imageFiveEquiv f L hk e)
end
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
