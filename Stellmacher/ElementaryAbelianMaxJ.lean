module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Automorphism transport for the elementary Thompson subgroup

The family of maximal-order elementary abelian subgroups is preserved by an
ambient group automorphism: containment, elementary-abelianity, and subgroup
cardinality all transport across the induced equivalence. Mapping the defining
supremum therefore carries `elementaryAbelianMaxJ S` to the Thompson subgroup
of the image of `S`.

This is the conjugation-invariance step needed when the consecutively maximal
Sylow intersection in Stellmacher (5.1) is conjugated into the fixed Sylow
subgroup. Source: `refs/latex/stellmacher-n-group.tex`, proof of (5.1), journal
p. 27.
-/

namespace Stellmacher

universe u

variable {G : Type u} [Group G]

private theorem map_symm_map (e : G ≃* G) (A : Subgroup G) :
    (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

private theorem map_map_symm (e : G ≃* G) (A : Subgroup G) :
    (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

private theorem maxFamily_map
    (e : G ≃* G) (S A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    A.map e.toMonoidHom ∈
      elementaryAbelianMaxSubgroups (S.map e.toMonoidHom) := by
  rcases hA with ⟨hAS, hAelem, hAmax⟩
  refine ⟨Subgroup.map_mono hAS, hAelem.map e.toMonoidHom, ?_⟩
  intro B hBS hBelem
  let B' : Subgroup G := B.map e.symm.toMonoidHom
  have hB'S : B' ≤ S := by
    change B.map e.symm.toMonoidHom ≤ S
    apply (Subgroup.map_le_map_iff_of_injective
      (f := e.toMonoidHom) e.injective).mp
    rw [map_map_symm e B]
    exact hBS
  have hB'elem : IsElementaryAbelian 2 B' :=
    hBelem.map e.symm.toMonoidHom
  have hcard := hAmax B' hB'S hB'elem
  have hcardB : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective
      (K := B) (f := e.symm.toMonoidHom) e.symm.injective
  calc
    Nat.card B = Nat.card B' := hcardB.symm
    _ ≤ Nat.card A := hcard
    _ = Nat.card (A.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective
        (K := A) (f := e.toMonoidHom) e.injective).symm

/-- An ambient group automorphism carries the elementary Thompson subgroup to
the elementary Thompson subgroup of the image. -/
public theorem elementaryAbelianMaxJ_map_equiv
    (e : G ≃* G) (S : Subgroup G) :
    elementaryAbelianMaxJ (S.map e.toMonoidHom) =
      (elementaryAbelianMaxJ S).map e.toMonoidHom := by
  unfold elementaryAbelianMaxJ
  apply le_antisymm
  · refine sSup_le ?_
    intro B hB
    let A : Subgroup G := B.map e.symm.toMonoidHom
    have hA : A ∈ elementaryAbelianMaxSubgroups S := by
      have hraw := maxFamily_map e.symm
        (S.map e.toMonoidHom) B hB
      change A ∈ elementaryAbelianMaxSubgroups
        ((S.map e.toMonoidHom).map e.symm.toMonoidHom) at hraw
      rw [map_symm_map e S] at hraw
      exact hraw
    have hAle : A ≤ sSup (elementaryAbelianMaxSubgroups S) := le_sSup hA
    have hmapped := Subgroup.map_mono (f := e.toMonoidHom) hAle
    change (B.map e.symm.toMonoidHom).map e.toMonoidHom ≤
      (sSup (elementaryAbelianMaxSubgroups S)).map e.toMonoidHom at hmapped
    rw [map_map_symm e B] at hmapped
    exact hmapped
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro A hA
    have hmap : A.map e.toMonoidHom ∈
        elementaryAbelianMaxSubgroups (S.map e.toMonoidHom) :=
      maxFamily_map e S A hA
    have hle : A.map e.toMonoidHom ≤
        sSup (elementaryAbelianMaxSubgroups (S.map e.toMonoidHom)) :=
      le_sSup hmap
    exact Subgroup.map_le_iff_le_comap.mp hle

end Stellmacher
