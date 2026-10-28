module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSU3.Obstruction
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.EvenRootPairs
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Ambient generation by distinct PSU₃ root subgroups

For a normal simple PSU₃(2^f) subgroup L and an ambient Sylow two-subgroup T,
the intersection L ∩ T is intrinsically Sylow in L. Every ambient conjugation
restricts to an automorphism of L, so its image is again Sylow. Generation by
distinct Sylow subgroups in the actual projective matrix model, transported
through the `IsPSU` equivalence, gives the required ambient join containing L.

The final application discharges the root-overgroup input of the lower
obstruction. The independent root-center calculations remain with the parent
source assembly; no center or E-member quotient premise is used here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, E.1.1–6
and E.1.14(1), printed pp.209–211, 214; Huppert II.10.12.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSU3
open Subgroup BenderSuzuki.MatrixGroups

private theorem sylow_sup_eq_top_of_isPSU3 {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup H] {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ f))
    (P Q : Sylow 2 H) (hne : P ≠ Q) : (P : Subgroup H) ⊔ Q = ⊤ := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hne' : P' ≠ Q' := by
    intro heq
    apply hne
    apply Sylow.ext
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective
      (congrArg Sylow.toSubgroup heq)
  have ht := HermitianForm.EvenRootPairs.sylow_sup_eq_top J hf hcard hconj P' Q' hne'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.surjective]
  exact ht

variable {G : Type*} [Group G] [Finite G]

/-- Distinct ambient conjugates of the intrinsic PSU₃ root subgroup generate L.
Normality restricts every ambient conjugation to an automorphism of L. -/
theorem rootSection_conjugate_join (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    ∀ g : G, (rootSection L T).map (MulAut.conj g).toMonoidHom ≠ rootSection L T →
      L ≤ rootSection L T ⊔ (rootSection L T).map (MulAut.conj g).toMonoidHom := by
  intro g hne
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal L
  let a : MulAut L := MulAut.conjNormal g
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hS : (P : Subgroup L).map L.subtype = rootSection L T := by
    rw [hP, subgroupOf_map_subtype]
    exact inf_comm _ _
  have hQ : (Q : Subgroup L).map L.subtype =
      (rootSection L T).map (MulAut.conj g).toMonoidHom := by
    change ((P : Subgroup L).map a.toMonoidHom).map L.subtype = _
    rw [← hS, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hPQ : P ≠ Q := by
    intro heq
    apply hne
    rw [← hQ, ← hS, heq]
  have hjoin := sylow_sup_eq_top_of_isPSU3 (by omega : 0 < f) hmodel P Q hPQ
  have himage := congrArg (fun U : Subgroup L => U.map L.subtype) hjoin
  rw [Subgroup.map_sup, hS, hQ, ← MonoidHom.range_eq_map, range_subtype] at himage
  exact himage.ge

/-- The root-pair theorem discharges the overgroup input of the PSU₃
lower-obstruction assembly, for the literal ambient subgroup and its center. -/
theorem root_overgroup_of_isPSU3 (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f))
    (K : Subgroup G) (hSK : rootSection L T ≤ K)
    (hKN : ¬ K ≤ normalizer (rootCenter L T : Set G)) : L ≤ K :=
  root_overgroup_of_conjugate_join L T (rootSection_conjugate_join L T hf hmodel) K hSK hKN

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSU3
