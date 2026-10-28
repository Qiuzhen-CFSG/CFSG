module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.ProjectiveTori
public import BenderSuzuki.SE.Basic
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Strongly embedded subgroups in the actual unitary covers

A strongly embedded subgroup contains a Sylow two-subgroup and its normalizer.
The doubly transitive projective unitary action makes this normalizer maximal,
so it equals the given proper subgroup. Its solvability comes from the concrete
root and torus calculation.

For SU₃, the central kernel lies in that normalizer. The image subgroup is
therefore proper in PSU₃; projective maximality and the exact inverse-image
formula for Sylow normalizers give the special-unitary result. Solvability
lifts across the central kernel. Both field orders remain fixed throughout.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2(a–c), and the Borel used before
Chapter 2, Lemma 13.2 (`refs/KGroup/GLS4/Chapter2.tex`, Section 13).
-/

noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1

namespace BenderSuzuki.ZD.RankOneModelGeometry

private theorem normalizer_le_of_stronglyEmbedded
    {H : Type*} [Group H] [Finite H] {B : Subgroup H}
    (hB : IsStronglyEmbedded B) (S : Sylow 2 H) (hSB : (S : Subgroup H) ≤ B) :
    normalizer (S : Set H) ≤ B := by
  obtain ⟨x, _, hx⟩ := hB.exists_involution
  have hxorder : orderOf x = 2 ^ 1 := by
    simpa using orderOf_eq_prime hx.sq_eq_one hx.ne_one
  obtain ⟨s, hs⟩ := S.exists_isConj_of_orderOf_eq_prime_pow hxorder
  have hsi : PFAppendixIII.IsInvolution (s : H) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hs
    rw [← hg]
    exact IsInvolution.map_of_injective hx (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  intro g hg
  apply hB.mem_of_involution_mem_rightConjugate (hSB s.property) _ hsi
  have hh := rightConjugateElem_mem_rightConjugate (M := B) (g := g)
    (hSB ((mem_normalizer_iff.mp hg _).mp s.property))
  simpa [rightConjugateElem, mul_assoc] using hh

private theorem solvable_of_central_kernel
    {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hk : f.ker ≤ center H) (B : Subgroup H)
    (hsol : Group.IsSolvable (B.map f)) : Group.IsSolvable B := by
  let g := f.subgroupMap B
  have hc (x : g.ker) : (x.val.val : H) ∈ center H :=
    hk (congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
  let : Group.IsSolvable g.ker := Group.isSolvable_of_comm (fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_center_iff.mp (hc x) y.val.val).symm)
  let : Group.IsSolvable (B.map f) := hsol
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by simp)

open _root_.BenderSuzuki.MatrixGroups
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hcard hfixed hJ in
private theorem projective_overgroup_eq_normalizer
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hB : B ≠ ⊤)
    (hPB : normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ B) :
    B = normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let N := normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  have hN : N ≠ ⊤ := fun he => hB (top_le_iff.mp (he ▸ hPB))
  let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr hN
  have hb := unitary_projective_borel J hn hcard hfixed hJ P
  let : MulAction.IsPreprimitive (ProjectiveSpecialUnitaryMatrixGroup J)
      (ProjectiveSpecialUnitaryMatrixGroup J ⧸ N) :=
    MulAction.isPreprimitive_of_is_two_pretransitive
      (hb.psu_coset_isTwoPretransitive J n hn hcard hfixed hJ)
  have hc : IsCoatom N := by
    rw [← MulAction.stabilizer_quotient N]
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ _
  exact (hc.le_iff_eq hB).mp hPB

include hn hcard hfixed hJ in
/-- Strong embedding identifies a subgroup of the genuine PSU₃ model with
one of its solvable Sylow two-normalizers. -/
public theorem unitary_projective_borel_of_stronglyEmbedded
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : IsStronglyEmbedded B) : IsBorelSubgroup B := by
  obtain ⟨P, hPB⟩ := hB.containsSylowTwo
  have he := projective_overgroup_eq_normalizer J hn hcard hfixed hJ P B hB.ne_top
    (normalizer_le_of_stronglyEmbedded hB P hPB)
  rw [he]
  exact unitary_projective_borel J hn hcard hfixed hJ P

include hn hcard hfixed hJ in
/-- The same recognition in SU₃ retains the full central kernel. -/
public theorem unitary_special_borel_of_stronglyEmbedded
    (B : Subgroup J.specialSubgroup) (hB : IsStronglyEmbedded B) : IsBorelSubgroup B := by
  obtain ⟨P, hPB⟩ := hB.containsSylowTwo
  have hNB := normalizer_le_of_stronglyEmbedded hB P hPB
  let f := J.specialToProjective
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hkB : f.ker ≤ B :=
    J.specialToProjective_ker_le_center.trans ((center_le_normalizer _).trans hNB)
  have hpre : (B.map f).comap f = B := comap_map_eq_self hkB
  have hproper : B.map f ≠ ⊤ := by
    intro ht
    apply hB.ne_top
    rw [← hpre, ht, comap_top]
  have hQB : normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ B.map f := by
    change normalizer (((P : Subgroup J.specialSubgroup).map f) : Set _) ≤ B.map f
    rw [← P.normalizer_map_surjective f J.specialToProjective_surjective]
    exact map_mono hNB
  have he := projective_overgroup_eq_normalizer J hn hcard hfixed hJ Q (B.map f) hproper hQB
  have hsol : Group.IsSolvable (B.map f) := by
    rw [he]
    exact (unitary_projective_borel J hn hcard hfixed hJ Q).1
  refine ⟨solvable_of_central_kernel f J.specialToProjective_ker_le_center B hsol, P, ?_⟩
  rw [← hpre, he]
  exact P.normalizer_comap_of_central_kernel f J.specialToProjective_surjective
    J.specialToProjective_ker_le_center

end BenderSuzuki.ZD.RankOneModelGeometry
