module

public import Theory.SpecificGroups.SU3.NestedStrongClosure.Normalized

/-!
# Strongly closed subgroups in binary unitary automorphism overgroups

Let K contain all inner automorphisms of the actual PSU₃ group. Any strongly
closed subgroup B of a Sylow two-subgroup of K is inner if every involution
of B is inner. Extend the literal inner root image to a Sylow subgroup of K,
then use Sylow conjugacy within K to transport B to the root-containing case.
Conjugation preserves the full inner range, so the normalized theorem returns
the conclusion for the original subgroup and its original embedding into Aut.

This statement has no rank or commuting-partner premise. The nested-pair
consumer uses the larger factor as B, since it is exactly the given union.
Source: Aschbacher (1975), Lemma 3.4, printed pp.94–96, unitary terminal case;
Huppert II.10.12 and GLS3 Theorem 2.5.12 and Section 2.7.
-/

public section
open Matrix Subgroup BenderSuzuki.External Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
open BorelTorus BorelTorus.SemilinearActors ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Strongly closed subgroups of Sylow two-subgroups of unitary automorphism
overgroups are inner as soon as their square-one elements are inner. -/
theorem stronglyClosed_inner_of_involutions {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ K)
    (T : Sylow 2 K) (B : Subgroup K)
    (hc : IsStronglyClosedSet (B : Set K) T ⊤)
    (hi : ∀ a ∈ B, a^2 = 1 → a.val ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    B.map K.subtype ≤ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Finite.of_injective (fun a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) =>
      (a : ProjectiveSpecialUnitaryMatrixGroup J → ProjectiveSpecialUnitaryMatrixGroup J))
      DFunLike.coe_injective
  let f := innerEmbedding K hK
  let P := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  obtain ⟨S, hS⟩ := (P.isPGroup'.map f).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T S
  let e := MulAut.conj g
  have hmap : (T : Subgroup K).map e.toMonoidHom = S := congrArg Sylow.toSubgroup hg
  have hclosed : IsStronglyClosedSet (B.map e.toMonoidHom : Set K) S ⊤ := by
    have hh := hc.image T e.toMonoidHom e.surjective
    simpa only [← Subgroup.coe_map, hmap] using hh
  let I := MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)
  have hinv : ∀ a ∈ B.map e.toMonoidHom, a^2 = 1 → a.val ∈ I := by
    rintro _ ⟨a, ha, rfl⟩ hs
    have ha2 : a^2 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      exact hs
    have hh := (inferInstance : I.Normal).conj_mem a.val (hi a ha ha2) g.val
    exact hh
  have hout := normalized_inner_of_involutions J hn hJ hcard hfixed K hK
    S (B.map e.toMonoidHom) S.isPGroup' hS hclosed.1 hclosed hinv
  rintro _ ⟨a, ha, rfl⟩
  have he : (e a).val ∈ I := hout (mem_map_of_mem K.subtype (mem_map_of_mem e.toMonoidHom ha))
  have hh := (inferInstance : I.Normal).conj_mem (e a).val he g.val⁻¹
  change g.val⁻¹ * (g.val * a.val * g.val⁻¹) * g.val ∈ I at hh
  have hcancel : g.val⁻¹ * (g.val * a.val * g.val⁻¹) * g.val = a.val := by group
  rw [hcancel] at hh
  exact hh

end BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
