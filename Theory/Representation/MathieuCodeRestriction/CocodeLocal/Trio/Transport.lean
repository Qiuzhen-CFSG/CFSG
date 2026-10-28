module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Transport.Certificates
public import Theory.Mathieu.M24.LocalGeometry.OctadOrder

/-!
# Native conjugacy of octad trios

Five-transitivity first transports one octad. The thirty checked native
transports fixing the first standard octad then position a disjoint second
octad. The third octad is the complement of the first two, so the same M24
element carries the entire standard partition to the prescribed trio.

Source: Aschbacher, *Sporadic Groups*, Chapter 7, §20; the marking preceding
Aschbacher–Smith H.14.1, printed p.396. The conclusion supplies an element
of the literal Witt-design automorphism group, suitable for transporting
its stabilizer and cocode action.
-/

public section
open scoped Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
namespace MathieuCode.TrioCalculation
noncomputable section

private lemma octad_smul (g : M24) {B : Finset (Fin 24)} (hB : B ∈ m24Blocks) :
    g • B ∈ m24Blocks := by
  have h := (mem_M24_iff g.val).mp g.property
  change g.val • B ∈ (m24Blocks : Set (Finset (Fin 24)))
  rw [← h]
  exact Set.smul_mem_smul_set hB

lemma exists_smul_disjoint_octads {A B : Finset (Fin 24)}
    (hA : A ∈ m24Blocks) (hB : B ∈ m24Blocks) (hd : Disjoint A B) :
    ∃ g : M24, g • standardTrioOctad 0 = A ∧ g • standardTrioOctad 1 = B := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq ⟨_, standardTrioOctad_mem 0⟩ ⟨A,hA⟩
  change g • standardTrioOctad 0 = A at hg
  have hd' : Disjoint (standardTrioOctad 0) (g⁻¹ • B) := by
    rw [← hg] at hd
    exact Finset.disjoint_left.mpr (by
      intro x hx hy
      exact Finset.disjoint_left.mp hd (Finset.smul_mem_smul_finset hx)
        (by simpa using Finset.smul_mem_smul_finset (a := g) hy))
  obtain ⟨h, h0, h1⟩ := TransportData.exists_transport (octad_smul g⁻¹ hB) hd'
  exact ⟨g*h, by rw [mul_smul, h0, hg], by rw [mul_smul, h1, smul_inv_smul]⟩

/-- Every native trio is a translate by an actual element of the native M24. -/
lemma exists_smul_standardTrio (T : Trio) : ∃ g : M24, g • standardTrio.parts = T.parts := by
  obtain ⟨A,B,C,hAB,hAC,hBC,hparts⟩ := Finset.card_eq_three.mp T.card
  have hA : A ∈ T.parts := by simp [hparts]
  have hB : B ∈ T.parts := by simp [hparts]
  have hC : C ∈ T.parts := by simp [hparts]
  obtain ⟨g,hg0,hg1⟩ := exists_smul_disjoint_octads (T.octad A hA) (T.octad B hB)
    (T.disjoint A hA B hB hAB)
  have he : C = Finset.univ \ (A ∪ B) := by
    ext x
    have hcov : x ∈ A ∪ (B ∪ C) := by
      have hh : x ∈ T.parts.biUnion id := by rw [T.cover]; simp
      simpa [hparts] using hh
    have hAC' := Finset.disjoint_left.mp (T.disjoint A hA C hC hAC)
    have hBC' := Finset.disjoint_left.mp (T.disjoint B hB C hC hBC)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
    constructor
    · intro hx; exact ⟨fun ha => hAC' ha hx, fun hb => hBC' hb hx⟩
    · rintro ⟨ha,hb⟩
      simpa [Finset.mem_union, ha, hb] using hcov
  refine ⟨g, ?_⟩
  have hstd : standardTrio.parts =
      {standardTrioOctad 0, standardTrioOctad 1,
        Finset.univ \ (standardTrioOctad 0 ∪ standardTrioOctad 1)} := by decide +kernel
  rw [hstd, hparts, he]
  simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton,
    Finset.smul_finset_sdiff, Finset.smul_finset_union, Finset.smul_finset_univ, hg0, hg1]

end
end MathieuCode.TrioCalculation
