module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.OppositePair

/-!
# Opposite-pair normalization over finite binary fields

The literal upper unitriangular image has odd index and order |F|³, so is a
Sylow two-subgroup. Its inverse-transpose image is another Sylow subgroup and
is disjoint from it. Sylow conjugacy first fixes the upper subgroup; the proved
open-cell calculation then corrects the lower image by an upper unipotent
element. This makes both subgroups invariant under the corrected automorphism.

The matrix open-cell argument imported from OddPrimeCoverage is field-general;
only its old Sylow wrapper required prime cardinality. Here the genuine binary
Sylow subgroup supplies that step. No simplicity or nonsolvability is assumed.

Source: GLS3, §§2.3 and 2.7, as the normalization step toward the generation
assertion of Theorem 2.5.12(a), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3Even.AutomorphismCoverage
variable (F : Type*) [Field F] [Finite F]

private theorem exists_inner_preserves_upper {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (α : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), (upperUnipotent F).map (MulAut.conj g * α).toMonoidHom =
      upperUnipotent F := by
  let U := unipotentSylow F hn hF
  let V := U.mapSurjective (f := α.toMonoidHom) α.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) V U
  refine ⟨g,?_⟩
  have h := congrArg (fun S : Sylow 2 PSL(3,F) => (S : Subgroup PSL(3,F))) hg
  change ((upperUnipotent F).map α.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at h
  rw [Subgroup.map_map] at h
  exact h

/-- An inner correction makes an arbitrary automorphism preserve the literal
upper and lower unitriangular subgroups over a finite binary field. -/
theorem exists_inner_preserves_pair {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (α : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), PreservesUnipotentPair F (MulAut.conj g * α) := by
  obtain ⟨a,ha⟩ := exists_inner_preserves_upper F hn hF α
  let β : MulAut PSL(3,F) := MulAut.conj a * α
  have hd : Disjoint (upperUnipotent F) ((lowerUnipotent F).map β.toMonoidHom) := by
    have h := Subgroup.disjoint_map (f := β.toMonoidHom) β.injective
      (OppositePair.disjoint_upper_lower F)
    change Disjoint ((upperUnipotent F).map (MulAut.conj a * α).toMonoidHom) _ at h
    rwa [ha] at h
  let U := unipotentSylow F hn hF
  let L := U.mapSurjective (f := (graph F).toMonoidHom) (graph F).surjective
  let V := L.mapSurjective (f := β.toMonoidHom) β.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) U V
  have hs : (upperUnipotent F).map (MulAut.conj g).toMonoidHom =
      (lowerUnipotent F).map β.toMonoidHom :=
    congrArg (fun S : Sylow 2 PSL(3,F) => (S : Subgroup PSL(3,F))) hg
  obtain ⟨b,hb,hbl⟩ := OppositePair.exists_unipotent_conjugator F g (hs.symm ▸ hd)
  rw [hs] at hbl
  have hbu : (upperUnipotent F).map (MulAut.conj b).toMonoidHom = upperUnipotent F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((upperUnipotent F).le_normalizer hb)
  have he (H : Subgroup PSL(3,F)) :
      H.map (MulAut.conj (b*a) * α).toMonoidHom =
        (H.map β.toMonoidHom).map (MulAut.conj b).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [β, MulAut.conj_apply, mul_assoc]
  refine ⟨b*a,?_,?_⟩
  · rw [he]
    change ((upperUnipotent F).map (MulAut.conj a * α).toMonoidHom).map _ = _
    rw [ha,hbu]
  · rw [he]
    exact hbl

end Matrix.PSL3Even.AutomorphismCoverage
