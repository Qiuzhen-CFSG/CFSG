module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel.RankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel.LocalNormality
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel.Conjugation
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# From ternary parabolic placement to the Sylow Borel

A solvable subgroup containing the full upper-unitriangular Sylow and lying
in a point or line parabolic normalizes that Sylow. The parabolic normalizes
its vector- or covector-fixing local factor, whose quotient by O₂ is the
actual SL₂(F). The rank-one proper-overgroup theorem and characteristic
Sylow transport therefore put the subgroup in the Borel.

Sylow conjugacy inside the parabolic handles an arbitrary conjugation
witness. The field-size hypothesis includes F₄. The final theorem has the
exact `ProjectiveInput` contract; only its solvability clause is needed after
parabolic placement and containment of the full Sylow are supplied.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). Construction of the parabolic witness
remains with the parent placement theorem.
-/

public section

open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement
open ParabolicBorel
variable (F : Type*) [Field F] [Finite F]

private theorem solvable_le_borel_of_le_parabolic [CharP F 2]
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (H : Subgroup PSL(3,F)) [Group.IsSolvable H]
    (hUH : unipotent F ≤ H) (point : Bool)
    (hHP : H ≤ RootPlaneGeometry.parabolic F point) : H ≤ borel F := by
  let S := unipotentSylow F (by omega : 0 < f) hF
  have hn : H ≤ normalizer (S : Set PSL(3,F)) := by
    cases point
    · exact solvable_overgroup_normalizes_of_normal_local F hf hF S
        (lineLocal F) H (unipotent_le_lineLocal F) hUH
        (hHP.trans (lineParabolic_le_normalizer_local F))
        (lineLocalCoreQuotientEquiv F)
    · exact solvable_overgroup_normalizes_of_normal_local F hf hF S
        (pointLocal F) H (unipotent_le_pointLocal F) hUH
        (hHP.trans (pointParabolic_le_normalizer_local F))
        (pointLocalCoreQuotientEquiv F)
  change H ≤ normalizer (unipotent F : Set PSL(3,F)) at hn
  rwa [normalizer_unipotent F (by omega) hF] at hn

/-- A solvable overgroup of the full UT₃ Sylow in a conjugate parabolic lies in its Borel. -/
theorem solvable_le_borel_of_conjugate_parabolic
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (H : Subgroup PSL(3,F)) [Group.IsSolvable H]
    (hUH : unipotent F ≤ H)
    (hpar : ∃ (g : PSL(3,F)) (point : Bool),
      H.map (MulAut.conj g).toMonoidHom ≤ RootPlaneGeometry.parabolic F point) :
    H ≤ borel F := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let S := unipotentSylow F (by omega : 0 < f) hF
  obtain ⟨g,point,hg⟩ := hpar
  have hSP : (S : Subgroup PSL(3,F)) ≤ RootPlaneGeometry.parabolic F point := by
    cases point
    · exact (unipotent_le_borel F).trans (map_mono inf_le_right)
    · exact (unipotent_le_borel F).trans (map_mono inf_le_left)
  have hn : H ≤ normalizer (S : Set PSL(3,F)) := by
    apply normalizes_of_conjugate_into S (RootPlaneGeometry.parabolic F point) H hSP hUH
      ?_ g hg
    intro K hKP hSK hsol
    let := hsol
    have hb := solvable_le_borel_of_le_parabolic F hf hF K hSK point hKP
    change K ≤ normalizer (unipotent F : Set PSL(3,F))
    rwa [normalizer_unipotent F (by omega) hF]
  change H ≤ normalizer (unipotent F : Set PSL(3,F)) at hn
  rwa [normalizer_unipotent F (by omega) hF] at hn

/-- The source three-complement lies in the Sylow Borel once the parabolic witness is supplied. -/
theorem le_borel_of_parabolic
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (B : Subgroup PSL(3,F)) (h : ProjectiveInput F B)
    (hpar : ∃ (g : PSL(3,F)) (point : Bool),
      (B ⊔ unipotent F).map (MulAut.conj g).toMonoidHom ≤
        RootPlaneGeometry.parabolic F point) : B ≤ borel F := by
  let := h.solvable
  exact le_sup_left.trans
    (solvable_le_borel_of_conjugate_parabolic F hf hF (B ⊔ unipotent F) le_sup_right hpar)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement
