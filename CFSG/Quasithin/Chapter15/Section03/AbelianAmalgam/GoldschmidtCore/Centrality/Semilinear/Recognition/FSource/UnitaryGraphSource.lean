module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.UnitaryGraph
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The marked projective unitary graph row in the literal F.6 consumer

The source residual supplies a Sylow supplement. A proper extension of its
simple projective unitary component produces an actual outside involution
and the required inverse-transpose action on an identity-Gram model. The
row-(11) application retains the original Sylow and both local extension
maps. The catalogue model, its prime congruence, and those local maps belong
to their earlier source producers; no graph action or splitting premise
remains.

Source: Aschbacher–Smith F.6.18(11), printed pp.309–310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G F : Type u} [Group G] [Finite G] [Field F] [Finite F]
  [IsSimpleGroup (generalizedFitting G)]

/-- The proper source component supplies the literal generalized-Fitting graph action. -/
theorem projectiveUnitary_graph_row_of_source
    (hres : pResidual 2 G = generalizedFitting G)
    (hproper : generalizedFitting G ≠ ⊤) (S : Sylow 2 G)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (eK : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nonempty (GraphExtensionRow (D := G)) := by
  have hgen : generalizedFitting G ⊔ (S : Subgroup G) = ⊤ := by
    rw [← hres]
    exact pResidual_sup_sylow_eq_top S
  obtain ⟨t, ht2, htout, htgen, J', j, gl, hconj, hgram, hgl, hj⟩ :=
    exists_projective_unitary_graph_involution S hgen hproper J hp hp8 hcard hc eK
  exact ⟨{ prime := p
           prime_isPrime := hp
           congruence := Or.inl hp8
           automorphism := MulAut.conjNormal t
           model := DegreeThreeGraph.projectiveUnitary F J' hcard
             (by intro x; rw [hconj, hc]) (by omega) hgram j gl hgl hj
           element := t
           involution := ht2
           outside := htout
           generated := htgen
           action := fun _ => rfl }⟩

/-- Literal row (11), with its unitary graph-extension data constructed on
G and all three original local extension maps preserved. -/
theorem eleven_projectiveUnitary_of_source_component
    (hres : pResidual 2 G = generalizedFitting G)
    (hproper : generalizedFitting G ≠ ⊤)
    (hK : IsQuasisimple (generalizedFitting G))
    {G₁ G₂ : Subgroup G} (S : Sylow 2 G)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (eK : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hsylow : Extension S C4Square E4)
    (hleft : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (DihedralGroup 6)) : Alternative G₁ G₂ S := by
  obtain ⟨d⟩ := projectiveUnitary_graph_row_of_source hres hproper S J hp hp8 hcard hc eK
  exact .eleven d hK hsylow hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
