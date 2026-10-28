module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.UnitaryGraphCover
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The full unitary central-cover graph row in the literal F.6 consumer

The original prime-to-three quotient supplies the odd component center.
The centralizer quotient has simple generalized Fitting subgroup, so its
projective graph involution exists by the preceding source theorem. Lifting
that involution and recognizing the component with the new projective
marking gives the literal SU₃ or PSU₃ graph action on the original Fstar.
No simplicity, graph action, splitting, or nontrivial-center assumption is
imposed on the source component. Row (11) retains its three actual local
extension maps.

Source: Aschbacher–Smith F.6.18(11), printed pp.309–310; I.1.1–I.1.4,
printed pp.407–408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H F : Type u} [Group G] [Finite G] [Group H] [Finite H] [Field F] [Finite F]

/-- The original quasisimple component supplies the full special or projective graph row. -/
theorem unitary_cover_graph_row_of_source
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hres : pResidual 2 G = generalizedFitting G)
    (hproper : generalizedFitting G ≠ ⊤)
    (hK : IsQuasisimple (generalizedFitting G)) (S : Sylow 2 G)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (eK : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) : Nonempty (GraphExtensionRow (D := G)) := by
  have hgen : generalizedFitting G ⊔ (S : Subgroup G) = ⊤ := by
    rw [← hres]
    exact pResidual_sup_sylow_eq_top S
  obtain ⟨t, ht2, htout, htgen, J', hconj, hgram, hm⟩ :=
    exists_unitary_cover_graph_involution eG hK S hgen hproper J hp hp8 hcard hc eK
  have hc' : ∀ x, J'.conj x = x ^ p := by intro x; rw [hconj, hc]
  have hsign : p % 4 = 3 := by omega
  have hg : DegreeThreeGraph p (generalizedFitting G) (MulAut.conjNormal t) := by
    rcases hm with hm | hm
    · obtain ⟨j, gl, hgl, hj⟩ := hm
      exact .projectiveUnitary F J' hcard hc' hsign hgram j gl hgl hj
    · obtain ⟨j, hj⟩ := hm
      exact .unitary F J' hcard hc' hsign hgram j hj
  exact ⟨{ prime := p
           prime_isPrime := hp
           congruence := Or.inl hp8
           automorphism := MulAut.conjNormal t
           model := hg
           element := t
           involution := ht2
           outside := htout
           generated := htgen
           action := fun _ => rfl }⟩

/-- Literal row (11), including the nontrivial central unitary cover branch,
with the original ambient group, component, Sylow, and local maps. -/
theorem eleven_unitary_cover_of_source_component
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hres : pResidual 2 G = generalizedFitting G)
    (hproper : generalizedFitting G ≠ ⊤)
    (hK : IsQuasisimple (generalizedFitting G))
    {G₁ G₂ : Subgroup G} (S : Sylow 2 G)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (eK : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J)
    (hsylow : Extension S C4Square E4)
    (hleft : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (DihedralGroup 6)) : Alternative G₁ G₂ S := by
  obtain ⟨d⟩ := unitary_cover_graph_row_of_source eG hres hproper hK S J hp hp8 hcard hc eK
  exact .eleven d hK hsylow hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
