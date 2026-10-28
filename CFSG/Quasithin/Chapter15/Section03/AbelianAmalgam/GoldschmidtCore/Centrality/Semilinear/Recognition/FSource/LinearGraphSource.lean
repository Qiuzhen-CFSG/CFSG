module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DegreeThreeSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.LinearGraph
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The marked projective linear graph row in the literal F.6 consumer

The source residual supplies the Sylow supplement. The proper extension
of a simple PSL₃ component produces an actual outside involution and its
inverse-transpose action on that same component. Its Sylow bound supplies
the modulo-eight condition. The row-(11) application retains the original
three local extension maps. Catalogue selection and the linear Sylow sign
remain separate source inputs; no outer-action or splitting premise remains.

Source: Aschbacher--Smith F.6.18(11), pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G F : Type u} [Group G] [Finite G] [Field F] [Finite F]
  [IsSimpleGroup (generalizedFitting G)]

/-- The proper source extension supplies the original Fstar graph action. -/
theorem projectiveLinear_graph_row_of_source
    (hres : pResidual 2 G = generalizedFitting G) (hproper : generalizedFitting G ≠ ⊤)
    (S : Sylow 2 G) (hS : Nat.card S ≤ 64)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : generalizedFitting G ≃* PSL(3,F)) : Nonempty (GraphExtensionRow (D := G)) := by
  have hgen : generalizedFitting G ⊔ (S : Subgroup G) = ⊤ := by
    rw [← hres]
    exact pResidual_sup_sylow_eq_top S
  let P : Sylow 2 PSL(3,F) := default
  have hP : Nat.card P ≤ 64 := (sylow_card_section_le S (generalizedFitting G)
    eK.toMonoidHom eK.surjective P).trans hS
  have hm : p % 8 = 5 := hcard ▸ Theory.ClassicalSmallSylow.psl3_mod_eight_of_small_sylow
    P hP (hcard ▸ hsign)
  obtain ⟨t, ht2, htout, htgen, j, hj⟩ :=
    exists_projective_linear_graph_involution S hgen hproper hp ho hcard eK
  exact ⟨{ prime := p
           prime_isPrime := hp
           congruence := Or.inr hm
           automorphism := MulAut.conjNormal t
           model := DegreeThreeGraph.projectiveLinear F hcard hsign j hj
           element := t
           involution := ht2
           outside := htout
           generated := htgen
           action := fun _ => rfl }⟩

private theorem card_of_e4_c4Square_extension {S : Type*} [Group S] [Finite S]
    (h : Extension S C4Square E4) : Nat.card S = 64 := by
  obtain ⟨N, hN, hn, hq⟩ := h
  let : N.Normal := hN
  let jN := Classical.choice hn
  let jQ := Classical.choice hq
  have hcN : Nat.card N = 16 := by
    rw [Nat.card_congr jN.toEquiv]
    norm_num [C4Square, C]
  have hcQ : N.index = 4 := by
    change Nat.card (S ⧸ N) = 4
    rw [Nat.card_congr jQ.toEquiv]
    norm_num [E4, C]
  have hh := N.card_mul_index
  rw [hcN, hcQ] at hh
  exact hh.symm

/-- Literal row (11), with all graph-extension data constructed from its
proper simple component and the actual local extension maps. -/
theorem eleven_projectiveLinear_of_source_component
    (hres : pResidual 2 G = generalizedFitting G) (hproper : generalizedFitting G ≠ ⊤)
    (hK : IsQuasisimple (generalizedFitting G))
    {G₁ G₂ : Subgroup G} (S : Sylow 2 G)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : generalizedFitting G ≃* PSL(3,F))
    (hsylow : Extension S C4Square E4)
    (hleft : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (DihedralGroup 6)) : Alternative G₁ G₂ S := by
  have hS : Nat.card S ≤ 64 := (card_of_e4_c4Square_extension hsylow).le
  obtain ⟨d⟩ := projectiveLinear_graph_row_of_source hres hproper S hS hp ho hcard hsign eK
  exact .eleven d hK hsylow hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
