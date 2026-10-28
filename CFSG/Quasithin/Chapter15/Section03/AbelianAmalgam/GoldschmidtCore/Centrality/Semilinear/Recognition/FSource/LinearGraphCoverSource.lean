module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.LinearGraphSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.LinearCoverGraph

/-!
# Literal graph row for both special and projective linear components

The original marked central quotient determines its scalar cover. For a
trivial center the proved projective extension theorem applies directly.
Otherwise the graph involution in the centralizer quotient lifts through
its odd kernel, and the marked scalar-cover action theorem identifies
inverse transpose on the original component. The Sylow bound supplies the
source prime congruence. The literal row-(11) consumer keeps its original
local extensions and has no separate splitting or graph-action premise.

Source: Aschbacher--Smith F.6.18(11), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H F : Type u} [Group G] [Finite G] [Group H] [Finite H] [Field F] [Finite F]

/-- The original linear component quotient constructs its actual graph row for either cover. -/
theorem linear_graph_row_of_source_component_quotient
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G) (hproper : generalizedFitting G ≠ ⊤)
    (S : Sylow 2 G) (hS : Nat.card S ≤ 64)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃* PSL(3,F)) :
    Nonempty (GraphExtensionRow (D := G)) := by
  let K := generalizedFitting G
  let : IsQuasisimple K := hK.2
  by_cases hz : center K = ⊥
  · let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let a : K ⧸ center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    let : IsSimpleGroup K := a.symm.isSimpleGroup
    exact projectiveLinear_graph_row_of_source hres hproper S hS hp ho hcard hsign
      (a.symm.trans eK)
  · have hgen : generalizedFitting G ⊔ (S : Subgroup G) = ⊤ := by
      rw [← hres]
      exact pResidual_sup_sylow_eq_top S
    have hm := (component_linear_three_small_sylow_models hK S hS hp hcard hsign eK).1
    obtain ⟨t, ht2, htout, htgen, j, hj⟩ :=
      exists_special_linear_graph_involution eG hK S hgen hproper hz hp ho hcard eK
    exact ⟨{ prime := p
             prime_isPrime := hp
             congruence := Or.inr hm
             automorphism := MulAut.conjNormal t
             model := DegreeThreeGraph.linear F hcard hsign j hj
             element := t
             involution := ht2
             outside := htout
             generated := htgen
             action := fun _ => rfl }⟩

/-- Literal row (11) for every genuine linear scalar cover of the source quotient. -/
theorem eleven_linear_of_source_component_quotient
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G) (hproper : generalizedFitting G ≠ ⊤)
    {G₁ G₂ : Subgroup G} (S : Sylow 2 G)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃* PSL(3,F))
    (hsylow : Extension S C4Square E4)
    (hleft : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (DihedralGroup 6)) : Alternative G₁ G₂ S := by
  have hS : Nat.card S ≤ 64 := by
    obtain ⟨N, hN, ⟨a⟩, ⟨b⟩⟩ := hsylow
    let : N.Normal := hN
    have hNc : Nat.card N = 16 := by
      rw [Nat.card_congr a.toEquiv]
      norm_num [C4Square, C]
    have hNi : N.index = 4 := by
      change Nat.card (S ⧸ N) = 4
      rw [Nat.card_congr b.toEquiv]
      norm_num [E4, C]
    have hc := N.card_mul_index
    rw [hNc, hNi] at hc
    omega
  obtain ⟨d⟩ := linear_graph_row_of_source_component_quotient eG hK hres hproper
    S hS hp ho hcard hsign eK
  exact .eleven d hK.2 hsylow hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
