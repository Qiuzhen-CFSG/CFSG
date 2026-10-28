module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeModel
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
public import Theory.GroupTheory.PerfectNormalTwoResidualProduct
public import Theory.GroupTheory.PResidual.SylowIndexThree
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The actual component product in F.6.17(2)

For the normal component selected by the source reduction, the opposite local
residual supplements it in O²(G). Prime-field covering and automorphism
calculations make the component centerless with two-group outer quotient.
The literal centralizer intersection therefore splits off and has order three,
by the opposite vertex's symmetric-three quotient and O₂(G)=1.

The resulting equivalence is multiplication in the original ambient group;
no product recognition or chosen-factor premise is introduced.
Source: Aschbacher--Smith F.6.17(2), printed p.309, with the SQTK prime-field
refinement from F.6.18, printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable {G₁ G₂ : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The selected component and the literal centralizer intersection give
F.6.17's product and cubic factor on the original ambient carrier. -/
theorem SingleResidualComponent.prime_product
    (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hp : Odd p) (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p) :
    let D := pResidual 2 G ⊓ centralizer (d.component : Set G)
    D.Normal ∧ Nat.card D = 3 ∧ d.component ⊔ D = pResidual 2 G ∧
      Disjoint d.component D ∧
      ∃ f : d.component × D ≃* pResidual 2 G,
        ∀ k a, (f (k,a) : G) = (k : G) * (a : G) := by
  let K := d.component
  let : K.Normal := d.normal
  let : IsQuasisimple K := d.isComponent.2
  obtain ⟨hz, ho, _⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  obtain ⟨hsup, hd, f, hf⟩ := exists_twoResidual_product K hz ho
  let D := pResidual 2 G ⊓ centralizer (K : Set G)
  have hKL : K ≤ pResidual 2 G := (le_sup_left : K ≤ K ⊔ D).trans hsup.le
  let A := (pResidual 2 G₂).map G₂.subtype
  have hgen : K ⊔ A = pResidual 2 G := by
    apply le_antisymm (sup_le hKL (map_pResidual_le 2 G₂.subtype))
    rw [h.twoResidual_eq_sup]
    exact sup_le (d.left_contains.trans le_sup_left) le_sup_right
  let j : pResidual 2 G₂ ≃* A :=
    (pResidual 2 G₂).equivMapOfInjective G₂.subtype G₂.subtype_injective
  let jq : (pResidual 2 G₂ ⧸ pCore 2 (pResidual 2 G₂)) ≃* (A ⧸ pCore 2 A) :=
    QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  have hthree : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [← Nat.card_congr jq.toEquiv]
    exact residual_core_quotient_card_of_sylow_index_three (default : Sylow 2 G₂)
      (SymmetricThreeTwoCore.sylow_index_three h.quotient_right.some _)
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e))
  exact ⟨inferInstance,
    twoResidual_centralizer_card_three K A hz ho hcore hgen d.right_escapes hthree,
    hsup, hd, f, hf⟩

/-- In particular the residual has the required actual prime PSL₂ and cubic models. -/
theorem SingleResidualComponent.prime_product_model
    (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hp : Odd p) (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p) :
    Nonempty (pResidual 2 G ≃* (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) ×
      Multiplicative (ZMod 3))) := by
  obtain ⟨_, _, ⟨k⟩⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  obtain ⟨_, hcard, _, _, f, _⟩ := d.prime_product e h hp hm
  let a := mulEquivOfPrimeCardEq hcard (by simp : Nat.card (Multiplicative (ZMod 3)) = 3)
  exact ⟨f.symm.trans (k.prodCongr a)⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
