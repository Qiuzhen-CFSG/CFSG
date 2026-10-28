module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SourceComponent
public import Mathlib.Algebra.Field.ULift
/-!
# The literal component-product row for the 15.3 source consumer

The lower source proof supplies the actual factors of O²(G), multiplication,
local models and outer actor. Transporting the prime field through ULift
puts that same model in the consumer's universe. The product equivalence
is changed only in its target subtype, from the residual to the literal join.
The source endpoint derives the prime model and cubic input from genuine
A/C and the exceptional-vertex branch of the original SQTK quotient.

Source: Aschbacher–Smith F.6.17(2), F.6.18(3), printed pp.309–310,
and the 15.3 Goldschmidt comparison.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
  {G₁ G₂ : Subgroup G}
private noncomputable def componentPrimeFieldParameter (p : ℕ) (hp : p.Prime) : FieldParameter.{u} := by
  let : Fact p.Prime := ⟨hp⟩
  exact { Carrier := ULift.{u} (ZMod p)
          prime := p
          prime_isPrime := hp
          degree := 1
          degree_pos := by decide
          card := by simp }

theorem component_product_of_prime_model
    (d : ChapterF.SourceAssembly.SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    Alternative G₁ G₂ S := by
  obtain ⟨h24,hl,hr,⟨ht⟩,_,hD,hs,_,⟨j⟩,⟨f,hf⟩,_,t,htT,htK,hoK,hoD⟩ :=
    d.source_prime_conclusion e h hp h8 hm hc
  let D := pResidual 2 G ⊓ centralizer (d.component : Set G)
  let field := componentPrimeFieldParameter.{u} p Fact.out
  let eF : ZMod p ≃+* field.Carrier := ULift.ringEquiv.symm
  let jd : D ≃* C 3 := mulEquivOfPrimeCardEq hD (by simp [C])
  let prod : d.component × D ≃* (d.component ⊔ D : Subgroup G) :=
    f.trans (MulEquiv.subgroupCongr hs.symm)
  let row : ProductRow S := {
    field := field
    degree := rfl
    congruence := h24
    first := d.component
    second := D
    firstEquiv := j.trans (Atlas.fieldEquivPSL 2 eF)
    secondEquiv := jd
    product := prod
    product_apply := hf
    residual := hs.symm
    element := t
    mem_sylow := show t ∈ (S : Subgroup G) from (by rw [← hS]; exact htT)
    outside := htK
    firstOuter := hoK
    secondOuter := hoD }
  exact Alternative.three row ⟨(MulEquiv.subgroupCongr hS).symm.trans ht⟩ hl hr

theorem component_product_of_either_exceptional
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA κ U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC κ U)
    (q : ThreePrimeSQTKQuotient κ G)
    (d : ChapterF.SourceAssembly.SingleResidualComponent G₁ G₂)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) (S : Sylow 2 G)
    (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (ChapterF.twoCore_le_primeToThreeCore.trans
      (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient q.equiv.symm).le)
  obtain ⟨p,hp,ho,h8,hm⟩ := d.prime_psl2_of_either_exceptional
    (hA _) (hC _) q.sqtk q.equiv.symm h hcore hbad
  let : Fact p.Prime := ⟨hp⟩
  have hc := (d.exceptional_component_data q.equiv.symm h hcore hbad).1
  exact component_product_of_prime_model d q.equiv.symm h S hS ho h8 hm hc
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
