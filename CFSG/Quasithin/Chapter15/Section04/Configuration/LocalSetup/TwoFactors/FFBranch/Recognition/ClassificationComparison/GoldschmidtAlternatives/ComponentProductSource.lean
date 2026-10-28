module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SourceComponent

/-!
# The component-product alternative on the original 15.4 quotient

The factors are the actual component K and O²(G) ∩ C_G(K). Their original
multiplication and universal conjugation actions give every clause of Case3,
including outer action by every element of the common Sylow subgroup outside K.
The source endpoint obtains its prime model and cubic residual from the
proved exceptional-vertex component sieve, using the original A/C inputs.

Source: Aschbacher–Smith F.6.17(2), F.6.18(3), printed pp.309–310,
and the 15.4.18 comparison on printed p.1163.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {κ : GroupClass.{u}} {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
  {G₁ G₂ : Subgroup G}

omit [Finite G] in
private theorem outerOn_of_literal_automorphism (A : Subgroup G) [A.Normal] (t : G)
    (h : ∃ α : MulAut A, (∀ a : A, (α a : G) = t * (a : G) * t⁻¹) ∧
      α ∉ MulAut.innerSubgroup A) : GoldschmidtAlternatives.OuterOn A t := by
  obtain ⟨α,ha,ho⟩ := h
  refine ⟨by rw [A.normalizer_eq_top]; exact mem_top _,?_⟩
  rintro ⟨k,hk⟩
  apply ho
  refine ⟨k,?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact ((ha x).trans (hk x)).symm

theorem component_product_case3_of_prime_model
    (d : ChapterF.SourceAssembly.SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    GoldschmidtAlternatives.Case3 G₁ G₂ := by
  obtain ⟨h24,hl,hr,ht,hDn,hD,hs,hd,⟨j⟩,_,hall,t,htT,htK,_,_⟩ :=
    d.source_prime_conclusion e h hp h8 hm hc
  let D := pResidual 2 G ⊓ centralizer (d.component : Set G)
  let : d.component.Normal := d.normal
  let : D.Normal := hDn
  have hmK : ClassicalGroup.IsPSL d.component 2 p :=
    ⟨ZMod p,inferInstance,inferInstance,Nat.card_zmod _,⟨j⟩⟩
  let jd : D ≃* GoldschmidtAlternatives.C 3 :=
    mulEquivOfPrimeCardEq hD (by simp [GoldschmidtAlternatives.C])
  refine ⟨p,d.component,D,Fact.out,h24,hmK,⟨jd⟩,hs,hd,?_,ht,hl,hr,⟨t,htT,htK⟩,?_⟩
  · intro k a
    exact a.property.2 k k.property
  · intro t ht htK
    obtain ⟨hk,hd⟩ := hall t ht htK
    exact ⟨outerOn_of_literal_automorphism d.component t hk,
      outerOn_of_literal_automorphism D t hd⟩

theorem F618_component_product_case3_of_either_exceptional
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC κ U)
    (hH : IsSQTK κ H)
    {G₁ G₂ : Subgroup (threePrimeQuotient H)}
    (d : ChapterF.SourceAssembly.SingleResidualComponent G₁ G₂)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    GoldschmidtAlternatives.Case3 G₁ G₂ := by
  have hcore : pCore 2 (threePrimeQuotient H) = ⊥ := le_bot_iff.mp
    (ChapterF.twoCore_le_primeToThreeCore.trans
      (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient (MulEquiv.refl _)).le)
  obtain ⟨p,hp,ho,h8,hm⟩ := d.prime_psl2_of_either_exceptional
    hA (hC _) hH (MulEquiv.refl _) h hcore hbad
  let : Fact p.Prime := ⟨hp⟩
  have hc := (d.exceptional_component_data (MulEquiv.refl _) h hcore hbad).1
  exact component_product_case3_of_prime_model d (MulEquiv.refl _) h ho h8 hm hc
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
