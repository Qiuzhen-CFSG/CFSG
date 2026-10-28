module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex

/-!
# The original prime-component quotient

The kernel of conjugation on the normal source component is the actual
O₂(H). Its image contains the inner automorphism group. The proved prime
PSL₂ outer index is two, so that image is either the inner group or all
automorphisms, yielding the precise PSL₂/PGL₂ quotient alternatives.

Source: Aschbacher--Smith 2.5.16 and 2.5.21, printed pp.560,565.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual original quotient is PSL₂ or PGL₂ for a normal prime-field component. -/
theorem MathieuSourceSetup.normal_prime_core_quotient
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p)) :
    Nonempty ((H ⧸ pCore 2 H) ≃* PSL(2,ZMod p)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p)) := by
  let D := K.subgroupOf H
  let eD : D ≃* PSL(2,ZMod p) := (subgroupOfEquivOfLe c.component_le).trans eK
  let a : H →* MulAut PSL(2,ZMod p) :=
    (MulAut.congr eD).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut D)
  have hk : a.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr eD).injective]
    exact MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
  let eQ : (H ⧸ pCore 2 H) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivRange a)
  let I := MulAut.innerSubgroup PSL(2,ZMod p)
  have hinner : I ≤ a.range := by
    rintro _ ⟨u,rfl⟩
    refine ⟨(eD.symm u : H), ?_⟩
    change MulAut.congr eD (MulAut.conjNormal (H := D) (eD.symm u : H)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj, eD.apply_symm_apply]
  by_cases he : a.range = I
  · let eI : PSL(2,ZMod p) ≃* I := MonoidHom.ofInjective
      (Theory.GroupTheory.conj_injective_of_center_eq_bot (psl2_center_eq_bot (ZMod p)))
    exact Or.inl ⟨eQ.trans ((MulEquiv.subgroupCongr he).trans eI.symm)⟩
  · have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    have hindex : I.index = 2 := Theory.PSL2.prime_card_inner_index
      (ZMod p) ho (by omega) (by simp)
    have hlt : a.range.index < 2 := by
      simpa only [hindex] using Subgroup.index_strictAnti (lt_of_le_of_ne hinner (Ne.symm he))
    have hpos : 0 < a.range.index := Nat.card_pos
    have htop : a.range = ⊤ := Subgroup.index_eq_one.mp (by omega)
    have hodd : IsOddPrimePower (Nat.card (ZMod p)) :=
      ⟨p,1,Fact.out,ho,by decide,by simp⟩
    have hlarge : 3 < Nat.card (ZMod p) := by simpa using (show 3 < p by omega)
    let eA : GorensteinWalter.PGL2 (ZMod p) ≃* MulAut PSL(2,ZMod p) :=
      MulEquiv.ofBijective (pgl2InnerAutPSL2 (ZMod p) hodd hlarge)
        ⟨pgl2InnerAutPSL2_injective _ _ _,
          Theory.PSL2.prime_card_pgl_coverage (p := p) _ (by simp) _ _⟩
    exact Or.inr ⟨eQ.trans ((MulEquiv.subgroupCongr htop).trans (topEquiv.trans eA.symm))⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
