module

public import CFSG.KnownSimple.ExceptionalModels
public import Theory.GroupTheory.CComponent.TwoComponent.InvolutionOddCore
public import Theory.SpecificGroups.Triality.InvolutionTwoComponents
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms

/-!
# Twisted exceptional reductions for B₂

The binary triality outer-involution branch is proved on an arbitrary group
with the catalogue's actual model isomorphism. Transport retains the original
automorphism, its fixed subgroup, and its genuine two-component.

The four conditional catalogue reductions record the remaining local inputs:
cyclic fixed-group odd cores for twisted E₆, trivial fixed-group odd cores for
small Ree, inner centralizers in binary triality together with all odd-
characteristic triality fixed groups, and involution centralizers in large Ree.
For large Ree, the proved innerness of all involutory automorphisms discharges
the automorphism premise. Simplicity of the model is inherited from the supplied
simple group. None of these conditional reductions asserts the full family
B₂ theorem before its local inputs are proved.

The models and their field conventions are exactly those in ExceptionalModels,
Triality.StandardModel and ReeF4.Model. In particular odd-characteristic triality
and the full quadratic coefficient field for twisted E₆ are retained.

Sources: GLS II, Definition 2.4 and Lemma 5.28
(`refs/KGroup/GLS2/ChapterA.tex`, `ChapterB.tex`); GLS3, §§2.5, 4.5 and 4.9
(`refs/KGroup/GLS3/chapter2.tex`, `chapter4.tex`).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
variable {S : Type*} [Group S]

/-- The outer binary triality source branch on the original group and action. -/
theorem triality_binary_outer_twoComponent_quasisimple (n : ℕ) (hn : 0 < n)
    (hS : Triality.Standard.IsTrialityGroupAt (2 ^ n) S)
    (a : MulAut S) (ha : orderOf a = 2) (houter : a ∉ MulAut.innerSubgroup S)
    (L : Subgroup a.fixedSubgroup) (hL : L.IsTwoComponent) : IsQuasisimple L := by
  obtain ⟨P, hq, ⟨e⟩⟩ := hS
  have hP := P.eq_binaryParameters_of_q_eq n hn hq
  subst P
  let b := MulAut.congr e a
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hbo : b ∉ MulAut.innerSubgroup (Triality.Standard.BinaryCarrier n hn) := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := (MulAut.congr_inner_iff e a).mp ⟨g, hg.symm⟩
    exact houter ⟨x, hx.symm⟩
  let f := MulAut.fixedSubgroupCongr e a
  have hqL := Triality.Standard.InvolutionTwoComponents.binary_outer_twoComponent_quasisimple
    n hn b hb hbo (L.map f.toMonoidHom) (hL.map_equiv f)
  exact IsQuasisimple.of_mulEquiv (f.subgroupMap L).symm (hG := hqL)

variable [IsSimpleGroup S]

/-- Twisted E₆ reduces to cyclicity, allowing its centralizer odd tori. -/
theorem of_twistedE6_cyclic_fixed_oddCore {q : ℕ}
    (hS : ExceptionalGroup.IsTwistedE6 S q)
    (hcore : ∀ (p m : ℕ) [Fact p.Prime], IsSimpleGroup (TwistedE6.Model p m) →
      ∀ a : MulAut (TwistedE6.Model p m), orderOf a = 2 →
        IsCyclic (pPrimeCore 2 a.fixedSubgroup)) : HasInvolutoryB2 S := by
  obtain ⟨p, m, hp, _, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (TwistedE6.Model p m) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixed_cyclic_oddCore
    (hcore p m inferInstance)).of_mulEquiv e

/-- The small Ree reduction preserves the literal matrix field and parameter. -/
theorem of_reeG2_fixed_oddCore {q : ℕ} (hS : ExceptionalGroup.IsReeG2 S q)
    (hcore : ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 3],
      Atlas.ReeG2.Parameters F m → IsSimpleGroup (Atlas.ReeG2.Model F m) →
      ∀ a : MulAut (Atlas.ReeG2.Model F m), orderOf a = 2 →
        pPrimeCore 2 a.fixedSubgroup = ⊥) : HasInvolutoryB2 S := by
  obtain ⟨m, F, hF, hfin, hchar, hp, _, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (Atlas.ReeG2.Model F m) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixed_oddCore_eq_bot
    (hcore m F hp inferInstance)).of_mulEquiv e

/-- The full triality family retains odd characteristic; its binary outer branch is discharged. -/
theorem of_triality_odd_and_binary_inner_oddCore
    (hS : Triality.Standard.IsTrialityGroup S)
    (hbinary : ∀ (n : ℕ) (hn : 0 < n) (x : Triality.Standard.BinaryCarrier n hn),
      orderOf x = 2 →
        pPrimeCore 2 (centralizer ({x} : Set (Triality.Standard.BinaryCarrier n hn))) = ⊥)
    (hodd : ∀ P : Triality.Standard.Parameters, P.prime ≠ 2 →
      IsSimpleGroup (Triality.Standard.Carrier P) →
      ∀ a : MulAut (Triality.Standard.Carrier P), orderOf a = 2 →
        pPrimeCore 2 a.fixedSubgroup = ⊥) : HasInvolutoryB2 S := by
  obtain ⟨P, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (Triality.Standard.Carrier P) := e.symm.isSimpleGroup
  by_cases hp : P.prime = 2
  · obtain ⟨n, hn, rfl⟩ := (Triality.Standard.exists_binaryParameters_iff P).mpr hp
    exact (Triality.Standard.InvolutionTwoComponents.binary_hasInvolutoryB2_of_inner_oddCore
      n hn (hbinary n hn)).of_mulEquiv e
  · exact (HasInvolutoryB2.of_fixed_oddCore_eq_bot
      (hodd P hp inferInstance)).of_mulEquiv e

/-- All large Ree involutory automorphisms are inner, leaving only element centralizers. -/
theorem of_reeF4_centralizer_oddCore (hS : ReeF4.IsReeF4Model S)
    (hcore : ∀ (m : ℕ), 1 ≤ m → IsSimpleGroup (ReeF4.Model m) →
      ∀ x : ReeF4.Model m, orderOf x = 2 →
        pPrimeCore 2 (centralizer ({x} : Set (ReeF4.Model m))) = ⊥) :
    HasInvolutoryB2 S := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  apply HasInvolutoryB2.of_mulEquiv (e := e)
  apply HasInvolutoryB2.of_inner_of_centralizer_oddCore_eq_bot
  · intro a ha
    have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
    obtain ⟨x, hx⟩ := ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one hm a
      ha2
    exact ⟨x, hx.symm⟩
  · exact hcore m hm inferInstance

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
