module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Models
public import Theory.SpecificGroups.BinaryComponentFixers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# Ordinary small binary Lie component centralizers

The intrinsic fixer bounds for L4(2), L5(2), G2(2)' and the Tits group
force the equality of the actual cubic-residual and component centralizers.
Each recognized quotient also supplies centerlessness, three-rank and the
outer two-group bound; no additional model Facts are assumed.
Source: Aschbacher--Smith15.1.22(4),(7).
-/
public section
namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

@[expose] def SmallBinaryOrdinaryModel (Q : Type*) [Group Q] : Prop :=
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL Q n 2) ∨
  Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (Q ≃* Tits.ParrottGroup)

private theorem binary_linear_equiv {Q : Type*} [Group Q] {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSL Q n 2) : Nonempty (Q ≃* SL(n,ZMod 2)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact ⟨(e.trans (Atlas.fieldEquivPSL n k)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL hn)⟩

theorem facts_of_small_binary_model {Q : Type*} [Group Q] [Finite Q]
    (he : SmallBinaryOrdinaryModel Q) : Facts Q := by
  rcases he with ⟨n,hn,hm⟩ | he | he
  · obtain ⟨e⟩ := binary_linear_equiv (by omega : 0 < n) hm
    exact Facts.of_equiv e (linear hn)
  · obtain ⟨e⟩ := he
    exact Facts.of_equiv e g2
  · obtain ⟨e⟩ := he
    exact Facts.of_equiv (e.trans Tits.parrottFiniteImageEquiv) tits_facts

theorem ordinary_small_binary_model_centralizer (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hodd : pPrimeCore 2 d.G1 = ⊥) (hSL : Chapter1.IsSylowIn 2 d.SL d.L)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)]
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (hout : ¬ (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype ≤ d.MZ) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  have hf := facts_of_small_binary_model he
  rcases he with ⟨n,hn,hm⟩ | he | he
  · obtain ⟨e⟩ := binary_linear_equiv (by omega : 0 < n) hm
    exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A _ hfix => linear_fixers hn P A hfix) hout
  · obtain ⟨e⟩ := he
    exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A hA hfix => @g2_fixers P A hA hfix) hout
  · obtain ⟨e⟩ := he
    exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf
      (e.trans Tits.parrottFiniteImageEquiv)
      (fun P A _ hfix => tits_fixers P A hfix) hout
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
