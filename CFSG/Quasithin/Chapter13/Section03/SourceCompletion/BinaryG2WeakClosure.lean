module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.BinaryG2Module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.Source

/-!
# Original unitary weak closure with the binary G₂ row discharged

Apply the proven B.4.6 fixed-space-family classification on the actual
normalizer quotient and its original elementary module. The natural-six
marking itself supplies rank six; the weak-closure and chosen-module
consumers therefore retain only the genuine earlier source geometry and
the normal derived-group module marking of 13.3.2.

Source: Aschbacher–Smith 13.3.19(2), printed p.896. The point-closure
hypothesis and r>3 come from 13.3.17–18 and are not asserted by this module.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE
variable {G:Type*} [Group G] [Finite G]

/-- The actual weak-closure consumer with the binary B.4.6 row discharged. -/
theorem weakClosure_two_of_binaryG2_action
    {V T:Subgroup G} [IsElementaryAbelian 2 V]
    (hTN:T≤normalizer (V:Set G))
    (hinter:∀g:G,V⊓V.map (MulAut.conj g).toMonoidHom≠⊥→
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (hr:(3:ℕ∞)<globalR V)
    (L:Subgroup (Automizer V)) [L.Normal]
    (e:L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:L) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v)) :
    indexedWeakClosure V T 2≤centralizer (V:Set G) := by
  have hd:Module.finrank (ZMod 2) (Additive V)=6:=
    E.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
  have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
  rw [Nat.card_zmod,hd] at hc
  have hV:rank V=6 := by
    change Nat.log 2 (Nat.card (Additive V))=6
    rw [hc,Nat.log_pow (by decide:1<2)]
  exact weakClosure_two_centralizes_of_unitary_action hTN hV hinter hr
    (binaryG2_automizer_row V L e E he)

/-- The chosen-module source consumer retains the genuine point-closure
hypotheses and actual normal derived marking; no B.4.6 callback remains. -/
theorem chosen_module_weakClosure_two_of_binaryG2
    {T:Sylow 2 G} {K V:Subgroup G} [IsElementaryAbelian 2 V]
    (d:Chapter12.Section02.ChosenModule T K V)
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (z:G) (hz:z≠1)
    (htrans:∀x∈V,x≠1→∃n∈normalizer (V:Set G),MulAut.conj n z=x)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (hr:(3:ℕ∞)<globalR V)
    (L:Subgroup (Automizer V)) [L.Normal]
    (e:L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:L) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v)) :
    indexedWeakClosure V (T:Subgroup G) 2≤centralizer (V:Set G) := by
  have hd:Module.finrank (ZMod 2) (Additive V)=6:=
    E.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
  have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
  rw [Nat.card_zmod,hd] at hc
  have hV:rank V=6 := by
    change Nat.log 2 (Nat.card (Additive V))=6
    rw [hc,Nat.log_pow (by decide:1<2)]
  exact chosen_module_weakClosure_two d hTN hV z hz htrans hr
    (binaryG2_automizer_row V L e E he)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
