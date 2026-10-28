module
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Mathlib.Order.Preorder.Finite
/-!
# The source catalogue on an actual involution centralizer

Extend the chosen Sylow subgroup of C_G(i) to an ambient Sylow subgroup.
A central involution of that ambient two-group and a maximal two-local over
its centralizer supply the original 1.1.6 hypotheses. The complete known-simple
1.1.5 theorem then classifies each actual ordinary component, preserving its
conjugation action, commutator equality, and both subgroup inclusions.

No containing model, fixed-group description, or chosen-mark premise is
assumed. This is the containing-component input used in 2.5.19 after I.3.2.
Source: Aschbacher–Smith 1.1.5–6, pp.501–503, and 2.5.19, p.561.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
open Chapter15.Section03.Candidates.ComponentStructure
variable {G:Type*} [Group G] [Finite G]

/-- The actual full Sylow and central involution satisfy every source hypothesis. -/
theorem involution_centralizer_marked_setup {κ:GroupClass}
    (hG:IsQTKE κ G) (i:G) (hi:orderOf i=2)
    (P:Sylow 2 (centralizer ({i}:Set G))) :
    ∃(T:Sylow 2 G) (z:G) (M:Subgroup G),
      (P:Subgroup (centralizer ({i}:Set G))).map (centralizer ({i}:Set G)).subtype≤(T:Subgroup G) ∧
      z∈centerIn (T:Subgroup G) ∧ orderOf z=2 ∧ IsMaximalTwoLocal M ∧
      Lemma115Hypotheses (centralizer ({i}:Set G)) P M z := by
  let B:=zpowers i
  let C:=centralizer ({i}:Set G)
  have hBne:B≠⊥:=zpowers_ne_bot.mpr (by intro h;simp [h] at hi)
  have hB:IsPGroup 2 B:=IsPGroup.of_card (n:=1) (by simpa only [B,Nat.card_zpowers,pow_one] using hi)
  have hBC:B≤C:=zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCC:centralizer (B:Set G)=C:=by
    change centralizer (zpowers i:Set G)=centralizer ({i}:Set G)
    rw [zpowers_eq_closure,centralizer_closure]
  have hCN:C≤normalizer (B:Set G):=hCC ▸ Subgroup.centralizer_le_normalizer _
  have hBP:B≤(P:Subgroup C).map C.subtype:=
    (le_pCoreIn_of_normalizes hB hBC hCN).trans (pCoreIn_le_sylow C P)
  obtain ⟨T,hPT⟩:=(P.isPGroup'.map C.subtype).exists_le_sylow
  have hiT:i∈(T:Subgroup G):=hPT (hBP (mem_zpowers i))
  let : Nontrivial (T:Subgroup G):=⟨⟨⟨i,hiT⟩,1,by intro he;have hh:i=1:=congrArg Subtype.val he;simp [hh] at hi⟩⟩
  let : Nontrivial (center (T:Subgroup G)):=T.isPGroup'.center_nontrivial
  have hd:2∣Nat.card (center (T:Subgroup G)) := by
    rcases (T.isPGroup'.to_subgroup (center (T:Subgroup G))).card_eq_or_dvd with h|h
    · exact (ne_of_gt T.isPGroup'.bot_lt_center (Subgroup.card_eq_one.mp h)).elim
    · exact h
  obtain ⟨z,hz⟩:=exists_prime_orderOf_dvd_card' (G:=center (T:Subgroup G)) 2 hd
  have hz2:orderOf ((z:(T:Subgroup G)):G)=2:=
    (Subgroup.orderOf_coe (z:(T:Subgroup G))).trans ((Subgroup.orderOf_coe z).trans hz)
  have hzC:((z:(T:Subgroup G)):G)∈centerIn (T:Subgroup G):=by
    refine ⟨(z:(T:Subgroup G)).property,?_⟩
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨x,hx⟩)
  obtain ⟨M,hCM,hM⟩:=Finite.exists_le_maximal (isTwoLocal_involution_centralizer hz2)
  refine ⟨T,z,M,hPT,hzC,hz2,hM,?_⟩
  apply lemma_1_1_6 hBne hB hBC hCC.le hCN P T hPT hz2 hzC.1 hzC.2 hM hCM
  intro N hN hTN
  exact mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN)

/-- The complete marked source catalogue on a component of C_G(i). -/
theorem involution_component_source_catalogue
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G) (i:G) (hi:orderOf i=2)
    (D:Subgroup (centralizer ({i}:Set G)))
    (hD:IsComponent (centralizer ({i}:Set G)) D) :
    ∃(P:Sylow 2 (centralizer ({i}:Set G))) (M:Subgroup G) (z:G),
      Lemma115Hypotheses (centralizer ({i}:Set G)) P M z ∧
      D.map (centralizer ({i}:Set G)).subtype=⁅D.map (centralizer ({i}:Set G)).subtype,zpowers z⁆ ∧
      ¬D.map (centralizer ({i}:Set G)).subtype≤M ∧ HasModelAction115 D z := by
  let P:Sylow 2 (centralizer ({i}:Set G)):=default
  obtain ⟨T,z,M,_,_,_,_,h⟩:=involution_centralizer_marked_setup hG.toIsQTKE i hi P
  exact ⟨P,M,z,h,lemma_1_1_5_three_knownSimple hG _ P M z h D hD⟩
end CFSG.Quasithin.Chapter1
