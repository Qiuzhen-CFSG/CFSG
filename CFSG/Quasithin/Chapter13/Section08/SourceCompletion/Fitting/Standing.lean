module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Orders
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Standing source data for the Fitting residual calculation

Faithfulness of the original natural action identifies its barred component
with A6. The prescribed central quotient gives the ordinary or triple-cover
alternative. The unique nonidentity element of the original flag line is a
noncentral involution in T, and its normalizer centralizes it. These facts,
together with the proved solvable local edge, construct every field of the
standing data used by 13.8.12 on the unchanged ambient subgroups.

The universal earlier theorem 13.3.9 remains a separate input to the consumer;
no residual alternative or component exclusion is inserted into these data.
Source: Aschbacher--Smith, 13.8.12, printed p.950.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace LocalFitting
variable {G : Type*} [Group G] [Finite G]
 {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
 (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem barred_model : Nonempty (SolvableExclusion.Residual.barImage M V L ≃* alternatingGroup (Fin 6)) := by
  have hLM : L ≤ M := d.local_normalizer ▸ L.le_normalizer
  have hLV : L ≤ normalizer (V:Set G) := le_sup_left.trans d.normalizes_V
  let J := M ⊓ normalizer (V:Set G)
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion inf_le_right)
  let a : L →* MulAut V := f.comp (inclusion (le_inf hLM hLV))
  have hk : a.ker = centralCore L := by
    rw [d.centralCore_eq_centralizer]
    ext l
    change V.normalizerMonoidHom ⟨l.val,hLV l.property⟩ = 1 ↔ _
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
    rfl
  have hr : a.range = SolvableExclusion.Residual.barImage M V L := by
    change (f.comp (inclusion (le_inf hLM hLV))).range = (L.subgroupOf J).map f
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion (le_inf hLM hLV) l,l.property,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j.val,hj⟩,rfl⟩
  let eq : (L ⧸ centralCore L) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivRange a)
  exact ⟨(MulEquiv.subgroupCongr hr).symm.trans (eq.symm.trans d.local_quotient)⟩

theorem quotient_models :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) := by
  rcases local_odd_center_alternatives d with hc | hc
  · rcases local_quotient_alternatives d with ⟨e,_⟩ | ⟨e,_⟩
    · exact Or.inl ⟨e⟩
    · have hh := Nat.card_congr (centerCongr e).toEquiv
      rw [hc,Representation.Hexacode.even_center_card] at hh
      omega
  · exact Or.inr ⟨local_quotient_quasisimple d,hc,⟨local_central_quotient d⟩⟩

theorem line_involution : ∃ z:G, orderOf z = 2 ∧ z∈T ∧ z∈V₁ ∧
    z∉V ⊓ centralizer (L:Set G) ∧ G₁≤centralizer ({z}:Set G) := by
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1:V₁)).mp d.line_card
  have hz1 : (z:G)≠1 := fun he => hz (Subtype.ext he)
  have hp : V₁=zpowers (z:G) := by
    let : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
    have he := zpowers_eq_top_of_prime_card d.line_card hz
    have hm := congrArg (map V₁.subtype) he
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.coe_subtype] using hm.symm
  have hzorder : orderOf (z:G)=2 :=
    (Nat.card_zpowers (z:G)).symm.trans ((congrArg (fun A:Subgroup G=>Nat.card A) hp).symm.trans d.line_card)
  have hVLT : V≤L⊔(T:Subgroup G) := d.module_in_reduced.trans (sSup_le fun _ h=>h.1)
  have hVT : V≤(T:Subgroup G) := by
    have hcore := le_pCoreIn_of_normalizes (local_elementary d).isPGroup hVLT d.normalizes_V
    have hT := pCoreIn_le_sylow (L⊔(T:Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hT
    exact hcore.trans hT
  have hzV : (z:G)∈V := (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z.property
  refine ⟨z,hzorder,hVT hzV,z.property,?_,?_⟩
  · intro hc
    have hm : (⟨z,hzV⟩:V)∈(centralizer (L:Set G)).comap V.subtype := hc.2
    rw [local_centralizer_bot d] at hm
    exact hz1 (congrArg Subtype.val (show (⟨z,hzV⟩:V)=1 from hm))
  · rw [d.first_normalizer]
    exact (congrArg (fun A:Subgroup G=>normalizer (A:Set G)) hp).le.trans
      (normalizer_zpowers_eq_centralizer_of_order_two (z:G) hzorder).le

theorem residual_local_data {H:Subgroup G}
    (hH:H∈Source.Hz (one L T V₁) T G₁ M) :
    ∃z:G, SolvableExclusion.Residual.LocalData L (one L T V₁) (plus L T V₁) M V V₁ G₁ H T z := by
  obtain ⟨z,hzo,hzT,hzV,hzc,hG⟩ := line_involution d
  let := local_solvable d
  have hfirst : Group.IsSolvable (one L T V₁) := Group.isSolvable_of_isSolvable_injective
    (f:=inclusion (show one L T V₁≤one L T V₁⊔(T:Subgroup G) from le_sup_left))
    (inclusion_injective le_sup_left)
  let := hfirst
  exact ⟨z,{
    mem_Hz:=hH
    sylow_le:=d.local_normalizer ▸ d.normalizes_L
    involution:=hzo
    involution_mem:=hzT
    line_mem:=hzV
    noncentral:=hzc
    centralizer:=hG
    barred_model:=barred_model d
    quotient_models:=quotient_models d
    solvable_first:=hfirst
    solvable_plus:=Group.isSolvable_of_isSolvable_injective
      (f:=inclusion (plus_le_one L T V₁ d.line_stable))
      (inclusion_injective _)
    normalizes_first:=T_normalizes_one L T V₁ d.line_stable }⟩

end LocalFitting
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
