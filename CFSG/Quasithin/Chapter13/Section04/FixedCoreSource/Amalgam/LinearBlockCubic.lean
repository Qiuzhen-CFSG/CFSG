module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearBlockExclusion
public import Theory.Representation.PSL3Two.SixCubic
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients

/-!
# The omega contribution in the original linear block exclusion

Every cubic of the actual join X lies in its two-residual, which is the
selected component K. Its image under the component's literal quotient
marking has order three, since the full kernel is a two-group. Restricting
the previously proved whole-module equivalence therefore supplies the two
cubic contributions on the actual omega module in all three linear rows.

The final application discharges this module premise of the three-factor
obstruction. The source family inclusion, total block budget and outer
quotient contribution remain explicit. Their construction from the literal
K₂=L₂, the earlier trichotomy and the remaining model exclusions are still
required for source 13.4.7(4) and PlaneAmalgamSource1347.
Source: Aschbacher–Smith 13.4.7(4), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- Every original cubic has two movement contributions on the actual omega
module, in all three linear module cases. -/
theorem original_pair_linear_omega_cubic_length
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (E : Subgroup (A ⊔ B : Subgroup G)) (hE : Nat.card E = 3) :
    2 ≤ conjugationCubicLength E
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)).subgroupOf (A ⊔ B)) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hEK : E ≤ K := by
    rw [←(original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1]
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    exact (show Nat.Coprime 2 (Nat.card E) by rw [hE];decide).of_dvd_right
      (E.orderOf_dvd_natCard hx)
  let E' := E.map X.subtype
  have hE'C : E' ≤ C := map_mono hEK
  have hE' : Nat.card E' = 3 :=
    (card_map_of_injective (K := E) X.subtype_injective).trans hE
  obtain ⟨he,e,_,_,_,hm,_⟩ := original_pair_linear_whole_module h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := he
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  let q : E' →* BinaryLinearThree.Group := f.comp (inclusion hE'C)
  have hk : f.ker = pCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hEc : Nat.card (E'.subgroupOf C) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hE'C).toEquiv).trans hE'
  have hqrange : q.range = (E'.subgroupOf C).map f := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inclusion hE'C a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a.val,ha⟩,rfl⟩
  have hq : Nat.card q.range = 3 := by
    rw [hqrange]
    exact GLS3.Chapter5.cubic_image_card_of_two_kernel f (hk ▸ pCore_isPGroup) _ hEc
  have hEU : E' ≤ normalizer (U : Set G) := (map_subtype_le E).trans
    (le_normalizer_conjugateSpanBy Z X)
  have restrict {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
      (a : Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)))))) :
      Nonempty (Representation.Equiv (σ.comp q)
        (Representation.elementaryRepresentation (U.normalizerMonoidHom.comp (inclusion hEU)))) := by
    refine ⟨{toLinearEquiv := a.toLinearEquiv, isIntertwining' := ?_}⟩
    intro x
    exact a.isIntertwining' (inclusion hE'C x)
  have hm' := hm.imp (fun ⟨a⟩ => restrict _ a)
    (fun hh => hh.imp (fun ⟨a⟩ => restrict _ a) (fun ⟨a⟩ => restrict _ a))
  have hb := BinaryLinearThree.SixCubic.conjugation_length_ge_two E' U hEU q hq hm'
  have hEcX : E'.subgroupOf X = E := by
    change (E.map X.subtype).comap X.subtype = E
    exact comap_map_eq_self_of_injective X.subtype_injective E
  rw [←NoncentralChiefRefinement.CubicComparison.length_subgroupOf E' U X
    (map_subtype_le E) hUX,hEcX] at hb
  exact hb

/-- The actual omega contribution is discharged in the original three-factor
exclusion; only the block budget and outer section contribution remain. -/
theorem original_pair_linear_block_budget_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hfamily : elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G))
    (E : Subgroup (A ⊔ B : Subgroup G)) (hE : Nat.card E = 3)
    (hbudget : conjugationCubicLength E ((B.pCoreIn 2).subgroupOf (A ⊔ B)) ≤ 3)
    (houter : 1 ≤ sectionCubicLength E (pCore 2 (A ⊔ B : Subgroup G))
      ((B.pCoreIn 2).subgroupOf (A ⊔ B))) : False :=
  original_pair_linear_three_factor_budget_impossible h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    hfamily E hE hbudget
    (original_pair_linear_omega_cubic_length h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL E hE) houter

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
