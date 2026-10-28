module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.EqualCoreAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CommutingAction

/-!
# The equal-core solvable case for every admitted original pair

The original source hypotheses supply locality, escape, the order-four
omega center, reducedness of its whole orbit span, and both exact local
kernels. EqualCoreAction then bounds that span by sixteen and proves that
the two residual actions commute. The literal relative-normality and
prime-to-three clause activates CommutingAction, lifting through the full
kernel to both residual two-core bounds and the product X=AB.

Thus the solvable noncommuting branch has unequal vertex two-cores.
No additional small-module, escape, unconditional residual or commuting
premise is supplied. The universal preceding structural input retains its
original contract. Unequal-core solvable recognition and the plane
exclusion remain necessary for the universal 13.4.7 interfaces.

Source: Aschbacher--Smith 13.4.7(1), printed pp.900--901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))


private theorem pair_local_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {X : Subgroup G} (hX : X ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple X := by
  let R := X.pCoreIn 2
  let N := normalizer (R : Set G)
  have hXN : X ≤ N := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hN : IsTwoLocal N := ⟨R,hX,isPGroup_pCoreIn 2 X,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (X.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.injective⟩

include h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral
/-- The solvable original pair with equal vertex two-cores satisfies the
product and both residual-commutator bounds in 13.4.7(1i). -/
theorem original_pair_equal_core_solvable
    (h₀ : Hypothesis1331 T L) (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (he : A.pCoreIn 2 = B.pCoreIn 2) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    let K₁ := (pResidual 2 A).map A.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    Nat.card W ≤ 16 ∧ ⁅K₁,K₂⁆ ≤ K₁.pCoreIn 2 ⊓ K₂.pCoreIn 2 ∧
      (X : Set G) = (A : Set G) * (B : Set G) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let A' := A.subgroupOf X
  let B' := B.subgroupOf X
  let W' := W.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hZT : Z ≤ (T : Subgroup G) := fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hWX : W ≤ X := conjugateSpanBy_le (hZT.trans hTX) X.le_normalizer
  have hg := pair_goldschmidt hTA hTB eA eB hne
  obtain ⟨hlocal,_,hZ,_,_⟩ := original_pair_source_seed h structural D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral
  obtain ⟨hred,hkA,hkB,hkT⟩ := original_pair_action_kernel h₀ D m hTA hTB eA eB hne
    hindexA hindexB
  have hAB : A' ⊓ B' = (T : Subgroup G).subgroupOf X := by
    change (A ⊓ B).subgroupOf X = _
    rw [intersection_eq_sylow hTA hTB eA eB hne]
  have homega : (omegaOneCenterAmbient (A' ⊓ B')).map X.subtype = Z := by
    rw [hAB,←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hTX]
  have hseed : omegaOneCenterAmbient (A' ⊓ B') ≤ W' := by
    intro z hz
    exact le_conjugateSpanBy Z X (homega ▸ mem_map_of_mem X.subtype hz)
  have hZ' : Nat.card (omegaOneCenterAmbient (A' ⊓ B')) = 4 := by
    rw [←card_map_of_injective X.subtype_injective,homega]
    exact hZ
  have hker (Y : Subgroup G) (hYX : Y ≤ X)
      (hkY : Y ⊓ centralizer (W : Set G) = X.pCoreIn 2) :
      Y.subgroupOf X ⊓ centralizer (W' : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hYX,map_subgroupOf_eq_of_le hWX,hkY]
    rfl
  have he' : A'.pCoreIn 2 = B'.pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 A X le_sup_left,pCoreIn_subgroupOf 2 B X le_sup_right,he]
  have hkT' : (A' ⊓ B') ⊓ centralizer (W' : Set X) = pCore 2 X := by
    rw [hAB]
    exact hker (T : Subgroup G) hTX hkT
  have hsmall := equal_core_seed_card hg hred hseed hZ' hkT' he'
  have hcomm := equal_core_solvable_seed_commutes (pair_local_sqtk h₀.qtke hlocal.1.1)
    hg hred hseed hZ' (hker A le_sup_left hkA) (hker B le_sup_right hkB) hkT' he' hs
  have hc : ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (W : Set G) := by
    have hm := map_mono (f := X.subtype) hcomm
    rw [map_commutator,map_embedded_pResidual,map_embedded_pResidual,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right] at hm
    apply hm.trans
    intro g hg
    obtain ⟨g,hg,rfl⟩ := hg
    intro w hw
    have hh := hg ⟨w,hWX hw⟩ hw
    exact congrArg Subtype.val hh
  obtain ⟨_,_,_,hbound,hprod⟩ := original_pair_commuting_action h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcentral hc
  refine ⟨?_,hbound,hprod⟩
  rwa [Nat.card_congr (subgroupOfEquivOfLe hWX).toEquiv] at hsmall
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
