module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CommutingResiduals
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ResidualKernel
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Applying the commuting branch to the original omega action

Locality discharges the antecedent in 13.4.7(c). The reduced omega span
then gives the local action kernels, while (c) supplies normalization of
both residuals and the prime-to-three order of the full kernel. Apply the
coprime normalizer lift in the literal join, and transport the result back
to the original ambient subgroups.

Thus commuting residual actions imply relative normality of both
residuals, their commutator bound in both two-cores, and X=H₁H₂ as a set
product. This proves the part of case (i) consumed by
PlaneAmalgamSource1347, for any applicable original pair. It does not
assert the module decomposition or the remaining structural alternatives.
Source: Aschbacher–Smith 13.4.7, printed pp.899–900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

/-- The commuting action branch supplies the original product and commutator conclusions. -/
theorem original_pair_commuting_action {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
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
    (hcomm : ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)) :
    let X := A ⊔ B
    let K₁ := (pResidual 2 A).map A.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    X ∈ Chapter1.HOver G (T : Set G) ∧
      (K₁.subgroupOf X).Normal ∧ (K₂.subgroupOf X).Normal ∧
      ⁅K₁,K₂⁆ ≤ K₁.pCoreIn 2 ⊓ K₂.pCoreIn 2 ∧
      (X : Set G) = (A : Set G) * (B : Set G) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let C := X ⊓ centralizer (W : Set G)
  let N := centralizer (W.subgroupOf X : Set X)
  let A' := A.subgroupOf X
  let B' := B.subgroupOf X
  let K₁ := (pResidual 2 A).map A.subtype
  let K₂ := (pResidual 2 B).map B.subtype
  have hK₁X : K₁ ≤ X := (map_subtype_le _).trans le_sup_left
  have hK₂X : K₂ ≤ X := (map_subtype_le _).trans le_sup_right
  have hZX : Z ≤ X := by
    intro z hz
    exact (hTA.trans le_sup_left) (((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hWX : W ≤ X := conjugateSpanBy_le hZX X.le_normalizer
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  obtain ⟨hred,hkerA,hkerB,_⟩ := original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  let := hred.normal
  let : N.Normal := inferInstance
  obtain ⟨hnA,hnB,hr⟩ := hcentral hlocal
  have hnormA := kernel_normalizes_residual X Z K₁ hK₁X hnA
  have hnormB := kernel_normalizes_residual X Z K₂ hK₂X hnB
  have hcop := original_pair_kernel_primeToThree h₀ D m hTA hTB eA eB hne hindexA hindexB hr
  have hNmap : N.map X.subtype = C := by
    have he := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      ⊤ (W.subgroupOf X)
    simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hWX] using he.symm
  have hcop' : Nat.Coprime 3 (Nat.card N) := by
    rw [Nat.card_congr (N.equivMapOfInjective X.subtype X.subtype_injective).toEquiv,hNmap]
    exact hcop
  have hres (Y : Subgroup G) (hYX : Y ≤ X) :
      (pResidual 2 (Y.subgroupOf X)).map (Y.subgroupOf X).subtype =
        ((pResidual 2 Y).map Y.subtype).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hYX,
      map_subgroupOf_eq_of_le ((map_subtype_le _).trans hYX)]
  have hnormal (K : Subgroup G) (hKX : K ≤ X) (hn : C ≤ normalizer (K : Set G)) :
      N ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hKX]
    intro n hn'
    exact hn (hNmap ▸ mem_map_of_mem X.subtype hn')
  have hkernel (Y : Subgroup G) (hYX : Y ≤ X)
      (hk : Y ⊓ centralizer (W : Set G) = X.pCoreIn 2) :
      Y.subgroupOf X ⊓ N ≤ (Y.subgroupOf X).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hYX,map_subgroupOf_eq_of_le hWX,hk,
      pCoreIn_subgroupOf 2 Y X hYX,
      map_subgroupOf_eq_of_le ((Y.pCoreIn_le 2).trans hYX)]
    exact (le_inf (hk.symm.le.trans inf_le_left) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 hYX)
  have hc : ⁅(pResidual 2 A').map A'.subtype,(pResidual 2 B').map B'.subtype⁆ ≤ N := by
    rw [hres A le_sup_left,hres B le_sup_right]
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hK₁X,
      map_subgroupOf_eq_of_le hK₂X,hNmap]
    exact le_inf ((commutator_mono hK₁X hK₂X).trans (commutator_le_self X)) hcomm
  obtain ⟨h₁,h₂,hc,hprod⟩ := commuting_residuals (pair_goldschmidt hTA hTB eA eB hne) N hcop'
    (by rw [hres A le_sup_left]; exact hnormal K₁ hK₁X hnormA)
    (by rw [hres B le_sup_right]; exact hnormal K₂ hK₂X hnormB)
    (hkernel A le_sup_left hkerA) (hkernel B le_sup_right hkerB) hc
  rw [hres A le_sup_left] at h₁ hc
  rw [hres B le_sup_right] at h₂ hc
  refine ⟨hlocal,h₁,h₂,?_,?_⟩
  · have hm := map_mono (f := X.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hK₁X,map_subgroupOf_eq_of_le hK₂X] at hm
    apply hm.trans
    exact le_inf
      ((map_mono inf_le_left).trans (by
        rw [pCoreIn_subgroupOf 2 K₁ X hK₁X,
          map_subgroupOf_eq_of_le ((K₁.pCoreIn_le 2).trans hK₁X)]))
      ((map_mono inf_le_right).trans (by
        rw [pCoreIn_subgroupOf 2 K₂ X hK₂X,
          map_subgroupOf_eq_of_le ((K₂.pCoreIn_le 2).trans hK₂X)]))
  · have hm := congrArg (Set.image X.subtype) hprod
    change (Set.univ : Set X).image X.subtype =
      ((A' : Set X) * (B' : Set X)).image X.subtype at hm
    rw [Set.image_univ,←MonoidHom.coe_range,range_subtype,Set.image_mul,
      ←coe_map,←coe_map,map_subgroupOf_eq_of_le (show A ≤ X from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ X from le_sup_right)] at hm
    exact hm
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
