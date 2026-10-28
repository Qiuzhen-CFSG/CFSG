module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PairFrattini
public import Theory.GroupTheory.AbelianQuotientFixedSubgroup
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.RelativeCentralLayerCentralizerIndex
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# The source36 Sylow fixed-index bound

The first conjugate module pair lies in the normal A₆. An involution
centralizing that component has all remaining Thompson commutators in the
second order-two fixed line. Thus its centralizer has index at most two
in R. Extend this intersection to a Sylow subgroup of its ambient involution
centralizer. Noncharacteristic two makes this Sylow proper in an ambient
Sylow, improving the original index-eight bound to four.

Source: Aschbacher–Smith 2.4.36, printed p.549. The final application
retains the original paired coordinates and the actual involution.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

theorem second_factor_derived_le_fixed :
    ⁅c.U₂ ⊔ c.V₂,c.U₂ ⊔ c.V₂⁆ ≤ c.U₂ ⊓ centralizer (sourceR d : Set G) := by
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 c.V₂ := IsElementaryAbelian.map (MulAut.conj c.x⁻¹).toMonoidHom
  have hU : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hV : c.V₂ ≤ sourceR d := c.baumann ▸ c.second.conjugate_le (c.original.R_normal c.x_mem)
  have hnU : sourceR d ≤ normalizer (c.U₂ : Set G) :=
    c.baumann ▸ c.second.coordinates.normalizes
  have hnV : sourceR d ≤ normalizer (c.V₂ : Set G) :=
    c.baumann ▸ c.second.conjugate_normalized (c.original.R_normal c.x_mem)
  rw [c.second_fixed_line.2.1]
  apply le_inf
  · exact commutator_sup_le_of_normalized_derived c.U₂ c.V₂ (hV.trans hnU)
      (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
  · rw [sup_comm c.U₂ c.V₂]
    exact commutator_sup_le_of_normalized_derived c.V₂ c.U₂ (hU.trans hnV)
      (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)

theorem centralizer_index_le_two_of_first_factor
    (r : G) (hr : r ∈ sourceR d) (hr2 : orderOf r = 2)
    (hrF : r ∈ centralizer ((c.U₁ ⊔ c.V₁ : Subgroup G) : Set G)) :
    (centralizer ({r} : Set G)).relIndex (sourceR d) ≤ 2 := by
  let R := sourceR d
  let F₁ := c.U₁ ⊔ c.V₁
  let F₂ := c.U₂ ⊔ c.V₂
  let C := c.U₂ ⊓ centralizer (R : Set G)
  have hgen : R = (F₁ ⊔ F₂) ⊔ c.D := c.product.2.1
  have hF₁R : F₁ ≤ R := hgen ▸ (le_sup_left.trans le_sup_left)
  have hF₂R : F₂ ≤ R := hgen ▸ (le_sup_right.trans le_sup_left)
  have hDR : c.D ≤ R := hgen ▸ le_sup_right
  have hRC : R ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hRN : R ≤ normalizer (C : Set G) := hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hFF : ⁅F₁,F₂⁆ = ⊥ := FourModuleOrbit.conjugate_factors_commute c.orbit.toInputs
  have hDF : ⁅c.D,F₂⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (c.product.2.2.1.trans (centralizer_le hF₂R))
  have hRF : ⁅R,F₂⁆ ≤ C := by
    have h₁ : ⁅F₁ ⊔ F₂,F₂⁆ ≤ C := commutator_sup_le_of_relative_normal R F₁ F₂ F₂ C
      hRN hF₁R hF₂R (by rw [hFF]; exact bot_le) c.second_factor_derived_le_fixed
    have h₂ := commutator_sup_le_of_relative_normal R (F₁ ⊔ F₂) c.D F₂ C
      hRN (sup_le hF₁R hF₂R) hDR h₁ (by rw [hDF]; exact bot_le)
    simpa only [←hgen] using h₂
  have hPr : zpowers r ≤ R := zpowers_le.mpr hr
  have hFr : ⁅F₁,zpowers r⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hrF)
  have hDr : ⁅c.D,zpowers r⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (c.product.2.2.1.trans (centralizer_le hPr))
  have hRr : ⁅R,zpowers r⁆ ≤ C := by
    have h₂r : ⁅F₂,zpowers r⁆ ≤ C := by
      rw [commutator_comm]
      exact (commutator_mono hPr le_rfl).trans hRF
    have h₁ := commutator_sup_le_of_relative_normal R F₁ F₂ (zpowers r) C
      hRN hF₁R hF₂R (by rw [hFr]; exact bot_le) h₂r
    have h₂ := commutator_sup_le_of_relative_normal R (F₁ ⊔ F₂) c.D (zpowers r) C
      hRN (sup_le hF₁R hF₂R) hDR h₁ (by rw [hDr]; exact bot_le)
    simpa only [←hgen] using h₂
  have hindex : ((⊥ : Subgroup G).subgroupOf (zpowers r)).index = 2 := by
    rw [bot_subgroupOf,index_bot,Nat.card_zpowers,hr2]
  have hh := relIndex_centralizer_le_card_of_central_index_two_layer
    R (zpowers r) ⊥ C (by intro a ha; rw [coe_bot]; exact mem_centralizer_singleton_iff.mpr (by simp)) hRC hindex hRr
  rw [show Nat.card C = 2 from c.second_fixed_line.1] at hh
  simpa only [zpowers_eq_closure,centralizer_closure] using hh

end SourcePairCoordinates

namespace SourceCentralizerGeometry
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)

theorem component_centralizer_index_le_two
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (r : G) (hr : r ∈ sourceR d) (hr2 : orderOf r = 2)
    (hrK : r ∈ centralizer (K.map (involutionCentralizer g.z₂).subtype : Set G)) :
    (centralizer ({r} : Set G)).relIndex (sourceR d) ≤ 2 := by
  let H := involutionCentralizer g.z₂
  let J := K.map H.subtype
  have hUJ : c.U₁ ≤ J := (map_subtype_le _).trans hLK
  have hn : H ≤ normalizer (J : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rw [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh
  have hVJ : c.V₁ ≤ J := by
    have hx : c.x⁻¹ ∈ normalizer (J : Set G) := hn (H.inv_mem g.x_second)
    exact (map_mono hUJ).trans_eq (mem_normalizer_iff_map_conj_eq.mp hx)
  exact c.centralizer_index_le_two_of_first_factor r hr hr2
    ((centralizer_le (show c.U₁ ⊔ c.V₁ ≤ J from sup_le hUJ hVJ)) hrK)

/-- In the original index-four Thompson geometry, a noncharacteristic-two
involution centralizer has a Sylow subgroup on which the second mark has
fixed index at most four. -/
theorem exists_sylow_fixed_index_le_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (r : G) (hr2 : orderOf r = 2)
    (hi : (centralizer ({r} : Set G)).relIndex (sourceR d) ≤ 2)
    (hnot : centralizer ({r} : Set G) ∉ Chapter1.He G) :
    ∃ P : Sylow 2 (centralizer ({r} : Set G)),
      (sourceR d).subgroupOf (centralizer ({r} : Set G)) ≤ P ∧
      (centralizer ({g.z₂} : Set G)).relIndex
        ((P : Subgroup _).map (centralizer ({r} : Set G)).subtype) ≤ 4 := by
  let C := centralizer ({r} : Set G)
  let R := sourceR d
  let A := R ⊓ C
  have hRT : R ≤ (T : Subgroup G) := (show R ≤ (d.S : Subgroup d.H).map d.H.subtype from
    sSup_le (fun _ h => h.1)).trans c.original.T_le
  have hAT : A ≤ (T : Subgroup G) := inf_le_left.trans hRT
  obtain ⟨P,hP⟩ := ((T.isPGroup'.to_le hRT).comap_subtype (K := C)).exists_le_sylow
  let B := (P : Subgroup C).map C.subtype
  have hAB : A ≤ B := by
    intro a ha
    exact mem_map_of_mem C.subtype (hP (show (⟨a,ha.2⟩ : C) ∈ R.subgroupOf C from ha.1))
  obtain ⟨Q,hBQ⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have hQB : ¬ (Q : Subgroup G) ≤ B := by
    intro hle
    apply hnot
    exact Chapter1.twoLocal_mem_He_of_sylow_le Q (hG.evenCharacteristic Q)
      (Theory.GroupTheory.isTwoLocal_involution_centralizer hr2)
      (hle.trans (map_subtype_le _))
  have hBQi : 2 ≤ B.relIndex (Q : Subgroup G) := by
    have hpos : 0 < B.relIndex (Q : Subgroup G) := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : B.relIndex (Q : Subgroup G) ≠ 1 := fun hh => hQB (relIndex_eq_one.mp hh)
    omega
  have hRTi : R.relIndex (T : Subgroup G) = 4 := by
    have hRP : R ≤ (g.P₂ : Subgroup _).map (centralizer ({g.z₂} : Set G)).subtype := by
      rw [g.second_span]
      exact le_sup_left
    have hPT : (g.P₂ : Subgroup _).map (centralizer ({g.z₂} : Set G)).subtype ≤ (T : Subgroup G) := by
      rw [g.second_intersection]
      exact inf_le_left
    have hh := relIndex_mul_relIndex R _ (T : Subgroup G) hRP hPT
    rw [g.second_index,g.second_sylow_index] at hh
    exact hh.symm
  have hATi : A.relIndex (T : Subgroup G) ≤ 8 := by
    have hh := relIndex_mul_relIndex A R (T : Subgroup G) inf_le_left hRT
    have hAR : A.relIndex R ≤ 2 := by simpa only [A,inf_relIndex_left] using hi
    rw [hRTi] at hh
    omega
  have hAQi : A.relIndex (Q : Subgroup G) = A.relIndex (T : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A))
    have h₁ := relIndex_mul_relIndex (⊥ : Subgroup G) A (Q : Subgroup G) bot_le (hAB.trans hBQ)
    have h₂ := relIndex_mul_relIndex (⊥ : Subgroup G) A (T : Subgroup G) bot_le hAT
    rw [relIndex_bot_left,relIndex_bot_left] at h₁ h₂
    rw [h₁,h₂]
    exact Nat.card_congr (Q.equiv T).toEquiv
  have hABi : A.relIndex B ≤ 4 := by
    have hh := relIndex_mul_relIndex A B (Q : Subgroup G) hAB hBQ
    rw [hAQi] at hh
    nlinarith
  have hAZ : A ≤ centralizer ({g.z₂} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (g.second_fixed a ha.1)
  exact ⟨P,hP,(relIndex_le_of_le_left hAZ index_ne_zero_of_finite).trans hABi⟩

end SourceCentralizerGeometry
end CFSG.Quasithin.Chapter2.DoubleA3
