module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearResidualSource
public import Theory.GroupTheory.ElementaryThompsonCoreDisplacement
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Displacement

/-!
# The three-factor obstruction in the original linear amalgam

The original linear join X has J(T) normal, its full quotient is L₃(2),
and its two-core centralizes the actual omega module W. If [O₂(X),K]
lies in W, then every maximum elementary subgroup of T is K-invariant.
The source family inclusion A(O₂(LT)) ⊆ A(T) then makes J(O₂(LT))
K-invariant, contradicting the original unique-normalizer bound and X's
escape from N_G(L).

The second theorem converts the three-factor budget on the original
second-parabolic two-core into precisely this contradiction. It keeps the
actual cubic inside X, both literal cores, W, the simple quotient map,
and the full two-group kernel. The original block's budget, the two module
contributions and the outer contribution remain explicit. This is a
conditional exclusion step, not the trichotomy or source 13.4.7(4).
The source identification K₂=L₂ and its chief counts must still supply
those numerical premises; the residual commutator is not assumed or proved
here. Source: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

private theorem outside_join_not_core_displacement
    {T : Sylow 2 G} {L V X C W : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    [IsElementaryAbelian 2 W]
    (hout : ¬ X ≤ normalizer (L : Set G))
    (hgen : X ≤ C ⊔ (T : Subgroup G))
    (hW : W ≤ T) (hWQ : W ≤ centralizer (X.pCoreIn 2 : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ X.pCoreIn 2)
    (hfamily : elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    ¬ ⁅X.pCoreIn 2,C⁆ ≤ W := by
  intro hmove
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let J := elementaryAbelianMaxJ Q
  have hCJ : C ≤ normalizer (J : Set G) := maxJ_normalized_of_core_displacement
    (T : Subgroup G) (X.pCoreIn 2) W C Q hW hWQ hJ hmove hfamily
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHJ : H ≤ normalizer (J : Set G) := hHQ.trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ Q)
  have hJH : J ≤ H := (sSup_le fun _ hA => hA.1).trans (H.pCoreIn_le 2)
  have hQne : Q ≠ ⊥ := fun he => D.ne_bot (le_bot_iff.mp (D.le_core.trans_eq he))
  have hJne : J ≠ ⊥ := elementaryAbelianMaxJ_ne_bot_of_finite_pGroup
    Q (isPGroup_pCoreIn 2 H) hQne
  have hbound := D.normal_subgroup_normalizer_le h.toHypothesis1221 hJH hJne hHJ
  exact hout ((hgen.trans (sup_le hCJ (le_sup_right.trans hHJ))).trans hbound)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

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


/-- The actual linear pair cannot have both the source maximum-family inclusion
and displacement of its whole two-core into the omega module. -/
theorem original_pair_linear_not_core_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hfamily : elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    ¬ ⁅(A ⊔ B).pCoreIn 2,K.map (A ⊔ B).subtype⁆ ≤
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  obtain ⟨hr,_,_,hk⟩ := original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  let := hr.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hWX).symm.toMonoidHom (subgroupOfEquivOfLe hWX).symm.injective
  have hWQ : W ≤ X.pCoreIn 2 := by
    have hh := map_mono (f := X.subtype) hr.le_pCore
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := hk.symm.le.trans inf_le_left
  have hQW : X.pCoreIn 2 ≤ centralizer (W : Set G) := hk.symm.le.trans inf_le_right
  have hn := original_pair_linear_thompson_normal h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hJQ := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans hTX) hn
  have hgen := (original_pair_linear_core_supplement h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK).2
  apply outside_join_not_core_displacement h D hout
    (hgen.symm.le.trans (sup_le_sup_left hQT C))
    (hWQ.trans hQT) (le_centralizer_iff.mp hQW) hJQ hfamily

/-- On the actual second-parabolic core, a total cubic budget of three,
two omega contributions and one quotient contribution exclude the block family. -/
theorem original_pair_linear_three_factor_budget_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hfamily : elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G))
    (E : Subgroup (A ⊔ B : Subgroup G)) (hE : Nat.card E = 3)
    (hbudget : conjugationCubicLength E ((B.pCoreIn 2).subgroupOf (A ⊔ B)) ≤ 3)
    (homega : 2 ≤ conjugationCubicLength E
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)).subgroupOf (A ⊔ B)))
    (houter : 1 ≤ sectionCubicLength E (pCore 2 (A ⊔ B : Subgroup G))
      ((B.pCoreIn 2).subgroupOf (A ⊔ B))) : False := by
  let X := A ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let U := W.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  obtain ⟨hr,_,_,hk⟩ := original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  let : U.Normal := hr.normal
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := hk.symm.le.trans inf_le_left
  have hQB : X.pCoreIn 2 ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 X) (hQT.trans hTB)
    (le_sup_right.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hQP : pCore 2 X ≤ (B.pCoreIn 2).subgroupOf X := by
    intro x hx
    exact hQB (mem_map_of_mem X.subtype hx)
  obtain ⟨e⟩ := original_pair_linear_full_quotient h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hpker : IsPGroup 2 f.ker := hker ▸ pCore_isPGroup
  have himage : E.map f ≠ ⊥ := by
    have hc := GLS3.Chapter5.cubic_image_card_of_two_kernel f hpker E hE
    intro hz
    rw [hz,card_bot] at hc
    omega
  have hpK : IsPPerfect 2 K := by
    rw [←(original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1]
    exact isPPerfect_pResidual 2
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  have hd := NoncentralChiefRefinement.CubicComparison.perfect_commutator_le_of_length_budget
    f hf hpker E K ((B.pCoreIn 2).subgroupOf X) (pCore 2 X) U
    (IsPGroup.of_card (n := 1) (by simpa using hE)) pCore_isPGroup hpK himage
    hr.le_pCore hQP 2 1 hbudget homega houter
  have hm := map_mono (f := X.subtype) hd
  rw [map_commutator,map_subgroupOf_eq_of_le hWX] at hm
  exact original_pair_linear_not_core_displacement h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hfamily hm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
