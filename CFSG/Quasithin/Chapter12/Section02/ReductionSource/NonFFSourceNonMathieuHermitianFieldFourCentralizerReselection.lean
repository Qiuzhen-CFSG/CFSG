module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOrdinaryRadical
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.ResidualCoreSelection
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleOverlap
public import Theory.GroupTheory.GeneralizedFitting.ComponentFixedInvolution
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianSectionSylow

/-!
# The unchanged Hermitian component in an involution centralizer

Replace the original pushing-up subgroup by its intersection residual
joined with its unchanged two-core. Choose an involution r in the ambient
two-core that centralizes this replacement and the full ordinary component.
The field-four component sieve applies to the rebuilt witness above C_G(r).
The old and new components contain the same nontrivial perfect residual;
quasisimple overlap and equality of their J₄ central quotients identify them.
Thus the original full component is normal in the full C_G(r).

The actual noncubic odd-actor consumer pairs r with the original T-fixed
module involution z. It retains the escaping full C_K(z) residual, now
normalized by C_G(r) intersect C_G(z), together with an actual section Sylow
whose centralizer of r is exactly the original radical. A recorded
section-centralizer conjugator aligns that Sylow with the original LT core.
No normality in N_G(A), containment of T in H, or trivial covering center
is asserted. Containment of the escaping residual in N_G(L), and the
subsequent 8.2.7--13 contradiction, remain to be proved.
Source: Aschbacher--Smith 4.1.4, 4.2.13 and 4.4.3, printed pp.607,611--612,623,
as used in 8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Reconstruct the ordinary component on any literal field-four witness. -/
theorem sourceOrbit_hermitian_ordinary_component_of_witness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
      W.subgroupOf H ≤ K ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  have hc := hw.2.2.2.2.2.2.1
  obtain ⟨e,he⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let := h.toHypothesis1221.quasisimple
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv e.symm
  let es := (centerQuotientCongr e).trans ((D.orbitCentralQuotientEquiv h.toHypothesis1221).trans eQ)
  obtain ⟨K,hK,hn,hout,hFK,hWK⟩ := field_four_pushingUp_ordinary hc
    hw.2.2.2.2.1 hw.2.2.2.2.2.2.2.2.1 (by rw [B.card_eq,hfield]; decide) es
  exact ⟨K,hK,hn,hout,hFK,hWK,D.sourceOrbit_hermitian_field_four_ordinary_janko
    h hmany hV hnon d B eQ hfield hw K hK⟩

/-- Reselect at an actual core involution, and prove that the unchanged full
component is normal in the new overgroup and in the full involution centralizer. -/
theorem sourceOrbit_hermitian_ordinary_centralizer_reselection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let I := F ⊔ J.pCoreIn 2
    I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
      ∃ (r : G) (H₁ W₁ : Subgroup G),
        r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
        K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
        centralizer ({r} : Set G) ≤ H₁ ∧
        Witness L D.sourceOrbit A I H₁ W₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧ ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
        ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal := by
  have hwV : Witness L V A J H W := by simpa only [hV] using hw
  have hc := hw.2.2.2.2.2.2.1
  have hFK := hc.ordinary_component_contains_original K hK
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huniq : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  obtain ⟨hcore,hpush,r,H₁,W₁,hr,hRr,hr2,hCr,hCH,hKH,hw₁V⟩ :=
    selected_involution_witness h.toHypothesis1221 D huniq hwV K hK hFK hout
  have hw₁ : Witness L D.sourceOrbit A
      (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) ⊔ J.pCoreIn 2) H₁ W₁ := by
    simpa only [hV] using hw₁V
  obtain ⟨e⟩ := D.sourceOrbit_hermitian_field_four_ordinary_janko h hmany hV hnon d B eQ hfield hw K hK
  obtain ⟨K₁,hK₁,hn₁,_,hF₁K₁,_,⟨e₁⟩⟩ :=
    D.sourceOrbit_hermitian_ordinary_component_of_witness h hmany hV hnon d B eQ hfield hw₁
  let Kg := K.map H.subtype
  let Kb := Kg.subgroupOf H₁
  let eb : Kb ≃* K := (subgroupOfEquivOfLe hKH).trans
    (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let := hK.2
  let := hK₁.2
  let := hn₁
  let : IsQuasisimple Kb := IsQuasisimple.of_mulEquiv eb.symm
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFKg : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hFH₁ : F ≤ H₁ := hFKg.trans hKH
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let Fb := F.subgroupOf H₁
  let : Group.IsPerfect Fb := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFH₁).symm.toMonoidHom) (subgroupOfEquivOfLe hFH₁).symm.surjective
  have hneF : F ≠ ⊥ := fun he => (hV ▸ D.ne_bot)
    (bot_unique (he ▸ hw.2.2.2.2.2.2.2.2.2.2.1))
  have hneFb : Fb ≠ ⊥ := by
    intro he
    have hh := congrArg (map H₁.subtype) he
    exact hneF (by simpa only [Fb,map_subgroupOf_eq_of_le hFH₁,Subgroup.map_bot] using hh)
  have hFK₁ : Fb ≤ K₁ := by
    have hF₁ := le_map_solvableResidual_of_isPerfect F (L ⊓ H₁) (le_inf hFL hFH₁)
    intro x hx
    exact hF₁K₁ (hF₁ hx)
  have hKbK₁ : Kb ≤ K₁ := quasisimple_le_normal_of_nonabelian_overlap Kb K₁ Fb
    (subgroupOf_mono H₁ hFKg) hFK₁ (by rwa [commutator_eq_self])
  let X := Kb.subgroupOf K₁
  let ex : X ≃* K := (subgroupOfEquivOfLe hKbK₁).trans eb
  let : IsQuasisimple X := IsQuasisimple.of_mulEquiv ex.symm
  have hX : X = ⊤ := quasisimple_subgroup_eq_top_of_central_quotient_card X (by
    rw [Nat.card_congr ((centerQuotientCongr ex).trans e).toEquiv,
      Nat.card_congr e₁.toEquiv])
  have hKb : Kb = K₁ := le_antisymm hKbK₁ (subgroupOf_eq_top.mp hX)
  have hrel : IsComponentIn Kg H₁ := ⟨hKH,by change IsComponent H₁ Kb; rw [hKb]; exact hK₁⟩
  have hn : (Kg.subgroupOf H₁).Normal := by change Kb.Normal; rw [hKb]; exact hn₁
  have hKr : Kg ≤ centralizer ({r} : Set G) := le_sup_left.trans hCr
  have hnC : (Kg.subgroupOf (centralizer ({r} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKr).mpr
      (hCH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  exact ⟨hcore,hpush,r,H₁,W₁,hr,hRr,hr2,hCr,hCH,hw₁,hrel,hn,hrel.restrict hKr hCH,hnC⟩

/-- The actual escaping noncubic actor supplies the paired involutions in
one full covering component. The simultaneous centralizer normalizes the
same escaping residual; the core involution has the exact aligned Sylow kernel. -/
theorem sourceOrbit_hermitian_oddActor_paired_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J H W : Subgroup G, Witness L D.sourceOrbit A J H W ∧
      ∃ K : Subgroup H, IsComponent H K ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ∃ (r : G) (z : K),
          r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
          ((z : H) : G) ∈ D.sourceOrbit ∧ orderOf z = 2 ∧
          (T : Subgroup G) ≤ centralizer ({((z : H) : G)} : Set G) ∧
          K.map H.subtype ≤ centralizer ({r} : Set G) ∧
          J.pCoreIn 2 ≤ centralizer ({r} : Set G) ⊓ centralizer ({((z : H) : G)} : Set G) ∧
          IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
          ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal ∧
          let S := ((solvableResidual (centralizer ({z} : Set K))).map
            (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype)
          ¬ S ≤ normalizer (L : Set G) ∧
          centralizer ({r} : Set G) ⊓ centralizer ({((z : H) : G)} : Set G) ≤ normalizer (S : Set G) ∧
          ∃ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
            let Pg := (P : Subgroup _).map
              (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
            J.pCoreIn 2 ≤ Pg ∧ Pg ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 ∧
            ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
              ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom = Pg ∧
              (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2 = Pg ∧
              D.sourceOrbit.map (MulAut.conj (c : G)).toMonoidHom ≤
                Chapter4.Section02.Unitary.fullModule L Pg := by
  obtain ⟨J,H,W,hw,K,hK,_,houtK,_,_,he⟩ :=
    D.sourceOrbit_hermitian_field_four_oddActor_pushingUp
      h hmany hV hnon d B eQ hfield hp hgt A hne hAe hA hout
  obtain ⟨hcore,_,r,H₁,W₁,hr,hRr,hr2,hCr,hCH,hw₁,_,_,hKCr,hnCr⟩ :=
    D.sourceOrbit_hermitian_ordinary_centralizer_reselection
      h hmany hV hnon d B eQ hfield hw K hK houtK
  obtain ⟨z,hzV,hz,hTz,hRz,hescape⟩ :=
    D.sourceOrbit_hermitian_ordinary_radical_fixed_residual_escape
      h hmany hV hnon d B eQ hfield hw K hK
  have hw₁V : Witness L V A
      (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) ⊔ J.pCoreIn 2) H₁ W₁ := by
    simpa only [hV] using hw₁
  obtain ⟨P,hRP,_,hPC,c,hc,hcT,hVc⟩ := D.sourceOrbit_hermitian_involution_section_sylow
    h.toHypothesis1221 hw₁V r (hcore.le.trans (le_sup_right.trans hCr)) hCH
  rw [hcore] at hRP hPC
  have hKr : K.map H.subtype ≤ centralizer ({r} : Set G) := le_sup_left.trans hCr
  refine ⟨J,H,W,hw,K,hK,he,r,z,hr,hRr,hr2,hzV,hz,hTz,hKr,
    le_inf (le_sup_right.trans hCr) hRz,hKCr,hnCr,hescape,?_,P,hRP,hPC,c,hc,hcT,?_⟩
  · let f := H.subtype.comp K.subtype
    have hh := centralizer_residual_image_normalized f
      (H.subtype_injective.comp K.subtype_injective) z
    have hfr : f.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
    rw [hfr,←map_map] at hh
    exact (inf_le_inf_right _ ((normal_subgroupOf_iff_le_normalizer hKr).mp hnCr)).trans hh
  · simpa only [hV] using hVc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
