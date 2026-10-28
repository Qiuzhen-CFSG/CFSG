module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.CenterCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveExceptions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideUnitaryThree
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Quotients
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.SpecialLinearExclusion
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Excluding the unitary central covers at the original local component

A nontrivial component center is the original point cubic. Hence the
actual Sylow normalizer contains L₁ and is normalized by L₁T. The original
solvable-overgroup theorem places it in N_G(L). Its action-kernel residual
supplements L₁, and the original T∩L inverter fixes that residual modulo
its own two-core. Killing the central cubic therefore makes the inverter
fix the entire projective Borel quotient.

For a central quotient PSU₃(2ⁿ), n ≥ 2, the native Borel calculation puts
this projective actor in the inner image of the actual root subgroup.
Perfectness lifts innerness through the component center, contradicting
its inversion by the same original inverter. All maps come from the
intrinsic C/O₂(C), its center, and the specified original Sylow; no
splitting or chosen module is used.

The special-unitary application retains its actual scalar kernel.
Together with the proved SL₃ exclusion, the A.3.6 congruence eliminates
both signed special-three rows of the original F.9.18 catalogue. The
last theorem applies this to the original full point normalizer. Earlier
structural inputs remain explicit; this does not construct universal
records from guarded inputs. The outside-component module argument,
triple-A₆ cover, binary L₃(2) case and final source assembly remain.

Source: Aschbacher–Smith 14.7.41 and 14.7.44, printed pp.1061–1062,
with 14.7.27–29 and the full Borel supplement, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_eq_one_iff)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem odd_borel_image_fixed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (B₀ : Subgroup G) (hBM : B₀ ≤ normalizer (L : Set G))
    (hAB : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype)
    (hBA : B₀ ≤ normalizer (F.Li L 1 : Set G))
    {E : Type*} [Group E] [Finite E] (f : B₀ →* E)
    (hf : Function.Surjective f) (ho : Odd (Nat.card E))
    (hkill : ∀ a : B₀, (a : G) ∈ F.Li L 1 → f a = 1)
    (t : G) (htL : t ∈ L) (htB : t ∈ normalizer (B₀ : Set G))
    (α : MulAut E) (heq : ∀ b : B₀, α (f b) = f (B₀.normalizerMonoidHom ⟨t,htB⟩ b)) :
    α = 1 := by
  let B := (pResidual 2 B₀).map B₀.subtype
  have hBB : B ≤ B₀ := map_subtype_le _
  have hB := hBB.trans hBM
  let D := binaryBorelCentralResidual L B hB
  have hDB : D ≤ B₀ := (map_subtype_le _).trans hBB
  have hgen := point_borel_kernel_supplement h structural B hB
    (isPPerfect_embedded_pResidual 2 B₀) hAB (hBB.trans hBA)
  have htB' : t ∈ normalizer (B : Set G) :=
    normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀) htB
  let htD := binaryBorelCentralResidual_normalized L B hB ⟨htB',L.le_normalizer htL⟩
  let fD : D →* E := f.comp (inclusion hDB)
  have hk : pCore 2 D ≤ fD.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply card_eq_one.mp
    exact (pCore_isPGroup.map fD).card_eq_or_dvd.resolve_right (fun hd =>
      ho.not_two_dvd_nat (hd.trans (pCore 2 D |>.map fD).card_subgroup_dvd_card))
  have hDfix : ∀ b : B₀, (b : G) ∈ D → α (f b) = f b := by
    intro b hb
    let x : D := ⟨b,hb⟩
    have hh := (coreAction_eq_one_iff _ _).mp
      (binaryBorelCentralResidual_fixed L B hB htL htB') x
    have hk' := hk hh
    change fD (D.normalizerMonoidHom ⟨t,htD⟩ x * x⁻¹) = 1 at hk'
    rw [map_mul,map_inv,mul_inv_eq_one] at hk'
    exact (heq b).trans hk'
  let K := (α.toMonoidHom.comp f).eqLocus f
  have hBK : B.subgroupOf B₀ ≤ K := by
    have hh : (F.Li L 1).subgroupOf B₀ ⊔ D.subgroupOf B₀ = B.subgroupOf B₀ := by
      apply map_injective B₀.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (hAB.trans hBB),
        map_subgroupOf_eq_of_le hDB,map_subgroupOf_eq_of_le hBB]
      exact hgen
    rw [←hh]
    apply sup_le
    · intro a ha
      change α (f a) = f a
      rw [hkill a ha,map_one]
    · exact hDfix
  apply MulEquiv.ext
  intro z
  obtain ⟨b,rfl⟩ := SourceActions.Markings.residual_surjective B₀ f hf ho z
  exact hBK b.property

/-- A nontrivial central cover of a binary PSU₃ component is impossible. -/
theorem local_unitaryThree_central_cover_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hz : center (C ⧸ pCore 2 C) ≠ ⊥)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : ((C ⧸ pCore 2 C) ⧸ center (C ⧸ pCore 2 C)) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  obtain ⟨hin,hAn,hAZ,_⟩ := local_nontrivial_component_center_at
    d h hab (structural.at T) (previous.at T) faithful earlier I hI C hC hz
  obtain ⟨hCN,t,_,hout⟩ := local_nontrivial_component_center_inverter
    d h hab structural previous faithful earlier I hI C hC hz
  let := hCN
  let := hAn
  let : IsQuasisimple (C ⧸ pCore 2 C) :=
    local_component_twoCore_isQuasisimple h hab structural previous faithful I hI C hC
  let j : C →* G := I.subtype.comp C.subtype
  have hj : Function.Injective j := I.subtype_injective.comp C.subtype_injective
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let π := QuotientGroup.mk' (pCore 2 C)
  let z := QuotientGroup.mk' (center (C ⧸ pCore 2 C))
  let r₀ := e.toMonoidHom.comp (z.comp π)
  have hr₀ : Function.Surjective r₀ := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective _ hr₀
  obtain ⟨m,hmP,hmN⟩ := psu_borel_model J n (by omega) hE hconj (P.mapSurjective hr₀)
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  have hJ₀ : J₀.form = !![0,0,1;0,1,0;1,0,0] := rfl
  let : Group (ProjectiveSpecialUnitaryMatrixGroup J₀) := inferInstance
  let : DivisionMonoid (ProjectiveSpecialUnitaryMatrixGroup J₀) := Group.toDivisionMonoid
  let : Group (projectiveBorel J₀ hJ₀) := inferInstance
  let : DivisionMonoid (projectiveBorel J₀ hJ₀) := Group.toDivisionMonoid
  let : Group (projectiveBorel J₀ hJ₀ ⧸ pCore 2 (projectiveBorel J₀ hJ₀)) :=
    QuotientGroup.Quotient.group _
  let : DivisionMonoid (projectiveBorel J₀ hJ₀ ⧸ pCore 2 (projectiveBorel J₀ hJ₀)) :=
    Group.toDivisionMonoid
  let e' := e.trans m
  let r := e'.toMonoidHom.comp (z.comp π)
  have hr : Function.Surjective r := e'.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) := Finite.of_surjective _ hr
  have hPr : (P : Subgroup C).map r = projectiveRoot J₀ hJ₀ := by
    change (P : Subgroup C).map (m.toMonoidHom.comp r₀) = _
    rw [←Subgroup.map_map]
    exact hmP
  let N : Subgroup C := normalizer (P : Set C)
  have hNr : N.map r = projectiveBorel J₀ hJ₀ := by
    change N.map (m.toMonoidHom.comp r₀) = _
    rw [←Subgroup.map_map,P.normalizer_map_surjective r₀ hr₀]
    exact hmN
  let B₀ : Subgroup G := N.map j
  let A : Subgroup C := (F.Li L 1).comap j
  have hAcenter (a : C) (ha : a ∈ A) : π a ∈ center (C ⧸ pCore 2 C) := by
    let qI := QuotientGroup.mk' (pCore 2 I)
    let Cbar := C.map qI
    let ec := cComponentTwoCoreQuotientEquiv hC
    have hz' : qI (a : I) ∈ (center Cbar).map Cbar.subtype :=
      hAZ ▸ mem_map_of_mem qI ha
    obtain ⟨b,hb,he⟩ := hz'
    have hec : ec (π a) = b := Subtype.ext he.symm
    have hh := (centerCongr ec.symm ⟨b,hb⟩).property
    change ec.symm b ∈ center (C ⧸ pCore 2 C) at hh
    rwa [←hec,ec.symm_apply_apply] at hh
  have hArange : F.Li L 1 ≤ j.range := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hin
  have hAm : A.map j = F.Li L 1 := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hArange
  have hπk : π.ker ≤ (P : Subgroup C) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hAN : A ≤ N := by
    intro a ha
    have hc : π a ∈ normalizer ((P : Subgroup C).map π : Set (C ⧸ pCore 2 C)) :=
      center_le_normalizer _ (hAcenter a ha)
    have he := comap_normalizer_eq_of_surjective ((P : Subgroup C).map π)
      (QuotientGroup.mk'_surjective (pCore 2 C))
    rw [comap_map_eq_self hπk] at he
    change a ∈ (normalizer ((P : Subgroup C).map π : Set (C ⧸ pCore 2 C))).comap π at hc
    rw [he] at hc
    exact hc
  have hAB : F.Li L 1 ≤ B₀ := hAm ▸ map_mono (f := j) hAN
  have hPpres (x : I) (hx : (x : G) ∈ T) :
      (P : Subgroup C).map (MulAut.conjNormal x).toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨c,hc,rfl⟩
      rw [hP] at hc ⊢
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hx hc)
        ((T : Subgroup G).inv_mem hx)
    · rw [card_map_of_injective (f := (MulAut.conjNormal x : MulAut C).toMonoidHom)
        (K := (P : Subgroup C)) (MulAut.conjNormal x : MulAut C).injective]
  have hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G) := by
    intro x hx
    let x' : I := ⟨x,F.sylow_le_of_mem_Hz hI hx⟩
    let α : MulAut C := MulAut.conjNormal x'
    have hN : N.map α.toMonoidHom = N := by
      change (normalizer (P : Set C)).map α.toMonoidHom = normalizer (P : Set C)
      have hh := map_normalizer_eq_of_bijective (f := α.toMonoidHom)
        (P : Subgroup C) α.bijective
      rw [show (P : Subgroup C).map α.toMonoidHom = P from hPpres x' hx] at hh
      simpa only [Sylow.coe_coe] using hh
    have he : (MulAut.conj x).toMonoidHom.comp j = j.comp α.toMonoidHom := rfl
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (N.map j).map (MulAut.conj x).toMonoidHom = N.map j
    rw [Subgroup.map_map,he,←Subgroup.map_map,hN]
  have hnB : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B₀ : Set G) :=
    sup_le (hAB.trans B₀.le_normalizer) hTB
  have hBH : B₀ ≤ F.H :=
    (map_mono (show N ≤ ⊤ from le_top)).trans (by
      rw [←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
      exact (map_subtype_le _).trans hI.2.1)
  let : Group.IsSolvable N := P.normalizer_isSolvable_two
  have hsol : Group.IsSolvable B₀ :=
    Group.isSolvable_of_surjective (j.subgroupMap_surjective N)
  have hBM := point_normalized_solvable_le_normalizer d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hBA := point_normalized_solvable_normalizes_point d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hAres : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype := by
    have hh := embedded_pResidual_mono 2 hAB
    have hpA : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
    rw [(pResidual_eq_top_iff 2 _).mpr hpA,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let α : MulAut C := MulAut.conjNormal tI
  let act := (MulAut.centralQuotientAction e').comp (normalQuotientAction C (pCore 2 C))
  let γ := act tI
  have hact (x : C) : γ (r x) = r (α x) := by
    change MulAut.centralQuotientAction e' (normalQuotientAction C (pCore 2 C) tI)
      (e' (z (π x))) = _
    rw [MulAut.centralQuotientAction_apply,normalQuotientAction_apply_mk]
    rfl
  have hroot : (projectiveRoot J₀ hJ₀).map γ.toMonoidHom = projectiveRoot J₀ hJ₀ := by
    rw [←hPr,Subgroup.map_map,show γ.toMonoidHom.comp r = r.comp α.toMonoidHom
      from MonoidHom.ext hact,←Subgroup.map_map,hPpres tI t.property.1]
  have hborel : (projectiveBorel J₀ hJ₀).map γ.toMonoidHom = projectiveBorel J₀ hJ₀ := by
    obtain ⟨R,hR,hN⟩ := projective_standard_sylow J₀ n (by omega) hE hconj hJ₀
    have hnr : normalizer (projectiveRoot J₀ hJ₀ : Set _) = projectiveBorel J₀ hJ₀ :=
      hR ▸ hN
    rw [←hnr,map_equiv_normalizer_eq,hroot]
  let γB : MulAut (projectiveBorel J₀ hJ₀) :=
    (γ.subgroupMap _).trans (MulEquiv.subgroupCongr hborel)
  let τ := (pCore 2 (projectiveBorel J₀ hJ₀)).quotientAut γB
  let eb : N ≃* B₀ := equivMapOfInjective N j hj
  let rB : B₀ →* projectiveBorel J₀ hJ₀ :=
    (r.comp (N.subtype.comp eb.symm.toMonoidHom)).codRestrict _
      (fun b => hNr.le (mem_map_of_mem r (eb.symm b).property))
  have hrB : Function.Surjective rB := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hNr.ge y.property
    refine ⟨eb ⟨x,hx⟩,Subtype.ext ?_⟩
    change r (eb.symm (eb ⟨x,hx⟩)) = y
    rw [eb.symm_apply_apply]
    exact hxy
  let f := (QuotientGroup.mk' (pCore 2 (projectiveBorel J₀ hJ₀))).comp rB
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hrB
  have heb (b : B₀) : j (eb.symm b) = b := congrArg Subtype.val (eb.apply_symm_apply b)
  have haB (b : B₀) : α (eb.symm b) =
      (eb.symm (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b) : C) := by
    apply hj
    change (t : G) * j (eb.symm b) * (t : G)⁻¹ = _
    rw [heb,heb]
    rfl
  have he (b : B₀) : τ (f b) = f (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b) := by
    change (pCore 2 (projectiveBorel J₀ hJ₀)).quotientAut γB (QuotientGroup.mk' _ (rB b)) = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' _ (γB (rB b)) = QuotientGroup.mk' _ (rB _)
    congr 1
    apply Subtype.ext
    change γ (r (eb.symm b)) = r (eb.symm (B₀.normalizerMonoidHom _ b))
    rw [hact,haB]
  have hkill (a : B₀) (ha : (a : G) ∈ F.Li L 1) : f a = 1 := by
    have hza := hAcenter (eb.symm a) (by change j (eb.symm a) ∈ F.Li L 1; rwa [heb])
    have hr0 : r (eb.symm a) = 1 := by
      change e' (z (π (eb.symm a))) = 1
      have hz0 : z (π (eb.symm a)) = 1 := (QuotientGroup.eq_one_iff _).mpr hza
      rw [hz0,map_one]
    have hh : rB a = 1 := Subtype.ext hr0
    change QuotientGroup.mk' _ (rB a) = 1
    rw [hh,map_one]
  have ho : Odd (Nat.card (projectiveBorel J₀ hJ₀ ⧸ pCore 2 (projectiveBorel J₀ hJ₀))) := by
    rw [Nat.card_congr (projectiveBorelQuotientEquiv J₀ n (by omega) hE hconj hJ₀).toEquiv]
    apply Odd.of_dvd_nat ?_ (card_quotient_dvd_card _)
    rw [Nat.card_units]
    rw [←ChapterF.Source.Unitary.suTorus_card J₀ hJ₀]
    exact ChapterF.Source.Unitary.suTorus_odd J₀ hJ₀ n (by omega) hE
  have hτ := odd_borel_image_fixed h structural B₀ hBM hAres hBA f hf ho hkill
    t t.property.2 (hTB t.property.1) τ he
  have hfix : ∀ x ∈ projectiveBorel J₀ hJ₀, γ x * x⁻¹ ∈ projectiveRoot J₀ hJ₀ := by
    intro x hx
    let b : projectiveBorel J₀ hJ₀ := ⟨x,hx⟩
    have hh := congrArg (fun a : MulAut (projectiveBorel J₀ hJ₀ ⧸ pCore 2 (projectiveBorel J₀ hJ₀)) =>
      a (QuotientGroup.mk' _ b)) hτ
    change (pCore 2 (projectiveBorel J₀ hJ₀)).quotientAut γB (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' _ b at hh
    rw [quotientAut_apply_mk] at hh
    have hk : γB b * b⁻¹ ∈ pCore 2 (projectiveBorel J₀ hJ₀) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' _ (_ * _) = 1
      rw [map_mul,map_inv,hh,mul_inv_cancel]
    have him := mem_map_of_mem (projectiveBorel J₀ hJ₀).subtype hk
    change γ x * x⁻¹ ∈ (projectiveBorel J₀ hJ₀).pCoreIn 2 at him
    rw [projectiveBorel_twoCore J₀ n (by omega) hE hconj hJ₀] at him
    exact him
  let D := (S : Subgroup I).map act
  have hD : IsPGroup 2 D := S.isPGroup'.map act
  have hRD : (projectiveRoot J₀ hJ₀).map MulAut.conj ≤ D := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←hPr] at hx
    obtain ⟨c,hc,rfl⟩ := hx
    have hcS : (c : I) ∈ S := by rw [hP] at hc; exact hc
    have hec : act (c : I) = MulAut.conj (r c) := by
      change MulAut.centralQuotientAction e' (normalQuotientAction C (pCore 2 C) (c : I)) = _
      rw [normalQuotientAction_inner,MulAut.centralQuotientAction_conj]
      rfl
    exact hec ▸ mem_map_of_mem act hcS
  have hγ : γ ∈ D := mem_map_of_mem act t.property.1
  obtain ⟨x,_,hx⟩ := fixed_standard_borel_actor_mem_root_inner J₀ hJ₀ hn hE hconj
    D hD hRD γ hγ hroot hfix
  obtain ⟨c,hc⟩ := (MulAut.centralQuotientAction_inner_iff e'
    (normalQuotientAction C (pCore 2 C) tI)).mp ⟨x,hx.symm⟩
  exact hout ⟨c,hc.symm⟩

/-- The odd-degree full unitary row is excluded with its actual scalar kernel. -/
theorem local_odd_special_unitaryThree_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n)) (hodd : Odd n)
    (e : (C ⧸ pCore 2 C) ≃* J.specialSubgroup) : False := by
  by_cases hz : center (C ⧸ pCore 2 C) = ⊥
  · have hzJ : center J.specialSubgroup = ⊥ := by
      apply card_eq_one.mp
      rw [←Nat.card_congr (centerCongr e).toEquiv,hz]
      exact Nat.card_unique
    exact local_odd_unitaryThree_component_impossible d h hab structural previous faithful
      earlier I hI C hC J hn hE hconj hodd
      (e.trans (J.specialProjectiveEquivOfCenterEqBot hzJ))
  · have hk := J.specialToProjective_ker_eq_center
      (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hE hconj)
    let ec := SourceModels.centralQuotientEquiv e
    let ep := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
    exact local_unitaryThree_central_cover_impossible d h hab structural previous faithful
      earlier I hI C hC hz J hn hE hconj (ec.trans ep)

/-- Neither signed special-three row of the genuine local catalogue survives.
The congruence retained by A.3.6 gives even linear degree or odd unitary degree;
both contradictions preserve the original component and its two-core quotient. -/
theorem local_special_three_catalogue_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (unitary : Bool) (n : ℕ) (hn : Models.ThreeParameter unitary n)
    (hm : (2^n)%3 = if unitary then 2 else 1)
    (he : Chapter1.Section02.LocalModels.IsSLSign (C ⧸ pCore 2 C) unitary 3 (2^n)) :
    False := by
  cases unitary with
  | false =>
    change (2^n)%3 = 1 at hm
    have hn1 : 1 ≤ n := hn
    have heven : Even n := by
      rw [Nat.BinaryTorusParity.two_pow_mod_three] at hm
      split_ifs at hm with he
      · exact Nat.even_iff.mpr he
      · norm_num at hm
    have hn2 : 1 < n := by
      have he := Nat.even_iff.mp heven
      omega
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := he
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hE)
    exact local_even_special_linearThree_component_impossible d h hab structural previous
      faithful earlier I hI C hC hE hn2 heven e
  | true =>
    change (2^n)%3 = 2 at hm
    have hn2 : 2 ≤ n := hn
    have hodd : Odd n := by
      rw [Nat.BinaryTorusParity.two_pow_mod_three] at hm
      split_ifs at hm with he
      · norm_num at hm
      · exact Nat.not_even_iff_odd.mp (fun hn => he (Nat.even_iff.mp hn))
    obtain ⟨E,_,_,J,hE,hconj,⟨e⟩⟩ := he
    exact local_odd_special_unitaryThree_component_impossible d h hab structural previous
      faithful earlier I hI C hC J hn2 hE hconj hodd e

/-- The special-three catalogue rows are impossible at the original full point
normalizer as well, with the same actual component quotient markings. -/
theorem original_special_three_catalogue_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (unitary : Bool) (n : ℕ) (hn : Models.ThreeParameter unitary n)
    (hm : (2^n)%3 = if unitary then 2 else 1)
    (he : Chapter1.Section02.LocalModels.IsSLSign (C ⧸ pCore 2 C) unitary 3 (2^n)) :
    False := by
  exact local_special_three_catalogue_impossible d h hab structural previous faithful
    earlier F.H (h.point_mem_Hz F previous) C hC unitary n hn hm he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
