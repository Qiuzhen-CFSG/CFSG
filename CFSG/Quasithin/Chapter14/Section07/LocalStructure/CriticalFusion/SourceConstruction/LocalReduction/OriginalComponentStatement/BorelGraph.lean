module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.CenterCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedLinearThree
public import Theory.SpecificGroups.SL3.BorelGraph

/-!
# The graph actor of an original central-cover component

For an actual component with even-degree SL₃ quotient, its scalar center
is the original point cubic. The Sylow normalizer therefore contains L₁.
The original solvable-overgroup theorem places this Borel in N_G(L), and
its literal action-kernel residual supplements L₁. The same inverter fixes
that residual modulo its own two-core. After the scalar cubic is killed,
this fixes the entire projective Borel quotient, including in nonsplit
original two-core extensions.

The two torus axes now force field order four and eliminate the field
factor. Inversion of the scalar center excludes the linear-only case.
The result gives an explicit GL₃-times-inverse-transpose action after a
specified inner conjugation of the original marking, with the inverter
still in the original T∩L. The full point-normalizer application below
uses that same marking and quotient action. Earlier structural premises
remain explicit; no universal record is inferred from guarded local data.

This proves the graph distinction at the start of 14.7.44, not the ensuing
natural-plus-dual module contradiction or the full component theorem.
Source: Aschbacher–Smith 14.7.41,14.7.44, printed pp.1061–1062,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_eq_one_iff)
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
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

/-- The original inverter of every even-degree SL₃ component has an actual
linear-graph factorization after an explicit inner change of the given marking.
The same Borel supplement also forces field order four. -/
theorem local_even_special_linearThree_graph
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n) (heven : Even n)
    (e : (C ⧸ pCore 2 C) ≃* SL(3,E)) :
    n = 2 ∧ ∃ hCN : C.Normal, letI := hCN
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      ∃ (g : SL(3,E)) (m : GL (Fin 3) E),
        MulAut.congr (e.trans (MulAut.conj g))
          (normalQuotientAction C (pCore 2 C)
            ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩) =
          linearConjSL E m * graphSL E := by
  obtain ⟨hin,hAn,hAZ,hCN,t,hi,_⟩ := local_even_special_linearThree_center_and_inverter
    d h hab structural previous faithful earlier I hI C hC hE heven e
  let := hCN
  let := hAn
  let j : C →* G := I.subtype.comp C.subtype
  have hj : Function.Injective j := I.subtype_injective.comp C.subtype_injective
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let q₀ : C →* SL(3,E) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,E) (P.mapSurjective hq₀)
    (unipotentSLSylow E (by omega : 0 < n) hE)
  let e' := e.trans (MulAut.conj g)
  let q : C →* SL(3,E) := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hPq : (P : Subgroup C).map q = unipotentSL E := by
    change (P : Subgroup C).map ((MulAut.conj g).toMonoidHom.comp q₀) = _
    rw [←Subgroup.map_map]
    change ((g • P.mapSurjective hq₀ : Sylow 2 SL(3,E)) : Subgroup SL(3,E)) = _
    rw [hg]
    rfl
  let N : Subgroup C := normalizer (P : Set C)
  let B₀ : Subgroup G := N.map j
  let A : Subgroup C := (F.Li L 1).comap j
  have hAcenter (a : C) (ha : a ∈ A) : q a ∈ center SL(3,E) := by
    let qI := QuotientGroup.mk' (pCore 2 I)
    let Cbar := C.map qI
    let ec := cComponentTwoCoreQuotientEquiv hC
    have hz : qI (a : I) ∈ (center Cbar).map Cbar.subtype :=
      hAZ ▸ mem_map_of_mem qI ha
    obtain ⟨z,hz,he⟩ := hz
    have hec : ec (QuotientGroup.mk' (pCore 2 C) a) = z := Subtype.ext he.symm
    have hc : QuotientGroup.mk' (pCore 2 C) a ∈ center (C ⧸ pCore 2 C) := by
      have hh := (centerCongr ec.symm ⟨z,hz⟩).property
      change ec.symm z ∈ center (C ⧸ pCore 2 C) at hh
      rwa [←hec,ec.symm_apply_apply] at hh
    exact (centerCongr e' ⟨_,hc⟩).property
  have hArange : F.Li L 1 ≤ j.range := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hin
  have hAm : A.map j = F.Li L 1 := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hArange
  have hqk : q.ker ≤ (P : Subgroup C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hAN : A ≤ N := by
    intro a ha
    have hz := hAcenter a ha
    have hc : q a ∈ normalizer ((P : Subgroup C).map q : Set SL(3,E)) :=
      center_le_normalizer _ hz
    have he := comap_normalizer_eq_of_surjective ((P : Subgroup C).map q) hq
    rw [comap_map_eq_self hqk] at he
    change a ∈ (normalizer ((P : Subgroup C).map q : Set SL(3,E))).comap q at hc
    rw [he] at hc
    exact hc
  have hAB : F.Li L 1 ≤ B₀ := hAm ▸ map_mono (f := j) hAN
  have hPpres (t : I) (ht : (t : G) ∈ T) :
      (P : Subgroup C).map (MulAut.conjNormal t).toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP] at hx ⊢
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hx)
        ((T : Subgroup G).inv_mem ht)
    · rw [card_map_of_injective (f := (MulAut.conjNormal t : MulAut C).toMonoidHom)
        (K := (P : Subgroup C)) (MulAut.conjNormal t : MulAut C).injective]
  have hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G) := by
    intro t ht
    let t' : I := ⟨t,F.sylow_le_of_mem_Hz hI ht⟩
    let α : MulAut C := MulAut.conjNormal t'
    have hN : N.map α.toMonoidHom = N := by
      change (normalizer (P : Set C)).map α.toMonoidHom = normalizer (P : Set C)
      have hh := map_normalizer_eq_of_bijective (f := α.toMonoidHom)
        (P : Subgroup C) α.bijective
      rw [show (P : Subgroup C).map α.toMonoidHom = P from hPpres t' ht] at hh
      simpa only [Sylow.coe_coe] using hh
    have he : (MulAut.conj t).toMonoidHom.comp j = j.comp α.toMonoidHom := rfl
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (N.map j).map (MulAut.conj t).toMonoidHom = N.map j
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
  let β : MulAut SL(3,E) := MulAut.congr e' (normalQuotientAction C (pCore 2 C) tI)
  let γ := centerAction E β
  let r := (Matrix.PSL3.projection E).comp q
  have heq (x : C) : β (q x) = q (α x) := by
    change e' (normalQuotientAction C (pCore 2 C) tI
      (e'.symm (e' (QuotientGroup.mk' _ x)))) = _
    rw [e'.symm_apply_apply,normalQuotientAction_apply_mk]
    rfl
  have hr (x : C) : γ (r x) = r (α x) := by
    change centerAction E β (QuotientGroup.mk (q x)) = _
    rw [centerAction_mk,heq]
    rfl
  have hU : (unipotent E).map γ.toMonoidHom = unipotent E := by
    have hrP : (P : Subgroup C).map r = unipotent E := by
      rw [show r = (Matrix.PSL3.projection E).comp q from rfl,←Subgroup.map_map,hPq]
      rfl
    rw [←hrP,Subgroup.map_map,show γ.toMonoidHom.comp r = r.comp α.toMonoidHom
      from MonoidHom.ext hr,←Subgroup.map_map,hPpres tI t.property.1]
  have hBγ : (borel E).map γ.toMonoidHom = borel E := by
    rw [←normalizer_unipotent E (by omega : 0 < n) hE,
      map_equiv_normalizer_eq (unipotent E) γ,hU]
  let γB : MulAut (borel E) := (γ.subgroupMap (borel E)).trans (MulEquiv.subgroupCongr hBγ)
  let τ := (pCore 2 (borel E)).quotientAut γB
  let eb : N ≃* B₀ := equivMapOfInjective N j hj
  have hNq : N.map q = borelSL E := by
    have hh := P.normalizer_map_surjective q hq
    change N.map q = normalizer ((P : Subgroup C).map q : Set SL(3,E)) at hh
    rw [hPq,normalizer_unipotentSL E] at hh
    exact hh
  have hNr : N.map r = borel E := by
    rw [show r = (Matrix.PSL3.projection E).comp q from rfl,←Subgroup.map_map,hNq]
    rfl
  let rB : B₀ →* borel E := (r.comp (N.subtype.comp eb.symm.toMonoidHom)).codRestrict
    (borel E) (fun b => hNr.le (mem_map_of_mem r (eb.symm b).property))
  have hrB : Function.Surjective rB := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hNr.ge y.property
    refine ⟨eb ⟨x,hx⟩,Subtype.ext ?_⟩
    change r (eb.symm (eb ⟨x,hx⟩)) = y
    rw [eb.symm_apply_apply]
    exact hxy
  let f := (QuotientGroup.mk' (pCore 2 (borel E))).comp rB
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hrB
  have heb (b : B₀) : j (eb.symm b) = b := congrArg Subtype.val (eb.apply_symm_apply b)
  have haB (b : B₀) : α (eb.symm b) =
      (eb.symm (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b) : C) := by
    apply hj
    change (t : G) * j (eb.symm b) * (t : G)⁻¹ = _
    rw [heb,heb]
    rfl
  have he (b : B₀) : τ (f b) = f (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b) := by
    change (pCore 2 (borel E)).quotientAut γB (QuotientGroup.mk' _ (rB b)) = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' _ (γB (rB b)) = QuotientGroup.mk' _ (rB _)
    congr 1
    apply Subtype.ext
    change γ (r (eb.symm b)) = r (eb.symm (B₀.normalizerMonoidHom _ b))
    rw [hr,haB]
  have hkill (a : B₀) (ha : (a : G) ∈ F.Li L 1) : f a = 1 := by
    have hz := hAcenter (eb.symm a) (by change j (eb.symm a) ∈ F.Li L 1; rwa [heb])
    have hr0 : r (eb.symm a) = 1 := (QuotientGroup.eq_one_iff _).mpr hz
    have hh : rB a = 1 := Subtype.ext hr0
    change QuotientGroup.mk' _ (rB a) = 1
    rw [hh,map_one]
  have ho : Odd (Nat.card (borel E ⧸ pCore 2 (borel E))) := by
    rw [←index_eq_card]
    exact Matrix.PSL3.CartanActions.FullTorusFixer.borel_twoCore_index_odd hE
  have hτ := odd_borel_image_fixed h structural B₀ hBM hAres hBA f hf ho hkill
    t t.property.2 (hTB t.property.1) τ he
  have hfix : ∀ x ∈ torus E, γ x * x⁻¹ ∈ unipotent E := by
    intro x hx
    let b : borel E := ⟨x,torus_le_borel E hx⟩
    have hh := congrArg (fun a : MulAut (borel E ⧸ pCore 2 (borel E)) =>
      a (QuotientGroup.mk' _ b)) hτ
    change (pCore 2 (borel E)).quotientAut γB (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' _ b at hh
    rw [quotientAut_apply_mk] at hh
    have hk : γB b * b⁻¹ ∈ pCore 2 (borel E) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' _ (_ * _) = 1
      rw [map_mul,map_inv,hh,mul_inv_cancel]
    rw [twoCore_eq E hE] at hk
    exact hk
  have hmove : ¬ ∀ z ∈ center SL(3,E), β z = z := by
    intro hfixed
    have hzero : center SL(3,E) = ⊥ := by
      apply eq_bot_iff.mpr
      intro z hz
      have hi' : β z = z⁻¹ := by
        have hzg : g⁻¹*z*g = z := by
          rw [mem_center_iff.mp hz g⁻¹,mul_assoc,inv_mul_cancel,mul_one]
        change g * ((MulAut.congr e (normalQuotientAction C (pCore 2 C) tI))
          (g⁻¹*z*g)) * g⁻¹ = z⁻¹
        rw [hzg,hi z hz,mem_center_iff.mp ((center _).inv_mem hz) g,mul_inv_cancel_right]
      have hzi : z = z⁻¹ := (hfixed z hz).symm.trans hi'
      have htwo : z^2 = 1 := by
        rw [pow_two]
        exact (congrArg (z * ·) hzi).trans (mul_inv_cancel _)
      have hthree : z^3 = 1 := by
        have hc := Matrix.SL3.card_center_dvd_three E
        exact congrArg Subtype.val (_root_.orderOf_dvd_iff_pow_eq_one.mp
          ((_root_.orderOf_dvd_natCard (⟨z,hz⟩ : center SL(3,E))).trans hc))
      exact mem_bot.mpr (by simpa [pow_succ,htwo] using hthree)
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three E).mp hzero
    apply hh
    rw [hE,Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp heven)]
  obtain ⟨hn2,m,hm⟩ := Matrix.SL3.BorelGraph.graph_of_projective_borel_fixed hE hn β hU hfix hmove
  exact ⟨hn2,hCN,t,g,m,hm⟩

/-- The field-four graph actor at the original full point normalizer, with
its literal component quotient and original T∩L inverter. This is the
original 14.7.44 application of the Borel supplement calculation. -/
theorem original_special_linearThree_four_graph
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 4) (e : (C ⧸ pCore 2 C) ≃* SL(3,E)) :
    ∃ hCN : C.Normal, letI := hCN
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      ∃ (g : SL(3,E)) (m : GL (Fin 3) E),
        MulAut.congr (e.trans (MulAut.conj g))
          (normalQuotientAction C (pCore 2 C)
            ⟨t,F.sylow_le_of_mem_Hz (h.point_mem_Hz_at F (previous.at T)) t.property.1⟩) =
          linearConjSL E m * graphSL E := by
  exact (local_even_special_linearThree_graph d h hab structural previous faithful earlier
    F.H (h.point_mem_Hz_at F (previous.at T)) C hC (n := 2)
    (by simpa using hE) (by decide) (by decide) e).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
