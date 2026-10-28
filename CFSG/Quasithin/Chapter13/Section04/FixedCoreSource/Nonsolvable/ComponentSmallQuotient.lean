module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentGeneration
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Minimality of the moved module in the three alternating quotient rows

For K/O₂(K) of order 60, 360 or 1080, the literal reduced-action image
has order dividing that same quotient order: O₂(K) centralizes R₂(KT).
The complete B.5 classification therefore cannot have a doubled SL₃(F)
row or an SL₄(2)/SL₅(2) row. This proves Irr⁺ on [R₂(KT),K], with no
assumption on its fixed space. Sylow invariance gives a ChosenModule.

The actual moved omega-orbit is nonzero, K-invariant and fully generated
by its K-commutators. Minimality now identifies it with [R₂(KT),K] and
constructs ChosenModule on that very subgroup. The quotient order premise
is precisely the A₅, A₆ or covered-A₆ case of earlier 13.3.2; it does not
assert the needed minimality or a module marking.

The doubled L₃(2) case still requires the source's L₁-containment, Baumann
and chief-factor exclusions. The A₅/covered-A₆ exclusions, remaining
markings and 13.4.10–17 assembly stay with qt-d-1341-nonsolvable-source.
The genuine earlier 12.2/13.3 inputs retain final discharge with
qt-d-1341-fixed-core-source. Both escaping weights still require their
own nonsolvability input in final assembly.

Source: Aschbacher–Smith B.5.1(1), and the initial module analysis in
13.4.10(4), printed pp.99,907–909. The literal quotient and chosen-module
transports follow the existing OriginalUnitaryNoncentrality/ContainingModule
construction, specialized here by the three source quotient orders.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open ChapterA.Section04 Section03.Noncentrality ChapterB.SourceInduction
open Chapter12.Section02 ChapterB.QuasisimpleSource Section03.SourceCompletion
open Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K V : Subgroup G}

private theorem small_component_quasisimple_row
    (T : Sylow 2 G) (B A : Subgroup G)
    (hAB : A ≤ B) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hJ : IsSQTK KnownSimple.IsKnownSimple (Diagonal.localGroup B A T))
    (hK : (B.subgroupOf (Diagonal.localGroup B A T)).IsCComponent)
    (hqK : IsQuasisimple (B ⧸ pCore 2 B))
    (hfaith : intrinsicSignalizerModule B ≠ ⊥)
    (hgen : ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B) :
    let J := Diagonal.localGroup B A T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    let B₀ := ((B.subgroupOf J).map q).subgroupOf N
    generalizedFitting N = B₀ ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp N.subtype) B₀) := by
  let J := Diagonal.localGroup B A T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  let B₀ := Bq.subgroupOf N
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAB.trans B.le_normalizer)) hTB
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  let : Bq.Normal := (inferInstance : BJ.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B₀.Normal := inferInstance
  have hsup : BJ ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hTJ,
      ←MonoidHom.range_eq_map,range_subtype]
    change B ⊔ (T : Subgroup G) = (B ⊔ A) ⊔ (T : Subgroup G)
    rw [sup_eq_left.mpr hAB]
  have hquot : IsPGroup 2 ((J ⧸ C) ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq (((T : Subgroup G).subgroupOf J).map q)
      (T.isPGroup'.comap_subtype.map q) (by
        rw [←Subgroup.map_sup,hsup,map_top_of_surjective q (QuotientGroup.mk'_surjective C)])
  have hqN : IsPGroup 2 (N ⧸ B₀) := isPGroup_quotient_subgroupOf Bq N hquot
  obtain ⟨_,hcomp,hrows⟩ :=
    component_join_offender_entry T J B hJ hBJ hJN hK hqK hfaith hTJ hgen
  let : IsQuasisimple B₀ := hcomp.2
  have hcore : pCore 2 N = ⊥ := offenderSubgroup_twoCore ρ
    (isPReduced_reducedPSubgroup (p := 2) (G := J)).quotient_pCore_eq_bot
  exact ⟨generalizedFitting_eq_of_quasisimple_two_quotient B₀ hqN hcore,
    quasisimple_row_of_component_two_quotient (ρ.comp N.subtype) B₀ hcomp hqN hcore hrows⟩

omit [Finite G] in
private theorem reduced_component_card_dvd
    (J B : Subgroup G) (hBJ : B ≤ J) (hJN : J ≤ normalizer (B : Set G)) :
    let W := reducedTwoSubgroup J
    let C := centralizer (W : Set J)
    Nat.card ((B.subgroupOf J).map (QuotientGroup.mk' C)) ∣
      Nat.card (B ⧸ pCore 2 B) := by
  let W := reducedTwoSubgroup J
  let C := centralizer (W : Set J)
  let BJ := B.subgroupOf J
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  let q := QuotientGroup.mk' C
  let f := q.subgroupMap BJ
  have hcore : pCore 2 BJ ≤ f.ker := by
    have hpc : (pCore 2 BJ).map BJ.subtype ≤ pCore 2 J :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map BJ.subtype⟩
    have hc := hpc.trans (le_centralizer_iff.mp
      (isPReduced_reducedPSubgroup (p := 2) (G := J)).le_centralizer_pCore)
    intro b hb
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := C) (b : J)).mpr
      (hc (mem_map_of_mem BJ.subtype hb))
  let g := QuotientGroup.lift (pCore 2 BJ) f hcore
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b,rfl⟩ := q.subgroupMap_surjective BJ y
    exact ⟨QuotientGroup.mk' (pCore 2 BJ) b,rfl⟩
  have hd := card_dvd_of_surjective g hg
  let e := subgroupOfEquivOfLe hBJ
  have he := Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv
  exact he ▸ hd

private theorem small_card_excludes_linear_three (F : BinaryField) {n : ℕ}
    (hn : n = 60 ∨ n = 360 ∨ n = 1080) :
    ¬ Nat.card SL(3,F.Carrier) ∣ n := by
  intro hd
  have hnpos : 0 < n := by rcases hn with rfl | rfl | rfl <;> decide
  have hnle : n ≤ 1080 := by rcases hn with rfl | rfl | rfl <;> decide
  have hb := (Nat.le_of_dvd hnpos hd).trans hnle
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear] at hb hd
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  have he : Nat.card F.Carrier = 2 := by
    by_contra he
    have hq3 : 3 ≤ Nat.card F.Carrier := by omega
    have hb' : 5616 ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
        (Nat.card F.Carrier ^ 2 - 1) := by
      calc
        5616 = 3^3 * (3^3-1) * (3^2-1) := by norm_num
        _ ≤ _ := by gcongr
    omega
  rw [he] at hd
  rcases hn with rfl | rfl | rfl <;> norm_num at hd

private theorem binary_linear_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem small_card_excludes_binary_higher {d n : ℕ}
    (hd : d = 4 ∨ d = 5) (hn : n = 60 ∨ n = 360 ∨ n = 1080) :
    ¬ Nat.card SL(d,ZMod 2) ∣ n := by
  rw [binary_linear_card]
  rcases hd with rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
    norm_num [Fin.prod_univ_succ]

private theorem small_moved_module_chosen
    (T : Sylow 2 G) (B A : Subgroup G)
    (hAB : A ≤ B) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hJ : IsSQTK KnownSimple.IsKnownSimple (Diagonal.localGroup B A T))
    (hK : (B.subgroupOf (Diagonal.localGroup B A T)).IsCComponent)
    (hqK : IsQuasisimple (B ⧸ pCore 2 B))
    (hfaith : intrinsicSignalizerModule B ≠ ⊥)
    (hgen : ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B)
    (hcard : Nat.card (B ⧸ pCore 2 B) = 60 ∨
      Nat.card (B ⧸ pCore 2 B) = 360 ∨ Nat.card (B ⧸ pCore 2 B) = 1080) :
    Nonempty (ChosenModule T B
      (Diagonal.movedModule B A T)) := by
  let J := Diagonal.localGroup B A T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  let σ := reducedRepresentation J
  let I := moved σ BJ
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAB.trans B.le_normalizer)) hTB
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hact : σ = ρ.comp q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
  have hI : I = moved ρ Bq := by
    change moved σ BJ = moved ρ (BJ.map q)
    rw [hact,moved_comp_map]
  have himage : subspaceImage J I = Diagonal.movedModule B A T := by
    rw [hI]
    change subspaceImage J (subspaceCommutator ρ ⊤ (BJ.map q)) = _
    rw [←NormalElementaryQuotient.commutatorSpace_eq W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) BJ]
    change ((⁅W,BJ⁆.subgroupOf W).map W.subtype).map J.subtype = _
    rw [map_subgroupOf_eq_of_le (commutator_le_left W BJ),map_commutator,
      map_subgroupOf_eq_of_le hBJ]
    rfl
  obtain ⟨hBq,_,_⟩ :=
    component_join_offender_entry T J B hJ hBJ hJN hK hqK hfaith hTJ hgen
  obtain ⟨_,⟨c⟩⟩ :=
    small_component_quasisimple_row T B A hAB hTB hJ hK hqK hfaith hgen
  have hspace : c.sectionData.space.toSubmodule = moved ρ Bq := by
    rw [c.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hBq]
  have hdiv : Nat.card (Bq.subgroupOf N) ∣ Nat.card (B ⧸ pCore 2 B) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBq).toEquiv]
    exact reduced_component_card_dvd J B hBJ hJN
  have hbase : IsIrrPlus (ρ.comp N.subtype) (Bq.subgroupOf N) c.sectionData.space.toSubmodule := by
    cases c.clause_one with
    | irreducible hi _ _ _ _ => exact hi
    | doubleThree F _ e _ _ =>
      rw [Nat.card_congr e.groupEquiv.toEquiv] at hdiv
      exact (small_card_excludes_linear_three F hcard hdiv).elim
    | naturalDual d hd _ hn =>
      obtain ⟨e⟩ := hn
      rw [Nat.card_congr e.groupEquiv.toEquiv] at hdiv
      exact (small_card_excludes_binary_higher hd hcard hdiv).elim
    | repeatedNatural d r hd _ _ _ hn =>
      obtain ⟨e⟩ := hn
      rw [Nat.card_congr e.groupEquiv.toEquiv] at hdiv
      exact (small_card_excludes_binary_higher hd hcard hdiv).elim
  have hirr : IsIrrPlus ρ Bq (moved ρ Bq) := by
    rw [←hspace]
    exact (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp hbase
  have hirr' : IsIrrPlus σ BJ I := by
    have hh := IsIrrPlus.map_embedding σ ρ q (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)
      Function.injective_id (fun g w => by rw [hact]; rfl) BJ (moved ρ Bq) hirr
    simpa only [Submodule.map_id,←hI] using hh
  have hnormal : (T : Subgroup G).subgroupOf J ≤ normalizer (BJ : Set J) :=
    le_normalizer_of_normal
  have hstable : (T : Subgroup G).subgroupOf J ≤ subspaceStabilizer σ I :=
    subspaceCommutator_invariant_normalizer σ
      (by intro t ht v; simp) hnormal
  have hchoice : IsIrrPlusWith σ BJ ((T : Subgroup G).subgroupOf J) I := by
    refine ⟨hnormal,hirr'.choose,hirr',?_⟩
    apply le_antisymm
    · rw [orbitSpan_eq_self σ hstable]
      exact iSup_le fun S => iSup_le fun hS => hS.1
    · exact quotientImage_le_homogeneousPart σ hirr'.choose
  have hJ : J = B ⊔ (T : Subgroup G) := by
    change (B ⊔ A) ⊔ (T : Subgroup G) = _
    rw [sup_eq_left.mpr hAB]
  have aux : ∀ (J' : Subgroup G) (I' : Submodule (ZMod 2) (Additive (ReducedModule J'))),
      J' = B ⊔ (T : Subgroup G) →
      IsIrrPlusWith (reducedRepresentation J') (B.subgroupOf J')
        ((T : Subgroup G).subgroupOf J') I' →
      subspaceImage J' I' = Diagonal.movedModule B A T →
      Nonempty (ChosenModule T B (Diagonal.movedModule B A T)) := by
    intro J' I' hj' hi' he'
    subst J'
    exact ⟨⟨I',hi',he'⟩⟩
  exact aux J I hJ hchoice himage

omit [Finite G] in
private theorem small_chosen_minimal (D : ChosenModule T K V)
    (A : Subgroup G) (hAV : A ≤ V) (hn : K ≤ normalizer (A : Set G)) :
    A = V ∨ A ≤ centralizer (K : Set G) := by
  let H := K ⊔ (T : Subgroup G)
  let I : Submodule (ZMod 2) (Additive (ReducedModule H)) :=
    ((A.subgroupOf H).subgroupOf (ReducedModule H)).toAddSubgroup.toZModSubmodule 2
  have hAR : A ≤ (ReducedModule H).map H.subtype := hAV.trans D.le_reduced
  have hAH : A ≤ H := hAR.trans (map_subtype_le _)
  have hI : I ≤ D.space := by
    intro v hv
    have hh : v.toMul.val.val ∈ subspaceImage H D.space := D.image_eq.symm ▸ hAV hv
    obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hh
    have he' : Additive.ofMul w = v :=
      Additive.toMul.injective (Subtype.ext (Subtype.ext he))
    exact he' ▸ hw
  have hi : K.subgroupOf H ≤ subspaceStabilizer (reducedRepresentation H) I := by
    apply le_subspaceStabilizer
    intro k hk a ha
    change k.val * a.toMul.val.val * k.val⁻¹ ∈ A
    exact (mem_normalizer_iff.mp (hn hk) _).mp ha
  have image : subspaceImage H I = A := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact hv
    · intro a ha
      obtain ⟨v, hv, he⟩ := hAR ha
      refine ⟨v, ⟨⟨v, hv⟩, ?_, rfl⟩, he⟩
      change v.val ∈ A
      change v.val = a at he
      rw [he]
      exact ha
  rcases D.irrPlus.isIrrPlus.eq_or_le_fixedSpace (reducedRepresentation H) hi hI with he | hc
  · exact Or.inl (image.symm.trans (he ▸ D.image_eq))
  · right
    intro a ha k hk
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := image.symm ▸ ha
    have hh := congrArg (fun w : Additive (ReducedModule H) => w.toMul.val.val)
      (hc hv ⟨⟨k, (le_sup_left : K ≤ H) hk⟩, hk⟩)
    change k * v.val.val * k⁻¹ = v.val.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

open Chapter14.Section03.FaithfulSource

/-- The A₅, A₆ and covered-A₆ quotient orders rule out all reducible B.5 rows.
Thus the actual moved omega-orbit is chosen and equals the entire reduced moved
module, also when its fixed space is zero. The doubled L₃(2) row is not excluded. -/
theorem component_chosen_of_small_quotient
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hcard : Nat.card (K ⧸ pCore 2 K) = 60 ∨
      Nat.card (K ⧸ pCore 2 K) = 360 ∨ Nat.card (K ⧸ pCore 2 K) = 1080) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    Nonempty (ChosenModule T K U) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ := by
  have hTK := (h1332 K hfK).1
  have hqK := component_quotient_quasisimple h1332 hfK
  have hgen := component_thompson_generation (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let R := (ReducedModule H).map H.subtype
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hUH : U ≤ H :=
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans
      (conjugateSpanBy_le
        ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from
          fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1).trans le_sup_right)
        (le_sup_left.trans H.le_normalizer))
  have hUR : U ≤ R := by
    have hh := map_mono (f := H.subtype) hred.le_reducedPSubgroup
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hUU : ⁅U,K⁆ = U := component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hUB : U ≤ ⁅R,K⁆ := hUU ▸ commutator_mono hUR le_rfl
  have hlocal : Section03.Noncentrality.Diagonal.localGroup K ⊥ T = H := by
    change (K ⊔ ⊥) ⊔ (T : Subgroup G) = H
    rw [sup_bot_eq]
  have hmoved : Section03.Noncentrality.Diagonal.movedModule K ⊥ T = ⁅R,K⁆ := by
    unfold Section03.Noncentrality.Diagonal.movedModule
      Section03.Noncentrality.Diagonal.reducedModule
    rw [hlocal]
  obtain ⟨DK⟩ := small_moved_module_chosen T K ⊥
    bot_le hTK (hlocal.symm ▸ hSQ)
    (hlocal.symm ▸ hfK.1.1)
    hqK hfK.2.2 hgen hcard
  have DK' : ChosenModule T K ⁅R,K⁆ := hmoved ▸ DK
  have hn : K ≤ normalizer (U : Set G) := normalizer_commutator_ge_right _ _
  have he : U = ⁅R,K⁆ := (small_chosen_minimal DK' U hUB hn).resolve_right (by
    intro hc
    have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [hUU] at hh
    exact component_moved_ne_bot h structural m hKM hh)
  refine ⟨?_,he⟩
  change Nonempty (ChosenModule T K U)
  rw [he]
  exact ⟨DK'⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
