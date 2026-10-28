module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredDoubled
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalResidual
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# The selected linear-three moved module

Apply the full B.5 classification directly to the actual reduced subgroup
U = [⟨Ω₁Z(T)^K⟩,K]. Thompson generation places its faithful component
image in the offender group. The quotient order 168 leaves either Irr⁺
minimality or two natural binary three-spaces. In the latter case the
literal action is transported to the existing augmentation Baumann/chief
contradiction. Thus U itself is chosen, with no minimality callback.

The earlier fixed-module clause excludes nonzero K-fixed vectors, and the
seven-case theorem identifies the whole U with the natural module. All
coordinates retain K → K/O₂(K). The resulting central-core marking and
the proved orbit splitting give |Ω₁Z(T)|=4 and Ω₁Z(T)≤V.
ComponentLinearResidual applies these coordinates to the original ordinary
L branch. Equality U=[R₂(KT),K], the covered-original linear row, the
selected covered-A₆ row, and comparison/commutator/graph assembly remain
with qt-d-1341-nonsolvable-source.

LargeDistanceInput retains producer qt-e-ms-small-a6-exhaustion-large-distance.
The earlier module and structural premises retain qt-d-1222-modules,
qt-d-1222-source and qt-d-1332-source, with final source discharge by
qt-d-1341-fixed-core-source. The universal Structural1222 is not inferred
from Structural1222At. Both escaping weights still require nonsolvability.
Source: Aschbacher–Smith B.5.1, 13.3.2(3), and 13.4.10(4–5),
printed pp.99,885,907–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open ChapterB.QuasisimpleSource ChapterB.SourceInduction Section03.Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem linear_three_degree_one (F : BinaryField)
    (hd : Nat.card SL(3,F.Carrier) ∣ 168) : F.degree = 1 := by
  have hb := Nat.le_of_dvd (by decide : 0 < 168) hd
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear] at hb
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
  rw [F.card_eq] at he
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using he)

private theorem large_linear_not_dvd {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ Nat.card SL(n,BinaryField.two.Carrier) ∣ 168 := by
  have hc : Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
      Matrix.card_GL_field]
    simp
  change ¬ Nat.card SL(n,ZMod 2) ∣ 168
  rw [hc]
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ]

/-- Classify the actual reduced, fully moved elementary subgroup of a
linear-three component. The conclusion uses its own elements and conjugation. -/
theorem linear_reduced_component_minimal_or_double
    (S : Sylow 2 G) (K U : Subgroup G) [K.Normal] [U.Normal]
    [IsElementaryAbelian 2 U]
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hred : IsPReduced 2 U) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hcard : Nat.card (K ⧸ pCore 2 K) = 168)
    (hsup : K ⊔ (S : Subgroup G) = ⊤)
    (hgen : ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆ = K)
    (hmove : ⁅U,K⁆ = U) (hne : U ≠ ⊥) :
    (∀ A : Subgroup G, A ≤ U → K ≤ normalizer (A : Set G) →
      A = U ∨ A ≤ centralizer (K : Set G)) ∨
    ∃ eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
      ∃ e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector),
        ∀ (k : K) (v : U), (e (MulAut.conjNormal k.val v)).toAdd =
          (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
            (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let Bq := K.map q
  let B := Bq.subgroupOf N
  have hcore : K.pCoreIn 2 ≤ C := by
    have hc : K.pCoreIn 2 ≤ pCore 2 G := by
      change (pCore 2 K).map K.subtype ≤ pCore 2 G
      exact le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    exact hc.trans (le_centralizer_iff.mp hred.le_centralizer_pCore)
  have hBq : Bq ≤ N := by
    have hJT := ChapterB.RankOneBaumann.thompson_image_le_offender_layer S U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (hred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) N le_rfl
    let : N.Normal := offenderSubgroup_normal ρ
    change K.map q ≤ N
    rw [←hgen,map_commutator]
    exact (commutator_mono le_rfl hJT).trans (commutator_le_right _ _)
  have hcompq : IsComponent (G ⧸ C) Bq :=
    hK.isComponent_map_of_twoCore_killed hqK q (QuotientGroup.mk'_surjective C)
      (by rwa [QuotientGroup.ker_mk']) (by
        intro he
        have hc : K ≤ C := by
          simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff K).mp he
        exact hne (hmove.symm.trans
          (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))))
  have hcomp : IsComponent N B := hcompq.subgroupOf hBq
  let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr hcomp.isCComponent.ne_bot
  let : Nontrivial N := Function.Injective.nontrivial (f := B.subtype) Subtype.val_injective
  have ha := ChapterB.offender_restriction_classification ρ
    ChapterB.SourceInduction.adequateClassification_knownSimple
    (NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))
    hred.quotient_pCore_eq_bot
    ⟨{ Cover := G, kernel := C, sqtk := hG, equiv := MulEquiv.refl _ }⟩
  let : Bq.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B.Normal := inferInstance
  have hquot : IsPGroup 2 ((G ⧸ C) ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq ((S : Subgroup G).map q)
      (S.isPGroup'.map q) (by
        rw [←Subgroup.map_sup,hsup,map_top_of_surjective q (QuotientGroup.mk'_surjective C)])
  have hqN := isPGroup_quotient_subgroupOf Bq N hquot
  have hNcore : pCore 2 N = ⊥ := offenderSubgroup_twoCore ρ hred.quotient_pCore_eq_bot
  obtain ⟨c⟩ := quasisimple_row_of_component_two_quotient (ρ.comp N.subtype) B hcomp hqN hNcore
    (ha.of_nontrivial _)
  have hmov : moved ρ Bq = ⊤ := by
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) ⊤ (K.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) K]
    change AddSubgroup.toZModSubmodule 2 ((⁅U,K⁆ : Subgroup G).subgroupOf U).toAddSubgroup = ⊤
    rw [hmove,subgroupOf_self]
    rfl
  have hs : c.sectionData.space.toSubmodule = ⊤ := by
    rw [c.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hBq,hmov]
  let f : K →* B := (subgroupOfEquivOfLe hBq).symm.toMonoidHom.comp (q.subgroupMap K)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨k,hk⟩ := q.subgroupMap_surjective K ((subgroupOfEquivOfLe hBq) b)
    exact ⟨k,(subgroupOfEquivOfLe hBq).injective hk⟩
  have hk : pCore 2 K ≤ f.ker := by
    intro k hk
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := C) k.val).mpr (hcore (mem_map_of_mem K.subtype hk))
  let g := QuotientGroup.lift (pCore 2 K) f hk
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  have hd : Nat.card B ∣ 168 := hcard ▸ card_dvd_of_surjective g hg
  cases c.clause_one with
  | irreducible hi _ _ _ _ =>
    left
    have hi' : IsIrrPlus ρ Bq ⊤ := by
      rw [hs] at hi
      exact (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp hi
    intro A hAU hn
    let I : Submodule (ZMod 2) (Additive U) := (A.subgroupOf U).toAddSubgroup.toZModSubmodule 2
    have hI : Bq ≤ subspaceStabilizer ρ I := by
      apply le_subspaceStabilizer
      rintro b ⟨k,hk,rfl⟩ v hv
      change ((ρ (q k) v).toMul : G) ∈ A
      rw [NormalElementaryQuotient.representation_apply]
      exact (mem_normalizer_iff.mp (hn hk) _).mp hv
    rcases hi'.eq_or_le_fixedSpace ρ hI le_top with he | hc
    · left
      apply le_antisymm hAU
      intro a ha
      have hh : Additive.ofMul (⟨a,ha⟩ : U) ∈ I := he.symm ▸ Submodule.mem_top
      exact hh
    · right
      intro a ha k hk
      have hh := hc (show Additive.ofMul (⟨a,hAU ha⟩ : U) ∈ I from ha)
        ⟨q k,mem_map_of_mem q hk⟩
      have hh' := congrArg (fun w : Additive U => w.toMul.val) hh
      change ((NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
        (q k) (Additive.ofMul ⟨a,hAU ha⟩)).toMul : G) = a at hh'
      rw [NormalElementaryQuotient.representation_apply] at hh'
      exact mul_inv_eq_iff_eq_mul.mp hh'
  | doubleThree F _ a _ _ =>
    have hF : F.degree = 1 := linear_three_degree_one F (by
      rwa [Nat.card_congr a.groupEquiv.toEquiv] at hd)
    let a' := a.trans (ExtensionConsequences.degreeOneRepeatedEquiv F hF 3 2)
    have hBc : Nat.card B = 168 := by
      rw [Nat.card_congr a'.groupEquiv.toEquiv]
      change Nat.card SL(3,ZMod 2) = 168
      rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      norm_num
    have hgi : Function.Injective g :=
      (Nat.bijective_iff_surjective_and_card g).mpr ⟨hg,hcard.trans hBc.symm⟩ |>.1
    let eK := (MulEquiv.ofBijective g ⟨hgi,hg⟩).trans a'.groupEquiv
    let l : Additive U ≃ₗ[ZMod 2] c.sectionData.space.toSubmodule :=
      (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) (Additive U)) ≃ₗ[ZMod 2] Additive U).symm.trans
        (LinearEquiv.ofEq _ _ hs.symm)
    let pair : (Fin 2 → BinaryLinearThree.Vector) ≃ₗ[ZMod 2]
        (BinaryLinearThree.Vector × BinaryLinearThree.Vector) := LinearEquiv.finTwoArrow _ _
    let e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector) :=
      ((l.trans a'.linearEquiv).trans pair).toAddEquiv.toMultiplicative
    refine Or.inr ⟨eK,e,?_⟩
    intro k v
    have hi := a'.intertwines (f k) (l (Additive.ofMul v))
    have hl : l (Additive.ofMul (MulAut.conjNormal k.val v)) =
        c.sectionData.space.toRepresentation (f k).val (l (Additive.ofMul v)) := by
      apply Subtype.ext
      change Additive.ofMul (MulAut.conjNormal k.val v) = ρ (q k.val) (Additive.ofMul v)
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (NormalElementaryQuotient.representation_apply U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) k.val _).symm
    change pair (a'.linearEquiv (l (Additive.ofMul (MulAut.conjNormal k.val v)))) = _
    rw [hl]
    exact congrArg (fun t : Fin 2 → Fin 3 → BinaryField.two.Carrier => pair t) hi
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    rw [Nat.card_congr a.groupEquiv.toEquiv] at hd
    exact (large_linear_not_dvd hn hd).elim
  | repeatedNatural n r hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    rw [Nat.card_congr a.groupEquiv.toEquiv] at hd
    exact (large_linear_not_dvd hn hd).elim


open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
variable {T : Sylow 2 G} {L K V : Subgroup G}

/-- The actual linear-three moved orbit is chosen: the doubled alternative
contradicts the original augmentation Baumann/chief-factor argument. -/
theorem linear_component_chosen
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nonempty (ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆) := by
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let A := K.subgroupOf H
  let W := U.subgroupOf H
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hKH : K ≤ H := le_sup_left
  have hUH : U ≤ H := hUK.trans hKH
  have hnK : H ≤ normalizer (K : Set G) := sup_le K.le_normalizer hTK
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnK
  let : W.Normal := hred.normal
  let : IsElementaryAbelian 2 W := hred.elementary
  have hUn : H ≤ normalizer (U : Set G) := le_normalizer_of_normal_subgroupOf hUH
  have hmove := component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hne : U ≠ ⊥ := component_moved_ne_bot h structural m hKM
  have hgen := component_thompson_generation (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let a : A ≃* K := subgroupOfEquivOfLe hKH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let := component_quotient_quasisimple h1332 hfK
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hcard : Nat.card (A ⧸ pCore 2 A) = 168 := by
    rw [Nat.card_congr (aq.trans eK).toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    norm_num
  have hsup : A ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,
      ←MonoidHom.range_eq_map,range_subtype]
    change K ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hgenA : ⁅A,elementaryAbelianMaxJ (S : Subgroup H)⁆ = A := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKH,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change ⁅K,elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype)⁆ = K
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact hgen
  have hmoveW : ⁅W,A⁆ = W := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hUH]
    exact hmove
  have hneW : W ≠ ⊥ := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact hne hh
  rcases linear_reduced_component_minimal_or_double S A W hSQ hred hfK.1.1
      hqA hcard hsup hgenA hmoveW hneW with hmin | ⟨qK,e,he⟩
  · apply Section03.PlaneNoncentralitySource.exists_chosenModuleOfMinimal
      hred hUH hTK hUn hmove hne
    intro B hBU hn
    have hBn : A ≤ normalizer (B.subgroupOf H : Set H) := by
      apply le_normalizer_iff.mpr
      intro k hk b hb
      exact (mem_normalizer_iff.mp (hn hk) b.val).mp hb
    rcases hmin (B.subgroupOf H) (comap_mono hBU) hBn with he | hc
    · left
      have hh := congrArg (map H.subtype) he
      rwa [map_subgroupOf_eq_of_le (hBU.trans hUH),map_subgroupOf_eq_of_le hUH] at hh
    · right
      intro b hb k hk
      exact congrArg Subtype.val (hc (show (⟨b,(hBU.trans hUH) hb⟩ : H) ∈ B.subgroupOf H from hb)
        ⟨k,hKH hk⟩ hk)
  · let w : W ≃* U := subgroupOfEquivOfLe hUH
    let qK' := aq.symm.trans qK
    let e' := w.symm.trans e
    have he' : letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
        ∀ (k : K) (v : U), (e' (k • v)).toAdd =
          (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
            (qK' (QuotientGroup.mk' (pCore 2 K) k)) (e' v).toAdd := by
      intro k v
      exact he (a.symm k) (w.symm v)
    exact (doubled_excluded_of_largeDistance hl h₀ h structural D m z hzT hzL
      hKz hHN hKM hTK qK' e' he').elim


omit [Finite G] in
private theorem linear_three_card (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nat.card (K ⧸ pCore 2 K) = 168 := by
  rw [Nat.card_congr eK.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  norm_num

/-- The fixed-free chosen linear-three action is the literal natural action;
the four-dimensional extension is excluded by irreducibility. -/
theorem linear_three_natural_coordinates {U : Subgroup G}
    (DK : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hfixed : U ⊓ centralizer (K : Set G) = ⊥)
    (hm : ModuleAlternatives1222 DK) :
    ∃ q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
      ∃ e : U ≃* Multiplicative BinaryLinearThree.Vector,
        ∀ (k : K) (v : U),
          (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
            BinaryLinearThree.W (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd := by
  have hc := linear_three_card eK
  let := DK.actionCentralizer_normal
  have hfaith : Nat.card (K ⧸ (centralizer (U : Set G)).subgroupOf K) ∣ 168 :=
    hc ▸ card_dvd_of_surjective DK.coreToFaithful DK.coreToFaithful_surjective
  have haction : Nonempty (ActionEquiv DK.quotientAction BinaryLinearThree.W) := by
    cases hm with
    | linear n hn a =>
      rcases hn with rfl | rfl | rfl
      · exact ⟨a⟩
      · exact (large_linear_not_dvd (Or.inl rfl)
          (dvd_of_eq ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc))).elim
      · exact (large_linear_not_dvd (Or.inr rfl)
          (dvd_of_eq ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc))).elim
    | linearThreeExtension a hd _ =>
      exact (RecognitionSource.not_linear_three_four_fixedFree DK hfixed a hd).elim
    | linearFiveExterior a _ _ =>
      exact (large_linear_not_dvd (Or.inr rfl)
        (dvd_of_eq ((Nat.card_congr a.toEquiv).symm.trans hc))).elim
    | alternating n hn hn' a =>
      rw [Nat.card_congr a.groupEquiv.toEquiv] at hfaith
      change Nat.card (alternatingGroup (Fin n)) ∣ 168 at hfaith
      interval_cases n <;>
        norm_num only [nat_card_alternatingGroup,Nat.card_fin,Nat.factorial] at hfaith
    | alternatingSevenFour a _ =>
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hfaith
      norm_num at hfaith
    | g2 a =>
      have hh := (Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc
      rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
      omega
    | tripleSix a _ _ _ =>
      have hh := (Nat.card_congr a.toEquiv).symm.trans hc
      rw [Atlas.Codes.hexEven_card] at hh
      omega
  obtain ⟨a⟩ := haction
  obtain ⟨q,e,he⟩ := DK.conjugationModel_of_quotientAction a
  refine ⟨q,e,?_⟩
  intro k v
  have hh : e.symm (Multiplicative.ofAdd (BinaryLinearThree.W
      (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)) =
      U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v := Subtype.ext (he k v)
  simpa only [e.apply_symm_apply,toAdd_ofAdd] using
    (congrArg (fun w : U => (e w).toAdd) hh).symm

omit [Finite G] in
private theorem linear_three_centralCore
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Section08.TransvectionRecognition.Component.ModelExtension.centralCore K = pCore 2 K := by
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have he : eK x ∈ center BinaryLinearThree.Group := (centerCongr eK ⟨x,hx⟩).property
    rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at he
    exact eK.map_eq_one_iff.mp he
  change (center (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)) = _
  rw [hz,MonoidHom.comap_bot,QuotientGroup.ker_mk']

/-- The original linear-three component has a natural marking and the full
central four-group. Minimality and vanishing fixed space are proved here. -/
theorem linear_component_marking
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      ∃ q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
        ∃ e : U ≃* Multiplicative BinaryLinearThree.Vector,
          (∀ (k : K) (v : U),
            (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
              BinaryLinearThree.W (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) ∧
          U ⊓ centralizer (K : Set G) = ⊥ ∧
          Nonempty (ComponentModuleAt DK z.val) ∧
          omegaOneCenterAmbient (T : Subgroup G) =
            V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
          Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨DK⟩ := linear_component_chosen hl h₀ h structural D m h1332 z hzT hzL hKz hHN hKM hfK eK
  have hfixed : U ⊓ centralizer (K : Set G) = ⊥ := by
    by_contra hf
    obtain ⟨a⟩ := fixed h₀ K hfK U DK hf
    let := DK.actionCentralizer_normal
    have hd := card_dvd_of_surjective
      (a.groupEquiv.toMonoidHom.comp DK.coreToFaithful)
      (a.groupEquiv.surjective.comp DK.coreToFaithful_surjective)
    rw [linear_three_card eK,nat_card_alternatingGroup,Nat.card_fin] at hd
    norm_num at hd
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨q,e,he⟩ := linear_three_natural_coordinates DK eK hfixed (modules K U hK12 DK)
  let ec := QuotientGroup.quotientMulEquivOfEq (linear_three_centralCore eK)
  have mark : ComponentModuleAt DK z.val := .linearThree (ec.trans q) e (fun k v => he k v)
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  exact ⟨DK,q,e,he,hfixed,⟨mark⟩,full_seed_of_component_split h structural m z
    (fun hh => hz1 (congrArg Subtype.val hh)) hzT hindex DK mark hKz hKM
    (component_seed_split h₀ hzT hz1 hKz (h1332 K hfK).1)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
