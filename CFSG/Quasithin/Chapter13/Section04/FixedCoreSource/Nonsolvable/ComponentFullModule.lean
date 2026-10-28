module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearModule
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels

/-!
# Fully moved linear-three modules in arbitrary overgroups

The full commutator property eliminates the product rows of B.5.6: its
factor subspaces are disjoint modulo the global fixed space, so one whole
moved factor would force the other faithful factor action to vanish. The
hyperplane row cannot be fully moved, and the outer A₆ row has the wrong
component order. The remaining quasisimple B.5.1 row gives either Irr⁺
minimality or two actual natural three-spaces on the literal K/O₂(K) map.

ComponentFullLinear applies this to [⟨Ω₁Z(T)^C_G(z)⟩,K], without assuming
that the ambient overgroup modulo K is a two-group. The earlier public
KT-only classification remains unchanged.
Source: Aschbacher--Smith B.5.1, B.5.6 and 13.4.10(7), pp.99,105,909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}


open Representation Representation.BinaryOffender
open ChapterB.SourceInduction ChapterB.QuasisimpleSource Section03.Noncentrality
open scoped MatrixGroups
private theorem component_le_product_factor {D : Type*} [Group D]
    {A B C : Subgroup D} (h : InternalProduct A B) (hC : IsComponent D C) :
    C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim


private theorem no_twoFactors_full_component
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) A X} (d : SourceTwoFactorCase ρ)
    (C : Subgroup A) (hC : C ≤ d.first) (hm : moved ρ C = ⊤) : False := by
  have hfirst : d.firstSpace.toSubmodule = ⊤ := top_unique (by
    rw [←hm]
    exact (show moved ρ C ≤ moved ρ d.first from Submodule.span_mono
      (by rintro _ ⟨a,ha,v,hv,rfl⟩; exact ⟨a,hC ha,v,hv,rfl⟩)).trans d.firstCase.moved_le_space)
  have himage : (fixed ρ).quotientImage d.firstSpace = ⊤ :=
    (Subrepresentation.quotientImage_eq_top_iff _ _).mpr (by rw [hfirst,sup_top_eq])
  have hzero : ((fixed ρ).quotientImage d.secondSpace).toSubmodule = ⊥ := by
    have hd := d.decomposition.disjoint
    rw [himage] at hd
    change Disjoint (⊤ : Submodule (ZMod 2) (X ⧸ (fixed ρ).toSubmodule)) _ at hd
    exact disjoint_top.mp hd.symm
  let U := ((fixed ρ).quotientImage d.secondSpace).toSubmodule
  let : Subsingleton U := by
    change Subsingleton ((fixed ρ).quotientImage d.secondSpace).toSubmodule
    rw [hzero]
    infer_instance
  let : Nontrivial d.second := d.secondCase.nontrivial
  have he (a b : d.second) : a = b := d.secondCase.faithful (by
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _)
  exact not_subsingleton d.second ⟨he⟩

private theorem quasisimple_of_full_linear_component
    {A X : Type*} [Group A] [Finite A] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) A X) (C : Subgroup A)
    (hC : IsComponent A C) (hm : moved ρ C = ⊤)
    (hcard : Nat.card C ∣ 168) (h : NontrivialAdequateAlternative ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) := by
  let := hC.2
  cases h with
  | quasisimple hq c =>
    have he : C = generalizedFitting A := hC.eq_of_le
      ⟨(inferInstance : (generalizedFitting A).Normal).isSubnormal,hq⟩
      (component_le_generalizedFitting A C hC)
    exact he.symm ▸ ⟨c⟩
  | symmetricThree d =>
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype,←alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
      (f := d.equiv.toMonoidHom) d.equiv.injective
    let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors d =>
    rcases component_le_product_factor d.product hC with ha | hb
    · exact (no_twoFactors_full_component d C ha hm).elim
    · let ds : SourceTwoFactorCase ρ :=
        ⟨d.second,d.first,d.product.swap,d.secondSpace,d.firstSpace,
          d.decomposition.symm,d.secondCase,d.firstCase⟩
      exact (no_twoFactors_full_component ds C hb hm).elim
  | outerSixThree d =>
    let := d.first_normal
    let := d.quotient_first_solvable
    have he : C = d.first := hC.eq_of_le d.first_isComponent
      (le_of_isPerfect_of_solvable_quotient C d.first)
    have hc : Nat.card C = 360 := by
      rw [he,Nat.card_congr d.firstEquiv.toEquiv,nat_card_alternatingGroup]
      norm_num
    rw [hc] at hcard
    norm_num at hcard
  | hyperplane d =>
    have ht : moved ρ ⊤ = ⊤ := top_unique (by
      rw [←hm]
      exact Submodule.span_mono (by
        rintro _ ⟨a,ha,v,hv,rfl⟩
        exact ⟨a,mem_top _,v,hv,rfl⟩))
    have hd := d.hyperplane
    rw [ht,top_sup_eq] at hd
    have hz : Module.finrank (ZMod 2) (X ⧸ (⊤ : Submodule (ZMod 2) X)) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega

private theorem full_linear_three_degree_one (F : BinaryField)
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

private theorem full_large_linear_not_dvd {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ Nat.card SL(n,BinaryField.two.Carrier) ∣ 168 := by
  have hc : Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
      Matrix.card_GL_field]
    simp
  change ¬ Nat.card SL(n,ZMod 2) ∣ 168
  rw [hc]
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ]

/-- Classify a reduced elementary subgroup fully moved by a normal
linear-three component, allowing arbitrary ambient overgroups. The conclusion uses its own elements and conjugation. -/
theorem full_linear_reduced_component_minimal_or_double
    (S : Sylow 2 G) (K U : Subgroup G) [K.Normal] [U.Normal]
    [IsElementaryAbelian 2 U]
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hred : IsPReduced 2 U) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hcard : Nat.card (K ⧸ pCore 2 K) = 168)
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
  have hmov : moved ρ Bq = ⊤ := by
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) ⊤ (K.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) K]
    change AddSubgroup.toZModSubmodule 2 ((⁅U,K⁆ : Subgroup G).subgroupOf U).toAddSubgroup = ⊤
    rw [hmove,subgroupOf_self]
    rfl
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
  have hmovB : moved (ρ.comp N.subtype) B = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hBq,hmov]
  obtain ⟨c⟩ := quasisimple_of_full_linear_component (ρ.comp N.subtype) B hcomp hmovB hd
    (ha.of_nontrivial _)
  have hs : c.sectionData.space.toSubmodule = ⊤ := by
    rw [c.sectionData.space_eq,hmovB]
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
    have hF : F.degree = 1 := full_linear_three_degree_one F (by
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
    exact (full_large_linear_not_dvd hn hd).elim
  | repeatedNatural n r hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    rw [Nat.card_congr a.groupEquiv.toEquiv] at hd
    exact (full_large_linear_not_dvd hn hd).elim


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
