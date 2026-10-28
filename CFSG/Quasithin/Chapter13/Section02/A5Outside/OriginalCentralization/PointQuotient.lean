module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointModule
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.Noncentral
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization

/-!
# The original paired point quotients outside the two-core

The prescribed first factor supplies a natural plane containing the actual
complementary point zv. Its three conjugates multiply to one. The second
point residual has the same identity modulo the central v-line. In the
literal O₃′ quotient, zv remains a nontrivial central Sylow involution.
Thus both quotient vertices move it. The S₃ quotient puts it in each local
two-core; failure of characteristic two would centralize it. The proved
noncentral-omega amalgam theorem now identifies both local groups as S₄ or
C₂ × S₄. Each original local two-residual therefore maps onto A₄, with
kernel its intersection with the original ambient two-core.

SourceAssembly/PointQuotient applies these results in the universal terminal
argument. Lifting this residual recognition to the A₃ block exclusion, the
FF core branch, nonsolvable generation and single-factor endgame remain
with qt-d-1367-assembly. Earlier Context/13.3.2, C.1.32 and 5.2.3 retain
their producers; qt-d-1361-source owns final discharge. This does not yet
prove original 13.2.7 or 13.6.7.

Source: Aschbacher--Smith 13.2.11(3) and 13.2.12, printed pp.881--883;
F.6.5, p.305; Stellmacher (1997), (7.5) and (8.2).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]

private theorem original_factor_lines
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 →
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) →
      let E := fun i => ((AddSubgroup.toSubgroup'
        (c.toSolvableFFFactors.factorFixedSpace
          ((ChapterB.baumann (S : Subgroup H)).map q) i).toAddSubgroup).map U.subtype).map H.subtype
      (∀ i, Nat.card (E i) = 2 ∧ E i ≤ V₂ ∧ Disjoint (E i) V₁) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j) ∧ E i ⊔ E j = V₂ ∧
        ∀ a ∈ E i, a ≠ 1 → ∀ b ∈ E j, b ≠ 1 → zpowers (a * b) = V₁) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  dsimp only
  intro c hc ht
  let D := c.toSolvableFFFactors
  let A := (ChapterB.baumann (S : Subgroup H)).map q
  let F := fun i => D.factorFixedSpace A i
  let E := fun i => ((AddSubgroup.toSubgroup' (F i).toAddSubgroup).map U.subtype).map H.subtype
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hUT : U ≤ (S : Subgroup H) :=
    hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
  obtain ⟨hJq,hBq⟩ := ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot hUT hj c hc ht
  let O := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  obtain ⟨P,hP⟩ := (S.mapSurjective (QuotientGroup.mk'_surjective C)).exists_sylow_map_eq_inf_of_normal O
  have hPA : (P : Subgroup O).map O.subtype = A := hP.trans hBq.symm
  have hcard (i) : Nat.card (E i) = 2 := by
    rw [card_map_of_injective H.subtype_injective,card_map_of_injective U.subtype_injective]
    change Nat.card (F i) = 2
    dsimp [F]
    rw [← hPA]
    exact D.factorFixedSpace_card P i
  have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hJm : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hSm]
  have hle (i) : E i ≤ V₂ := by
    rw [← source_alpha_eq_flag_plane d hH hB hZ hs hz,
      source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz]
    rintro x ⟨y,⟨u,hu,rfl⟩,rfl⟩
    have hfix : Additive.ofMul u ∈ fixedSpace ρ
        ((elementaryAbelianMaxJ (S : Subgroup H)).map q) := by
      rw [hJq,← hBq]
      exact hu.2
    have hcu := (NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (elementaryAbelianMaxJ (S : Subgroup H)) (Additive.ofMul u)).mp hfix
    refine ⟨u.property,?_⟩
    intro t ht
    rw [← hJm] at ht
    obtain ⟨t,ht,rfl⟩ := ht
    exact congrArg H.subtype (hcu t ht)
  have hdisj (i j) (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply disjoint_map H.subtype_injective
    apply disjoint_map U.subtype_injective
    apply Subgroup.disjoint_def.mpr
    intro u hui huj
    exact Additive.ofMul.injective (Submodule.disjoint_def.mp
      (D.factorFixedSpace_disjoint A hij) (Additive.ofMul u) hui huj)
  have hline (i) : Disjoint (E i) V₁ := by
    apply Subgroup.disjoint_def.mpr
    rintro x ⟨y,⟨u,hu,rfl⟩,rfl⟩ hx
    have hxu : ((u : H) : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
      rwa [source_omegaCenter_eq_flag_line d hH hB hZ hs hz]
    have hcu : (u : H) ∈ centralizer (S : Set H) := by
      intro t ht
      apply Subtype.ext
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hxu).2.2 (t : G)
        (hSm ▸ mem_map_of_mem H.subtype ht)
    have hfix := (NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (S : Subgroup H) (Additive.ofMul u)).mpr hcu
    obtain ⟨k,hk⟩ := exists_ne ((finCongr hc) i)
    let j := (finCongr hc).symm k
    have hji : j ≠ i := fun he => hk (by simpa [j] using congrArg (finCongr hc) he)
    obtain ⟨t,hit⟩ := ht i j
    have hperm : D.factorConjugation (q t) i = j := D.factor_injective
      ((D.factor_map_conj (q t) i).symm.trans hit)
    have huj := D.action_mem_factor_support (q t) i hu.1
    rw [hperm] at huj
    have hfixed : ρ (q t) (Additive.ofMul u) = Additive.ofMul u :=
      hfix ⟨q t,mem_map_of_mem q t.property⟩
    change ρ (q t) (Additive.ofMul u) ∈ subspaceCommutator ρ ⊤ (D.factor j) at huj
    rw [hfixed] at huj
    have hu0 := Submodule.disjoint_def.mp (D.supports_independent.pairwiseDisjoint hji.symm)
      (Additive.ofMul u) hu.1 huj
    exact congrArg (fun w : Additive U => ((w.toMul : H) : G)) hu0
  refine ⟨fun i => ⟨hcard i,hle i,hline i⟩,?_⟩
  intro i j hij
  have hcomm : E j ≤ centralizer (E i : Set G) := by
    let := d.elementary
    intro x hx y hy
    exact congrArg V.subtype (mul_comm
      (⟨y,d.flag.two_le_V (hle i hy)⟩ : V) (⟨x,d.flag.two_le_V (hle j hx)⟩ : V))
  have hn := hcomm.trans (Subgroup.centralizer_le_normalizer _)
  have hjoin : E i ⊔ E j = V₂ := by
    apply eq_of_le_of_card_ge (sup_le (hle i) (hle j))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (hdisj i j hij),
      hcard,hcard,d.flag.two_card]
  refine ⟨hdisj i j hij,hjoin,?_⟩
  intro a ha ha1 b hb hb1
  exact zpowers_mul_eq_third_line (E i) (E j) V₁ (hcard i) (hcard j)
    d.flag.one_card (hline i) (hline j) (hjoin ▸ d.flag.one_le_two) hn
    a b ha ha1 hb hb1


private theorem natural_three_sum (w : Fin 2 → ZMod 2) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      w + a.val.mulVec w + b.val.mulVec w = 0 := by
  decide +revert +kernel

private theorem factor_three_sum
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : Representation (ZMod 2) D E} (c : ChapterB.SolvableFFFactors ρ)
    (i : Fin c.count) (w : E) (hw : w ∈ subspaceCommutator ρ ⊤ (c.factor i)) :
    ∃ a b : c.factor i, w + ρ a w + ρ b w = 0 := by
  let W := subspaceCommutator ρ ⊤ (c.factor i)
  let u : W := ⟨w,hw⟩
  obtain ⟨a,b,he⟩ := natural_three_sum (c.naturalEquiv i u)
  let a' := (c.factorModel i).symm a
  let b' := (c.factorModel i).symm b
  refine ⟨a',b',?_⟩
  have ha := c.naturalEquiv_action i a' u
  have hb := c.naturalEquiv_action i b' u
  rw [MulEquiv.apply_symm_apply] at ha hb
  rw [ha,hb]
  have hh := congrArg (fun y => ((c.naturalEquiv i).symm y : E)) he
  simpa only [map_add,map_zero,specialLinearNatural_apply,LinearEquiv.symm_apply_apply,Submodule.coe_add,Submodule.coe_zero] using hh

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The complementary point belongs to the actual first natural factor.
Its two factor conjugates have product with it equal to one. -/
theorem original_point_complement_three_conjugates
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁) :
    let x := markedZ d.flag.flag.module * markedV d.flag.flag.module
    ∃ a ∈ P₁, ∃ b ∈ P₁, x * MulAut.conj a x * MulAut.conj b x = 1 := by
  let s := d.flag.flag.module
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,ht,i,j,hij,hv,hP⟩ := horiginal
  let E := fun k => ((AddSubgroup.toSubgroup' (c.toSolvableFFFactors.factorFixedSpace
    ((ChapterB.baumann (S : Subgroup H)).map q) k).toAddSubgroup).map U.subtype).map H.subtype
  obtain ⟨hE,hpair⟩ := original_factor_lines d hH hB hZ hs hz c hc ht
  obtain ⟨a,ha,ha1,_⟩ := exists_generator_of_card_two (E i) (hE i).1
  have hline := (hpair i j hij).2.2 a ha ha1 (markedV s) hv (markedV_ne_one s)
  have hab : a * markedV s ≠ 1 := by
    intro he
    have haV : a = (markedV s)⁻¹ := eq_inv_of_mul_eq_one_left he
    have haJ : a ∈ E j := haV ▸ (E j).inv_mem hv
    exact ha1 (Subgroup.disjoint_def.mp (hpair i j hij).1 ha haJ)
  have hzline : markedZ s ∈ V₁ := d.flag.flag.line_eq ▸ mem_zpowers _
  have heq : a * markedV s = markedZ s := congrArg Subtype.val
    (((Nat.card_eq_two_iff' (1 : V₁)).mp d.flag.one_card).unique
      (show (⟨a * markedV s,hline ▸ mem_zpowers _⟩ : V₁) ≠ 1 from
        fun h => hab (congrArg Subtype.val h))
      (show (⟨markedZ s,hzline⟩ : V₁) ≠ 1 from
        fun h => markedZ_ne_one s (congrArg Subtype.val h)))
  have hv2 : markedV s * markedV s = 1 := by
    change s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) *
      s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) = 1
    rw [←map_mul]
    have hh : Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v *
      Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v = 1 := by decide +kernel
    rw [hh,map_one]
  have haeq : a = markedZ s * markedV s := by rw [←heq,mul_assoc,hv2,mul_one]
  have hxE : markedZ s * markedV s ∈ E i := haeq ▸ ha
  obtain ⟨y,⟨u,hu,rfl⟩,huG⟩ := hxE
  obtain ⟨a',b',hsum⟩ := factor_three_sum c.toSolvableFFFactors i
    (Additive.ofMul u) hu.1
  obtain ⟨a,haq⟩ := (QuotientGroup.mk'_surjective C) (a' : H ⧸ C)
  obtain ⟨b,hbq⟩ := (QuotientGroup.mk'_surjective C) (b' : H ⧸ C)
  have hPa : (a : G) ∈ P₁ := hP ▸ mem_sup_left
    (mem_map_of_mem H.subtype (show a ∈ (c.factor i).comap q from (show q a ∈ c.factor i from by rw [haq]; exact a'.property)))
  have hPb : (b : G) ∈ P₁ := hP ▸ mem_sup_left
    (mem_map_of_mem H.subtype (show b ∈ (c.factor i).comap q from (show q b ∈ c.factor i from by rw [hbq]; exact b'.property)))
  refine ⟨a,hPa,b,hPb,?_⟩
  have hsumG := congrArg (fun w : Additive U => ((w.toMul : H) : G)) hsum
  have hact (t : H) : (((ρ (q t) (Additive.ofMul u)).toMul : H) : G) =
      MulAut.conj (t : G) ((u : H) : G) := by
    exact congrArg H.subtype (NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) t (Additive.ofMul u))
  change ((u : H) : G) * (((ρ a' (Additive.ofMul u)).toMul : H) : G) *
    (((ρ b' (Additive.ofMul u)).toMul : H) : G) = 1 at hsumG
  rw [←haq,←hbq,hact,hact] at hsumG
  change ((u : H) : G) = markedZ s * markedV s at huG
  rwa [huG] at hsumG

omit d in
private theorem symmetricThree_triple (x a b : Equiv.Perm (Fin 3))
    (hx : x^2=1) (ht : x * MulAut.conj a x * MulAut.conj b x = 1) : x=1 := by
  decide +revert +kernel

omit d in
private theorem triple_involution_local_core
    {D : Type*} [Group D] {A : Subgroup D}
    (he : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)))
    (x : D) (hx : x ∈ A) (hpow : x^2=1)
    (ht : ∃ a ∈ A, ∃ b ∈ A, x * MulAut.conj a x * MulAut.conj b x = 1) :
    x ∈ A.pCoreIn 2 := by
  obtain ⟨e⟩ := he
  obtain ⟨a,ha,b,hb,ht⟩ := ht
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let x' : A := ⟨x,hx⟩
  let a' : A := ⟨a,ha⟩
  let b' : A := ⟨b,hb⟩
  have ht' : x' * MulAut.conj a' x' * MulAut.conj b' x' = 1 := Subtype.ext ht
  have hh := symmetricThree_triple (f x') (f a') (f b')
    (by rw [←map_pow,show x'^2=1 from Subtype.ext hpow,map_one])
    (by simpa only [MulAut.conj_apply,map_mul,map_inv,map_one] using congrArg f ht')
  have hq : QuotientGroup.mk' (pCore 2 A) x' = 1 := e.injective
    (hh.trans (map_one e).symm)
  exact mem_map_of_mem A.subtype ((QuotientGroup.eq_one_iff x').mp hq)

omit d in
private theorem triple_not_central
    {D : Type*} [Group D] {A : Subgroup D} (x : D)
    (hpow : x^2=1) (hne : x≠1)
    (ht : ∃ a ∈ A, ∃ b ∈ A, x * MulAut.conj a x * MulAut.conj b x = 1) :
    ¬ A ≤ centralizer ({x} : Set D) := by
  intro hc
  obtain ⟨a,ha,b,hb,ht⟩ := ht
  have hconj (g : D) (hg : g ∈ A) : MulAut.conj g x = x := by
    simp only [MulAut.conj_apply,mem_centralizer_singleton_iff.mp (hc hg),
      mul_assoc,mul_inv_cancel,mul_one]
  rw [hconj a ha,hconj b hb,←pow_two,hpow,one_mul] at ht
  exact hne ht

omit d in
private theorem triple_local_models
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (hg : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (x : D) (hx : x ∈ omegaOneCenterAmbient (A ⊓ B)) (hne : x≠1)
    (ha : ∃ a ∈ A, ∃ b ∈ A, x * MulAut.conj a x * MulAut.conj b x = 1)
    (hb : ∃ a ∈ B, ∃ b ∈ B, x * MulAut.conj a x * MulAut.conj b x = 1) :
    (¬ A ≤ centralizer ({x} : Set D)) ∧ (¬ B ≤ centralizer ({x} : Set D)) ∧
    generalizedFitting A = pCore 2 A ∧ generalizedFitting B = pCore 2 B ∧
    (Nonempty (A ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (A ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∧
    (Nonempty (B ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (B ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) := by
  obtain ⟨hmem,hpow,hcent⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx
  have hna := triple_not_central x hpow hne ha
  have hnb := triple_not_central x hpow hne hb
  have hgood (A B : Subgroup D) (hg : ChapterF.IsGoldschmidtTriple A B)
      (hxA : x ∈ A) (hc : A ⊓ B ≤ centralizer ({x} : Set D))
      (ht : ∃ a ∈ A, ∃ b ∈ A, x * MulAut.conj a x * MulAut.conj b x = 1)
      (hn : ¬ A ≤ centralizer ({x} : Set D)) : generalizedFitting A = pCore 2 A := by
    by_contra hbad
    have hxQ := triple_involution_local_core hg.quotient_left x hxA hpow ht
    apply hn
    rw [←hg.left_residual_sup_intersection]
    refine sup_le ?_ hc
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hg.local_core_centralizes_residual hbad hxQ) a ha)
  have hc : A ⊓ B ≤ centralizer ({x} : Set D) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (hcent a ha)
  have hA := hgood A B hg hmem.1 hc ha hna
  have hB := hgood B A hg.symm hmem.2 (inf_comm B A ▸ hc) hb hnb
  have hmA : ⁅A,Stellmacher.SectionsFiveToSeven.omegaOneCenter (A ⊓ B)⁆ ≠ ⊥ := by
    intro hh
    exact hna ((commutator_eq_bot_iff_le_centralizer.mp hh).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hx)))
  have hmB : ⁅B,Stellmacher.SectionsFiveToSeven.omegaOneCenter (A ⊓ B)⁆ ≠ ⊥ := by
    intro hh
    exact hnb ((commutator_eq_bot_iff_le_centralizer.mp hh).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hx)))
  exact ⟨hna,hnb,hA,hB,hg.local_models_of_noncentral_omega hcore hA hB hmA hmB⟩

/-- In the outside-core branch both original quotient vertices are S₄ or
C₂ × S₄. The same nontrivial complementary involution moves both of them. -/
theorem point_quotient_local_models_of_complement_not_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hJv : P₁ ⊔ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) ≤
      Gv (markedV d.flag.flag.module)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    A.map q ⊓ B.map q = ((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q →
    markedZ d.flag.flag.module * markedV d.flag.flag.module ∉ J.pCoreIn 2 →
    ∃ x : J, (x : G) = markedZ d.flag.flag.module * markedV d.flag.flag.module ∧
      orderOf (q x) = 2 ∧ q x ∈ omegaOneCenterAmbient (A.map q ⊓ B.map q) ∧
      (¬ A.map q ≤ centralizer ({q x} : Set _)) ∧
      (¬ B.map q ≤ centralizer ({q x} : Set _)) ∧
      generalizedFitting (A.map q) = pCore 2 (A.map q) ∧
      generalizedFitting (B.map q) = pCore 2 (B.map q) ∧
      (Nonempty (A.map q ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (A.map q ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∧
      (Nonempty (B.map q ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (B.map q ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) := by
  intro P₂ J A B q hinter hg hqg hi hout
  let s := d.flag.flag.module
  let R := ChapterB.baumann (T : Subgroup G)
  have hRJ : R ≤ J := hBP.trans le_sup_left
  have hzR := singular_mem_baumann d hH hB hZ hs hz
  have hvR := point_mem_baumann d hH hB hZ hs hz
  have hxR : markedZ s * markedV s ∈ R := R.mul_mem hzR hvR
  let x : J := ⟨markedZ s * markedV s,hRJ hxR⟩
  let z : J := ⟨markedZ s,hRJ hzR⟩
  let v : J := ⟨markedV s,hRJ hvR⟩
  have hxpow : x^2=1 := by
    apply Subtype.ext
    change (s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z) *
      s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))^2=1
    rw [←map_mul,←map_pow]
    have hh : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z *
      Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)^2=1 := by decide +kernel
    rw [hh,map_one]
  have hvcore : v ∈ pCore 2 J := by
    obtain ⟨v',hv',he⟩ := point_mem_overgroup_core d hH hB hZ hs hz hRJ hJv
    exact (Subtype.ext he : v'=v) ▸ hv'
  have hqv : q v = 1 := (QuotientGroup.eq_one_iff v).mpr
    (ChapterF.twoCore_le_primeToThreeCore hvcore)
  have hqz : q z = q x := by
    change q z = q (z*v)
    rw [map_mul,hqv,mul_one]
  have hqxne : q x ≠ 1 := by
    intro he
    have hxX := (QuotientGroup.eq_one_iff x).mp he
    have hxQ : x ∈ pCore 2 J := hg.left_inf_primeToThreeCore ▸
      (show x ∈ A ⊓ pPrimeCore 3 J from ⟨hBP hxR,hxX⟩)
    exact hout (mem_map_of_mem J.subtype hxQ)
  have hqxpow : (q x)^2=1 := by rw [←map_pow,hxpow,map_one]
  have hqxΩ : q x ∈ omegaOneCenterAmbient (A.map q ⊓ B.map q) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨?_,hqxpow,?_⟩
    · rw [hi]
      exact mem_map_of_mem q hxR
    · intro y hy
      rw [hi] at hy
      obtain ⟨y,hy,rfl⟩ := hy
      have hh : y*x=x*y := Subtype.ext
        (mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz) y hy)
      rw [←map_mul,←map_mul,hh]
  have hta : ∃ a ∈ A.map q, ∃ b ∈ A.map q,
      q x * MulAut.conj a (q x) * MulAut.conj b (q x) = 1 := by
    obtain ⟨a,ha,b,hb,ht⟩ := original_point_complement_three_conjugates d hH hB hZ hs hz horiginal
    let a' : J := ⟨a,mem_sup_left ha⟩
    let b' : J := ⟨b,mem_sup_left hb⟩
    refine ⟨q a',mem_map_of_mem q ha,q b',mem_map_of_mem q hb,?_⟩
    have ht' : x * MulAut.conj a' x * MulAut.conj b' x = 1 := Subtype.ext ht
    simpa only [MulAut.conj_apply,map_mul,map_inv,map_one] using congrArg q ht'
  have htb : ∃ a ∈ B.map q, ∃ b ∈ B.map q,
      q x * MulAut.conj a (q x) * MulAut.conj b (q x) = 1 := by
    obtain ⟨c,hc,ht⟩ := exists_residual_triple s
    let c' : J := ⟨c,mem_sup_right (mem_sup_left hc)⟩
    refine ⟨q c',mem_map_of_mem q (mem_sup_left hc),q (c'^2),
      mem_map_of_mem q (P₂.pow_mem (mem_sup_left hc) 2),?_⟩
    have ht' : z * MulAut.conj c' z * MulAut.conj (c'^2) z = v := Subtype.ext ht
    simpa only [MulAut.conj_apply,map_mul,map_inv,hqz,hqv] using congrArg q ht'
  exact ⟨x,rfl,orderOf_eq_prime hqxpow hqxne,hqxΩ,
    triple_local_models hqg hg.primeToThreeCore_quotient_twoCore_eq_bot
      (q x) hqxΩ hqxne hta htb⟩

omit d in
private theorem residual_four_of_local_models
    {D : Type*} [Group D] [Finite D]
    (hm : Nonempty (D ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (D ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) :
    Nonempty (pResidual 2 D ≃* alternatingGroup (Fin 4)) := by
  have e4 : pResidual 2 (Equiv.Perm (Fin 4)) ≃* alternatingGroup (Fin 4) :=
    MulEquiv.subgroupCongr Theory.SpecificGroups.SymmetricFourResidual.residual_eq
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact ⟨((e.subgroupMap (pResidual 2 D)).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e))).trans e4⟩
  · obtain ⟨e⟩ := hm
    exact ⟨(pResidualEquivOfPGroupFactor 2 e
      (IsPGroup.of_card (n := 1) (by simp))).trans e4⟩

/-- The quotient restriction maps the actual two-residual onto A₄,
with kernel precisely its intersection with the original ambient two-core. -/
theorem point_quotient_residual_A4_of_complement_not_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hJv : P₁ ⊔ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) ≤
      Gv (markedV d.flag.flag.module)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    A.map q ⊓ B.map q = ((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q →
    markedZ d.flag.flag.module * markedV d.flag.flag.module ∉ J.pCoreIn 2 →
    (∀ M ∈ ({A,B} : Set (Subgroup J)),
      ∃ f : pResidual 2 M →* alternatingGroup (Fin 4),
        Function.Surjective f ∧
        f.ker = ((pCore 2 J).subgroupOf M).subgroupOf (pResidual 2 M)) := by
  intro P₂ J A B q hi hg hqg hqi hout M hM
  obtain ⟨_,_,_,_,_,_,_,_,hA,hB'⟩ :=
    point_quotient_local_models_of_complement_not_mem_core d hH hB hZ hs hz
      horiginal hBP hJv hi hg hqg hqi hout
  have hm : Nonempty (M.map q ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (M.map q ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) := by
    rcases hM with rfl | rfl
    · exact hA
    · exact hB'
  have hker : (q.subgroupMap M).ker = (pCore 2 J).subgroupOf M := by
    rcases hM with rfl | rfl
    · exact hg.primeToThreeCore_subgroup_kernel A le_rfl
    · exact hg.symm.primeToThreeCore_subgroup_kernel B le_rfl
  obtain ⟨e⟩ := residual_four_of_local_models hm
  let f₀ := q.subgroupMap M
  let R := pResidual 2 M
  let eR : R.map f₀ ≃* pResidual 2 (M.map q) :=
    MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 f₀ (q.subgroupMap_surjective M))
  let f := e.toMonoidHom.comp (eR.toMonoidHom.comp (f₀.subgroupMap R))
  refine ⟨f,e.surjective.comp (eR.surjective.comp (f₀.subgroupMap_surjective R)),?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
    MonoidHom.ker_comp_of_injective _ _ eR.injective,ker_subgroupMap,hker]

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
