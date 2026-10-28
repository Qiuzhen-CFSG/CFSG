module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.Diagram
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Fixing the actual binary component through the faithful action

The parabolic M ∩ X has an S₄ quotient image in X/O₂(X). Its restriction
to the original NI/C_NI(V) action has two-group kernel, because the
centralizer intersection lies in the original Sylow subgroup T. Its image
is therefore all of S₃.

If s ∈ S moved X, distinct C-components of I would commute modulo O₂(I).
The faithful action kills this normal two-subgroup, forcing the two full
S₃ images to commute. This contradiction fixes X under S, and the source
component-orbit theorem gives normality relative to I. Minimality and the
actual cubic-factor results are then applied on the original subgroups.
The last theorem derives the printed prime-to-three residual equality
from the earlier 3′-centralizer conclusion.

The preceding no-χ/C.1.34 reduction supplies X outside Mc. Its producer
is qt-e-152-char2-block-exclusion; the faithful action and earlier source
inputs are discharged by qt-e-152-char2-component-models and
qt-e-152-plane-uniqueness. The 15.2.21--22 input owner is
qt-e-152-char2-small-actions. Complementary-factor identification and
the final contradiction remain obligations of the linear-three branch.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private theorem linearStabilizer_eq_parabolic {F : Type*} [Field F]
    (W : Submodule F (Fin 3 → F)) : linearStabilizer W = Matrix.HigherLinear.parabolicSL W := by
  ext g
  change Matrix.SpecialLinearGroup.toLin' g ∈ MulAction.stabilizer _ W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

private theorem binary_parabolic_symmetricFour {A : Type*} [Group A]
    {F : Type} [Field F] [Finite F] (P : Subgroup A)
    (hp : IsLinearMaximalParabolic P 3 F) (hF : Nat.card F = 2) :
    Nonempty (P ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨e,W,hn,ht,he⟩ := hp
  let eP := (e.subgroupMap P).trans (MulEquiv.subgroupCongr he)
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let es := Atlas.fieldEquivSL 3 ef
  have hpoint : (Matrix.PSL3.LinearThree.pointParabolicSL F).map es.toMonoidHom =
      Matrix.PSL3Two.pointParabolicSL := by
    ext g
    obtain ⟨g,rfl⟩ := es.surjective g
    rw [show es g ∈ (Matrix.PSL3.LinearThree.pointParabolicSL F).map es.toMonoidHom ↔ g ∈ Matrix.PSL3.LinearThree.pointParabolicSL F from mem_map_iff_mem es.injective,Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff,
      Matrix.PSL3Two.mem_pointParabolicSL_iff]
    change (g.val 1 0 = 0 ∧ g.val 2 0 = 0) ↔ (ef (g.val 1 0) = 0 ∧ ef (g.val 2 0) = 0)
    simp
  have hline : (Matrix.PSL3.LinearThree.lineParabolicSL F).map es.toMonoidHom =
      Matrix.PSL3Two.lineParabolicSL := by
    ext g
    obtain ⟨g,rfl⟩ := es.surjective g
    rw [show es g ∈ (Matrix.PSL3.LinearThree.lineParabolicSL F).map es.toMonoidHom ↔ g ∈ Matrix.PSL3.LinearThree.lineParabolicSL F from mem_map_iff_mem es.injective,Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff,
      Matrix.PSL3Two.mem_lineParabolicSL_iff]
    change (g.val 2 0 = 0 ∧ g.val 2 1 = 0) ↔ (ef (g.val 2 0) = 0 ∧ ef (g.val 2 1) = 0)
    simp
  let ew := (MulEquiv.subgroupCongr (linearStabilizer_eq_parabolic W))
  rcases Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv W hn ht with ha | ha
  · obtain ⟨a⟩ := ha
    exact ⟨eP.trans (ew.trans (a.trans ((es.subgroupMap _).trans
      ((MulEquiv.subgroupCongr hpoint).trans Matrix.PSL3Two.MarkedAutomorphisms.pointEquivSymmetric))))⟩
  · obtain ⟨a⟩ := ha
    exact ⟨eP.trans (ew.trans (a.trans ((es.subgroupMap _).trans
      ((MulEquiv.subgroupCongr hline).trans Matrix.PSL3Two.MarkedAutomorphisms.lineEquivSymmetric))))⟩

/-- The literal M ∩ X has the binary parabolic S₄ as its quotient image. -/
theorem Branch.binary_marked_parabolic_model
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F) :
    Nonempty ((((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≃*
      Equiv.Perm (Fin 4)) :=
  binary_parabolic_symmetricFour _ b.core_parabolic (by simpa using b.field_card)


include d in
/-- The actual parabolic has full image in the faithful S₃ action on V. -/
theorem Branch.binary_parabolic_action_full
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    ((M ⊓ X).subgroupOf (M ⊓ I)).map f = ⊤ := by
  let NI := M ⊓ I
  let A := (M ⊓ X).subgroupOf NI
  let B := (M ⊓ X).subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  have hMX : M ⊓ X ≤ NI := inf_le_inf_left M b.input.component.1
  obtain ⟨eP⟩ := b.binary_marked_parabolic_model
  have hkq : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hkq
  let eS := Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv eP
  let eAB := (subgroupOfEquivOfLe hMX).trans (subgroupOfEquivOfLe (inf_le_right : M ⊓ X ≤ X)).symm
  have hcard : Nat.card (A ⧸ pCore 2 A) = 6 := by
    let eq := QuotientGroup.congr (pCore 2 A) (pCore 2 B) eAB (pCore_map_iso 2 eAB)
    rw [Nat.card_congr (eq.trans (eB.trans eS)).toEquiv,Nat.card_eq_fintype_card]
    decide
  have hkf : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    apply (T.isPGroup'.comap_subtype.comap_subtype).to_le
    intro x hx
    have hxV : (x.val.val : G) ∈ centralizer (V : Set G) := by
      change x.val ∈ f.ker at hx
      rw [hker] at hx
      exact hx
    have hxZ := centralizer_le d.geometry.plane_le hxV
    have hxH : (x.val.val : G) ∈ H := by
      have hh : (x.val.val : G) ∈ X ⊓ centralizer (ZS : Set G) := ⟨x.property.2,hxZ⟩
      rw [(b.binary_centralizer_eq_local d hI hout).2] at hh
      exact hh.1
    change (x.val.val : G) ∈ (T : Subgroup G)
    rw [← local_intersection_eq_sylow d]
    exact ⟨x.property.1,hxH⟩
  let ef := (f.subgroupMap A).pCoreQuotientEquiv (f.subgroupMap_surjective A) hkf
  have hl : 6 ≤ Nat.card (A.map f) := by
    rw [Nat.card_congr ef.toEquiv] at hcard
    rw [← hcard]
    exact Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (pCore 2 (A.map f)))
  change A.map f = ⊤
  apply Subgroup.eq_top_of_card_eq
  have hu := (A.map f).card_le_card_group
  have hs : Nat.card (Equiv.Perm (Fin 3)) = 6 := by rw [Nat.card_eq_fintype_card]; decide
  omega


private theorem symmetric_three_core_eq_bot : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have hh := ker_eq_twoCore_of_surjective_perm_three
    (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id (by
      simp only [MonoidHom.ker_id]
      exact IsPGroup.of_subsingleton 2 _)
  simpa only [MonoidHom.ker_id] using hh.symm

include d in
/-- A moved component would give two commuting full S₃ images. Hence S fixes X. -/
theorem Branch.binary_sylow_normalizes
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    planeSylow T ZS ≤ normalizer (X : Set G) := by
  let NI := M ⊓ I
  let A := (M ⊓ X).subgroupOf NI
  let j : NI →* I := inclusion inf_le_right
  have hj : Function.Injective j := inclusion_injective inf_le_right
  have hfull : A.map f = ⊤ := b.binary_parabolic_action_full d hI hout f hker
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hfull]
    rintro x ⟨y,_,rfl⟩
    exact ⟨y,rfl⟩
  let N := (pCore 2 I).comap j
  have hN : IsPGroup 2 N := pCore_isPGroup.comap_of_injective j hj
  have hNk : N ≤ f.ker := by
    have hn : (N.map f).Normal := (inferInstance : N.Normal).map f hf
    have hp : N.map f ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨hn,hN.map f⟩
    rw [symmetric_three_core_eq_bot] at hp
    exact (Subgroup.map_eq_bot_iff _).mp (eq_bot_iff.mpr hp)
  have hs := Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  intro s hsS
  have hsI : s ∈ I := ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right) hsS
  have hsM : s ∈ M := hsource.maximal.1.2 hsS.1
  let sn : NI := ⟨s,hsM,hsI⟩
  let si : I := ⟨s,hsI⟩
  let B := X.subgroupOf I
  have he : B.conjBy si = B := by
    by_contra hne
    have hc := ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two hQ
      b.input.component.2 (b.input.component.2.map_equiv (MulAut.conj si)) (Ne.symm hne)
    have hAB : A.map j ≤ B := by
      rintro x ⟨y,hy,rfl⟩
      exact hy.2
    have hac : (A.conjBy sn).map j ≤ B.conjBy si := by
      rw [map_conjBy_hom]
      exact map_mono hAB
    have hcomm : ⁅A,A.conjBy sn⁆ ≤ N := by
      apply map_le_iff_le_comap.mp
      rw [map_commutator]
      exact (commutator_mono hAB hac).trans (hc.1.trans hc.2)
    have himg : (A.conjBy sn).map f = ⊤ := by
      rw [map_conjBy_hom,hfull]
      exact map_top_of_surjective _ (MulAut.conj (f sn)).surjective
    have hbot : ⁅(⊤ : Subgroup (Equiv.Perm (Fin 3))),(⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ = ⊥ := by
      calc
        ⁅(⊤ : Subgroup (Equiv.Perm (Fin 3))),(⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ =
            ⁅A.map f,(A.conjBy sn).map f⁆ := by rw [hfull,himg]
        _ = ⁅A,A.conjBy sn⁆.map f := (map_commutator _ _ _).symm
        _ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (hcomm.trans hNk)
    have hcommute := commutator_eq_bot_iff_le_centralizer.mp hbot
    have hab := mem_centralizer_iff.mp (hcommute (mem_top (Equiv.swap (0 : Fin 3) 1)))
      (Equiv.swap (1 : Fin 3) 2) (mem_top _)
    exact (by decide : Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 ≠
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) hab
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh := congrArg (map I.subtype) he
  rw [map_conjBy_hom,map_subgroupOf_eq_of_le b.input.component.1] at hh
  exact hh

include d in
/-- The faithful action discharges the component-orbit premise of relative normality. -/
theorem Branch.binary_normal_of_action
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    I ≤ normalizer (X : Set G) :=
  normal_of_orbit_eq d hI b.input.component
    (le_antisymm (conjugateSpanBy_le le_rfl (b.binary_sylow_normalizes d hI hout f hker))
      (le_conjugateSpanBy X (planeSylow T ZS)))


include d in
/-- Minimality gives I = MᵢX after the action has fixed the component. -/
theorem Branch.binary_normal_join_of_action
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : MinimalPlaneEscape Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    I ≤ normalizer (X : Set G) ∧ (Mc ⊓ I) ⊔ X = I :=
  ⟨b.binary_normal_of_action d hI.1 hout f hker,
    minimal_join d hI b.input.component.1 hout⟩

include d in
/-- The faithful action supplies relative normality in the actual cubic-factor
consumer. The remaining 15.2.21 identification of the complementary factor is
a separate source obligation. -/
theorem Branch.binary_factor_data_of_action
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    let K := (pResidual 2 H).map H.subtype
    let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
    L ≤ K ∧ IsPPerfect 2 L ∧ Nat.card (L ⧸ pCore 2 L) = 3 ∧
      planeSylow T ZS ≤ normalizer (L : Set G) ∧
      Mc ⊓ I ≤ normalizer (L : Set G) ∧
      ¬ IsSmallActionIrreducible (planeSylow T ZS) K :=
  b.binary_factor_source_data d hI hout (b.binary_normal_of_action d hI hout f hker)

include d in
/-- The original branch has degree one, is normal in I, and generates I with Mᵢ.
The preliminary no-χ/C.1.34 reduction supplies the displayed outside premise
after the degree reduction; the action is the earlier NI/C_NI(V) identification. -/
theorem Branch.degree_normal_join_of_action
    {n : ℕ} {F : Type} [Field F] [Finite F] (b : Branch M I X n F)
    (hI : MinimalPlaneEscape Mc ZS I) (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    n = 1 ∧ I ≤ normalizer (X : Set G) ∧ (Mc ⊓ I) ⊔ X = I := by
  have hn := b.degree_eq_one d hI.1
  subst n
  exact ⟨rfl,b.binary_normal_join_of_action d hI (hout rfl) f hker⟩


include d in
/-- The 3′-centralizer conclusion of 15.2.21(2), together with the faithful
action, gives the printed equality O^{3′}(NI) = O^{3′}(M ∩ X). -/
theorem Branch.binary_cubic_residual_eq_of_action
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hcentral : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G))) :
    (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype =
      (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype := by
  let NI := M ⊓ I
  let A := (M ⊓ X).subgroupOf NI
  let C := M ⊓ centralizer (V : Set G)
  have hIX := b.binary_normal_of_action d hI hout f hker
  have hnorm : NI ≤ normalizer (M ⊓ X : Set G) :=
    (le_inf (inf_le_left.trans M.le_normalizer)
      (inf_le_right.trans hIX)).trans inf_normalizer_le_normalizer_inf
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hCNI : C ≤ NI := le_inf inf_le_left (inf_le_right.trans (d.module_centralizer_le hI))
  have he : f.ker = C.subgroupOf NI := by
    rw [hker]
    ext x
    change (x.val ∈ centralizer (V : Set G)) ↔ x.val ∈ M ∧ x.val ∈ centralizer (V : Set G)
    exact ⟨fun hx => ⟨x.property.1,hx⟩,And.right⟩
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [he,Nat.card_congr (subgroupOfEquivOfLe hCNI).toEquiv]
    have hh := primeToResidual_index_coprime (G := C) 3
    change primeToResidual 3 C = ⊥ at hcentral
    rwa [hcentral,index_bot] at hh
  have hfull : A.map f = ⊤ := b.binary_parabolic_action_full d hI hout f hker
  have hgen : A ⊔ f.ker = ⊤ := by
    have hh := congrArg (comap f) hfull
    simpa only [comap_map_eq,comap_top] using hh
  have hd : A.index ∣ Nat.card f.ker := by
    have hh := relIndex_sup_right f.ker A
    rw [sup_comm,hgen,relIndex_top_right] at hh
    rw [hh]
    exact relIndex_dvd_card _ _
  exact intersection_cubic_residual_eq_of_coprime_index b.input.component.1 hIX
    (hcop.coprime_dvd_right hd)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
