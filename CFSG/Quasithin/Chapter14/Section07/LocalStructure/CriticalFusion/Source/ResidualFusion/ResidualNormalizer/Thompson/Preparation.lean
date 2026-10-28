module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Preliminaries
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Theory.GroupTheory.ReducedNormal.Inheritance
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.BaumannNormalizer

/-!
# The reduced module and failure of Thompson factorization in 14.7.67

Write Y = DR₁ and J = J(Y), using the literal section kernel D and point
span E from ResidualNormalizer.Preliminaries. Condition (E) puts N_G(K)
in characteristic two. Normal inheritance and adjoining the normalizing
R₁ give the same conclusion for D and Y. The Sylow-central point therefore
generates a reduced elementary abelian subgroup of Y. We prove that this
full Y-span is exactly the original D-span E.

The kernel C_D(E) lies in T, and Y/D is a two-group, so C_Y(E) is a
two-group. Reducedness gives the reverse containment of O₂(Y), proving
C_Y(E) = O₂(Y) = C_R₁(E). If J(R₁) centralized E, B.2.3(5) and the
assumed Baumann normalizer bound would put D in T. In the contrary branch,
maximum elementary subgroups consequently give an actual FF-offender on
the faithful representation of Y/O₂(Y) on E. This is the counting step
of B.2.4 used in Thompson factorization; no FF conclusion is assumed.
The representation's formula is ambient conjugation on the original E.

Finally, the already proved returning-point argument transports U into
the core of J(Y)R₁, retaining only the earlier U ≤ O₂(K) input. The global
Thompson subgroup is relatively normal in Y and is not a two-group.
Its component exclusion and the solvable W₀ argument remain separate:
this module does not assert that D is a two-group or that J is solvable.

The relative Sylow, D ∩ N_G(L) bound and Baumann control are produced by
qt-14-07-residual-local-control. The earlier U containment is retained for
qt-14-05-terminal-duality / qt-14-07-components to discharge in source
assembly. Maximality of K in L* is unnecessary for the deductions here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071, PDF pp.1087–1088; B.2.3–4 and
B.2.11–15, printed pp.75–78. The reduced-closure proof specializes the
proved Sylow-overgroup inheritance in Theory.GroupTheory.ReducedNormal.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace ResidualNormalizer
/-- The source product DR₁, inside the original ambient group. -/
def Y (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G := D F ⊔ F.Ri L 1
/-- The elementary Thompson subgroup of DR₁. -/
def J (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G :=
  Stellmacher.elementaryAbelianMaxJ (Y L F)

omit [Finite G] in
theorem J_le_Y : J L F ≤ Y L F := sSup_le fun _ hA => hA.1

omit [Finite G] in
/-- J is characteristic in the original product Y = DR₁. -/
theorem Y_normalizes_J : Y L F ≤ normalizer (J L F : Set G) := by
  let A := Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Y L F))
  let : A.Characteristic := Stellmacher.elementaryAbelianMaxJ_top_characteristic
  have h := (Y L F).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (Y L F) A)
  rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective,
    ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

end ResidualNormalizer
private theorem sylowCentral_reduced {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (Z : Subgroup X) (hZP : Z ≤ P)
    (hZc : Z ≤ centralizer (P : Set X)) (he : IsElementaryAbelian 2 Z)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X) :
    IsPReduced 2 (normalClosure (Z : Set X)) := by
  have hZQ : Z ≤ centralizer (pCore 2 X : Set X) :=
    hZc.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  let A := normalClosure (Z : Set X)
  have hAQ : A ≤ pCore 2 X := normalClosure_le_normal (hZQ.trans hc)
  have hAc : A ≤ centralizer (pCore 2 X : Set X) := normalClosure_le_normal hZQ
  let : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp
    (hAc.trans (centralizer_le hAQ))
  let := he
  have hAe : IsElementaryAbelian 2 A := IsElementaryAbelian.normalClosure_of_isMulCommutative Z
  let ZP := Z.subgroupOf (P : Subgroup X)
  have hZPc : ZP ≤ center (P : Subgroup X) := by
    intro z hz
    exact mem_center_iff.mpr fun t => Subtype.ext (hZc hz t t.property)
  let : ZP.Normal := ⟨by
    intro z hz t
    simpa only [(mem_center_iff.mp (hZPc hz)) t, mul_inv_cancel_right] using hz⟩
  have hZPr : IsPReduced 2 ZP := by
    refine ⟨inferInstance, IsElementaryAbelian.subgroupOf hZP, ?_⟩
    have hC : centralizer (ZP : Set (P : Subgroup X)) = ⊤ := by
      apply top_unique
      intro t _ z hz
      exact ((mem_center_iff.mp (hZPc hz)) t).symm
    apply bot_unique
    intro x _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (ZP : Set (P : Subgroup X))) x
    exact (QuotientGroup.eq_one_iff t).mpr (hC.symm ▸ mem_top t)
  have h := hZPr.normalClosure_of_sylow_le P (P : Subgroup X) le_rfl ZP
  rw [map_subgroupOf_eq_of_le hZP] at h
  exact h hAe

namespace Data
open ResidualNormalizer
variable (d : Data T L V F W)

omit [Finite G] in
theorem residual_R_le_sylow : F.Ri L 1 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
    (map_subgroupOf_eq_of_le le_sup_right)

omit [Finite G] in
theorem residual_R_le_H : F.Ri L 1 ≤ F.H :=
  (pCoreIn_le 2 _).trans (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))

omit [Finite G] in
theorem residual_R_normalizes_D : F.Ri L 1 ≤ normalizer (D F : Set G) :=
  (residual_R_le_H.trans (H_normalizes_K F)).trans normalizer_K_normalizes_D

omit [Finite G] in
theorem residual_Y_le_normalizer_K : Y L F ≤ normalizer (K F : Set G) :=
  sup_le D_le_normalizer (residual_R_le_H.trans (H_normalizes_K F))

include d
/-- Characteristic two of the normalizer follows from the genuine local family
and condition (E); maximality in L* is not needed for this preliminary. -/
theorem residual_normalizer_characteristicTwo : HasCharacteristicTwo (normalizer (K F : Set G)) := by
  have hK := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (d.counterexample.qtke.evenCharacteristic T) d.K_mem_localFamily
  have hne : pCore 2 (K F) ≠ ⊥ := by
    intro he
    have hKb : K F = ⊥ := by
      apply bot_unique
      intro k hk
      have hc : (⟨k, hk⟩ : K F) ∈ centralizer (pCore 2 (K F) : Set (K F)) := by
        rw [he]
        intro y hy
        rw [mem_bot.mp hy]
        simp
      have hm := hK hc
      rw [he] at hm
      exact congrArg Subtype.val (mem_bot.mp hm)
    exact d.component.ne_bot (by rw [hKb, bot_subgroupOf])
  obtain ⟨N, hN, hKN⟩ := exists_twoLocal_overgroup_normalizer (K F) (pCore 2 (K F))
    hne pCore_isPGroup
  have hTN : (T : Subgroup G) ≤ normalizer (K F : Set G) :=
    (F.invariant 1).trans (H_normalizes_K F)
  have hNc := Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
    (d.counterexample.qtke.evenCharacteristic T) hN (hTN.trans hKN))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hKN)).mp
    (centralizer_pCore_le_of_sylow_le (T.subtype (hTN.trans hKN))
      ((normalizer (K F : Set G)).subgroupOf N) (fun x hx => hTN hx) hNc)

/-- The section kernel is relatively normal in N_G(K), hence has characteristic two. -/
theorem residual_D_characteristicTwo : HasCharacteristicTwo (D F) := by
  let N := normalizer (K F : Set G)
  let : ((D F).subgroupOf N).Normal :=
    normal_subgroupOf_of_le_normalizer normalizer_K_normalizes_D
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe D_le_normalizer)).mp
    (normal_core_selfCentralizing d.residual_normalizer_characteristicTwo ((D F).subgroupOf N))

/-- Adjoining the normalizing two-group R₁ preserves characteristic two. -/
theorem residual_Y_characteristicTwo : HasCharacteristicTwo (Y L F) :=
  centralizer_pCore_sup_le 2 _ _ d.residual_D_characteristicTwo
    (T.isPGroup'.to_le residual_R_le_sylow) residual_R_normalizes_D

/-- R₁ centralizes the original point and normalizes D, so it preserves its D-span. -/
theorem residual_R_normalizes_E : F.Ri L 1 ≤ normalizer (E F : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro r hr x ⟨a, ha, z, hz, rfl⟩
  have hc := mem_centralizer_iff.mp (d.H_centralizes_point (residual_R_le_H hr)) z hz
  have hfix : r * z * r⁻¹ = z := by rw [← hc]; simp
  apply Subgroup.subset_closure
  refine ⟨r * a * r⁻¹, le_normalizer_iff.mp residual_R_normalizes_D r hr a ha,
    z, hz, ?_⟩
  calc
    (r * a * r⁻¹) * z * (r * a * r⁻¹)⁻¹ =
        r * a * (r⁻¹ * z * r) * a⁻¹ * r⁻¹ := by group
    _ = r * (a * z * a⁻¹) * r⁻¹ := by
      have hi : r⁻¹ * z * r = z := by
        have := congrArg (fun t : G => r⁻¹ * t * r) hfix
        simpa [mul_assoc] using this.symm
      rw [hi]
      group

theorem residual_Y_normalizes_E : Y L F ≤ normalizer (E F : Set G) :=
  sup_le D_normalizes_E d.residual_R_normalizes_E

/-- The same E is the full DR₁-conjugate span, with the original point unchanged. -/
theorem residualSpan_eq_Y_span : E F = conjugateSpanBy (F.Vi 1) (Y L F) :=
  le_antisymm (conjugateSpanBy_mono le_rfl le_sup_left)
    (conjugateSpanBy_le point_le_E d.residual_Y_normalizes_E)

/-- The point is Sylow-central in the genuine relative Sylow R₁. -/
theorem residual_point_le_R : F.Vi 1 ≤ F.Ri L 1 := by
  apply le_pCoreIn_of_normalizes d.point_twoGroup
  · exact ((F.le_seed 1).trans d.natural.chosen.le_sylow).trans le_sup_right
  · exact sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

/-- B.2.14's reducedness conclusion for the literal E in DR₁. Both its
normality and elementary abelianity are derived, not inputs. -/
theorem residualSpan_reduced
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    IsPReduced 2 ((E F).subgroupOf (Y L F)) := by
  obtain ⟨P, hP⟩ := hSylow
  have hP' : (P : Subgroup (Y L F)) = (F.Ri L 1).subgroupOf (Y L F) := by
    apply map_injective (Y L F).subtype_injective
    rw [hP]
    exact (map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ Y L F from le_sup_right)).symm
  have hpoint : F.Vi 1 ≤ Y L F := d.point_le_D.trans le_sup_left
  have hZP : (F.Vi 1).subgroupOf (Y L F) ≤ P := by
    rw [hP']
    exact comap_mono d.residual_point_le_R
  have hZc : (F.Vi 1).subgroupOf (Y L F) ≤ centralizer (P : Set (Y L F)) := by
    intro z hz r hr
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (d.H_centralizes_point
      (residual_R_le_H (hP ▸ mem_map_of_mem (Y L F).subtype hr))) z hz).symm
  let := d.U_elementary
  let : IsElementaryAbelian 2 (F.Vi 1) :=
    IsElementaryAbelian.of_le d.conjugationSection.kernel_le
  have he : IsElementaryAbelian 2 ((F.Vi 1).subgroupOf (Y L F)) :=
    IsElementaryAbelian.subgroupOf hpoint
  have h := sylowCentral_reduced P ((F.Vi 1).subgroupOf (Y L F)) hZP hZc he
    d.residual_Y_characteristicTwo
  rwa [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hpoint,
    ← d.residualSpan_eq_Y_span] at h

/-- The source centralizer is a two-group: its intersection with D lies in T,
and its quotient by that intersection is an image of the two-group Y/D. -/
theorem residualSpan_centralizer_isPGroup :
    IsPGroup 2 (Y L F ⊓ centralizer (E F : Set G) : Subgroup G) := by
  let Y₁ := Y L F
  let DN := (D F).subgroupOf Y₁
  let : DN.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (D F).le_normalizer residual_R_normalizes_D)
  have hgen : DN ⊔ (F.Ri L 1).subgroupOf Y₁ = ⊤ := by
    apply map_injective Y₁.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D F ≤ Y₁ from le_sup_left),
      map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ Y₁ from le_sup_right), ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hquot : IsPGroup 2 (Y₁ ⧸ DN) :=
    isPGroup_quotient_of_sup_eq_top DN _
      (T.isPGroup'.to_le residual_R_le_sylow).comap_subtype hgen
  intro c
  let x : Y₁ := ⟨c, c.property.1⟩
  obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' DN x)
  have hxD : (c : G) ^ 2 ^ n ∈ D F := by
    have hh : x ^ 2 ^ n ∈ DN := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' DN (x ^ 2 ^ n) = 1
      rwa [map_pow]
    exact hh
  have hxT : (c : G) ^ 2 ^ n ∈ (T : Subgroup G) :=
    d.D_inf_centralizer_residualSpan_le_sylow
      ⟨hxD, (centralizer (E F : Set G)).pow_mem c.property.2 _⟩
  obtain ⟨m, hm⟩ := T.isPGroup' ⟨_, hxT⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  change (c : G) ^ 2 ^ (n + m) = 1
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

/-- The literal centralizer equality C_DR₁(E) = O₂(DR₁). -/
theorem residualSpan_centralizer_eq_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    Y L F ⊓ centralizer (E F : Set G) = (Y L F).pCoreIn 2 := by
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes d.residualSpan_centralizer_isPGroup inf_le_left
      ((le_inf (Y L F).le_normalizer
        (d.residual_Y_normalizes_E.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)
  · have hc := le_centralizer_iff.mp (d.residualSpan_reduced hSylow).le_centralizer_pCore
    rintro x ⟨q, hq, rfl⟩
    refine ⟨q.property, ?_⟩
    intro e he
    exact congrArg Subtype.val (hc hq ⟨e, d.residualSpan_le_D.trans le_sup_left he⟩ he)

/-- The core is precisely C_R₁(E), with the actual relative Sylow. -/
theorem residualSpan_sylow_centralizer_eq_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    F.Ri L 1 ⊓ centralizer (E F : Set G) = (Y L F).pCoreIn 2 := by
  have he := d.residualSpan_centralizer_eq_core hSylow
  obtain ⟨P, hP⟩ := hSylow
  apply le_antisymm ((inf_le_inf_right _ (show F.Ri L 1 ≤ Y L F from le_sup_right)).trans he.le)
  exact le_inf ((pCoreIn_le_sylow _ P).trans_eq hP) (he.symm.le.trans inf_le_right)

/-- The B.2.14 module lies in the specified R₁, not an arbitrary conjugate Sylow. -/
theorem residualSpan_le_R
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) : E F ≤ F.Ri L 1 := by
  have h := map_mono (f := (Y L F).subtype) (d.residualSpan_reduced hSylow).le_pCore
  rw [map_subgroupOf_eq_of_le (show E F ≤ Y L F from d.residualSpan_le_D.trans le_sup_left)] at h
  obtain ⟨P, hP⟩ := hSylow
  exact h.trans ((pCoreIn_le_sylow _ P).trans_eq hP)

/-- Baumann control excludes J(R₁)-centralization in the non-two-group branch. -/
theorem residual_sylowThompson_not_centralizes
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (F.Ri L 1) ≤ centralizer (E F : Set G) := by
  intro hJ
  let := (d.residualSpan_reduced hSylow).elementary
  have hem := IsElementaryAbelian.map (p := 2) (A := (E F).subgroupOf (Y L F)) (Y L F).subtype
  rw [map_subgroupOf_eq_of_le (show E F ≤ Y L F from d.residualSpan_le_D.trans le_sup_left)] at hem
  let := hem
  have hb := ChapterB.lemma_B_2_3_5 (F.Ri L 1) (E F) (d.residualSpan_le_R hSylow) hJ
  rw [d.residualSpan_sylow_centralizer_eq_core hSylow] at hb
  have hYB : Y L F ≤ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) := by
    rw [hb]
    exact ((Y L F).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (Y L F) (pCore 2 (Y L F)))).trans
      (Stellmacher.normalizer_le_normalizer_baumann _)
  exact hD (T.isPGroup'.to_le ((le_inf le_rfl
    (le_sup_left.trans (hYB.trans hBaum))).trans hDM))

/-- Intrinsic form of the centralizer equality, for the literal quotient action. -/
theorem residual_internal_centralizer_eq_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    centralizer ((E F).subgroupOf (Y L F) : Set (Y L F)) = pCore 2 (Y L F) := by
  apply le_antisymm
  · intro x hx
    have hc : x.val ∈ Y L F ⊓ centralizer (E F : Set G) := by
      refine ⟨x.property, ?_⟩
      intro e he
      exact congrArg Subtype.val (hx ⟨e, d.residualSpan_le_D.trans le_sup_left he⟩ he)
    rw [d.residualSpan_centralizer_eq_core hSylow] at hc
    exact (mem_map_iff_mem (Y L F).subtype_injective).mp hc
  · exact le_centralizer_iff.mp (d.residualSpan_reduced hSylow).le_centralizer_pCore

/-- The genuine binary conjugation action of DR₁/O₂(DR₁) on E. -/
def residualRepresentation
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    let := (d.residualSpan_reduced hSylow).elementary
    Representation (ZMod 2) (Y L F ⧸ pCore 2 (Y L F))
      (Additive ((E F).subgroupOf (Y L F))) := by
  let := (d.residualSpan_reduced hSylow).normal
  let := (d.residualSpan_reduced hSylow).elementary
  exact NormalElementaryQuotient.representation ((E F).subgroupOf (Y L F))
    (QuotientGroup.mk' (pCore 2 (Y L F))) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (d.residual_internal_centralizer_eq_core hSylow).symm)

theorem residualRepresentation_faithful
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    Function.Injective (d.residualRepresentation hSylow) := by
  let := (d.residualSpan_reduced hSylow).normal
  let := (d.residualSpan_reduced hSylow).elementary
  exact NormalElementaryQuotient.representation_injective _ _ _ _

/-- On quotient representatives, the action is literal ambient conjugation. -/
theorem residualRepresentation_apply
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (a : Y L F) (e : Additive ((E F).subgroupOf (Y L F))) :
    letI := (d.residualSpan_reduced hSylow).elementary
    (((d.residualRepresentation hSylow (QuotientGroup.mk' (pCore 2 (Y L F)) a) e).toMul :
      Y L F) : G) = (a : G) * ((e.toMul : Y L F) : G) * (a : G)⁻¹ := by
  let := (d.residualSpan_reduced hSylow).normal
  let := (d.residualSpan_reduced hSylow).elementary
  exact congrArg (Y L F).subtype (NormalElementaryQuotient.representation_apply
    ((E F).subgroupOf (Y L F)) (QuotientGroup.mk' (pCore 2 (Y L F)))
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
      (d.residual_internal_centralizer_eq_core hSylow).symm) a e)

/-- Thompson factorization fails on the actual quotient action. The offender
is constructed from a maximum elementary subgroup of the specified R₁. -/
theorem residualRepresentation_isFF
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Representation.BinaryOffender.IsFFModule (d.residualRepresentation hSylow) := by
  let := (d.residualSpan_reduced hSylow).normal
  let := (d.residualSpan_reduced hSylow).elementary
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le
    ((E F).subgroupOf (Y L F)) (QuotientGroup.mk' (pCore 2 (Y L F)))
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
      (d.residual_internal_centralizer_eq_core hSylow).symm)
    ((F.Ri L 1).subgroupOf (Y L F)) (comap_mono (d.residualSpan_le_R hSylow))
  intro hJ
  rw [QuotientGroup.ker_mk'] at hJ
  have hm := map_mono (f := (Y L F).subtype) hJ
  rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective,
    map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ Y L F from le_sup_right)] at hm
  exact d.residual_sylowThompson_not_centralizes hDM hSylow hBaum hD
    (hm.trans ((d.residualSpan_centralizer_eq_core hSylow).symm.le.trans inf_le_right))

omit d [Finite G] [AddCommGroup W] [Module (ZMod 2) W] in
/-- The core of K lies in the section kernel, with relative normality retained. -/
theorem residual_K_core_le_D : (K F).pCoreIn 2 ≤ D F := by
  apply (Chapter4.le_sectionCentralizer_iff _ _).mpr
  refine ⟨(pCoreIn_le 2 _).trans (K F).le_normalizer, ?_⟩
  exact le_normalizer_iff_commutator_le_left.mp
    ((K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))))

/-- The remaining core transport works in every intermediate overgroup of R₁;
in particular take A = J(DR₁)R₁ in the solvable branch of 14.7.31. -/
theorem returning_point_conjugate_U_le_intermediate_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (A : Subgroup G) (hRA : F.Ri L 1 ≤ A) (hAY : A ≤ Y L F)
    (hU : F.U ≤ (K F).pCoreIn 2) (g : G) (hg : conjugate (F.Vi 1) g ≤ E F) :
    conjugate F.U g ≤ A.pCoreIn 2 := by
  have hn : Y L F ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
    residual_Y_le_normalizer_K.trans
      (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))
  have hQY : (K F).pCoreIn 2 ≤ (Y L F).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (residual_K_core_le_D.trans le_sup_left) hn
  obtain ⟨P, hP⟩ := hSylow
  have hQA := (hQY.trans ((pCoreIn_le_sylow _ P).trans_eq hP)).trans hRA
  exact (d.returning_point_conjugate_U_le_core g hg hU).trans
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hQA (hAY.trans hn))

omit d [AddCommGroup W] [Module (ZMod 2) W] in
/-- The elementary Thompson subgroup of the relative Sylow is contained in J(DR₁). -/
theorem residual_sylowThompson_le_J
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    Stellmacher.elementaryAbelianMaxJ (F.Ri L 1) ≤ J L F := by
  obtain ⟨P, hP⟩ := hSylow
  have h := map_mono (f := (Y L F).subtype) (Stellmacher.elementaryAbelianMaxJ_sylow_le_top P)
  rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective,
    ← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective,
    hP, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

/-- In the contrary branch the global Thompson subgroup is not a two-group. -/
theorem residual_thompson_not_isPGroup
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) : ¬ IsPGroup 2 (J L F) := by
  intro hp
  have hJQ := le_pCoreIn_of_normalizes hp J_le_Y Y_normalizes_J
  exact d.residual_sylowThompson_not_centralizes hDM hSylow hBaum hD
    ((residual_sylowThompson_le_J hSylow).trans
      (hJQ.trans ((d.residualSpan_centralizer_eq_core hSylow).symm.le.trans inf_le_right)))

/-- The actual returning-point premise for 14.7.31(2), with Y there equal
to J(DR₁)R₁. Only the earlier U ≤ O₂(K) assertion remains an explicit input. -/
theorem returning_point_conjugate_U_le_thompson_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hU : F.U ≤ (K F).pCoreIn 2) (g : G) (hg : conjugate (F.Vi 1) g ≤ E F) :
    conjugate F.U g ≤ (J L F ⊔ F.Ri L 1).pCoreIn 2 :=
  d.returning_point_conjugate_U_le_intermediate_core hSylow _ le_sup_right
    (sup_le J_le_Y le_sup_right) hU g hg

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
