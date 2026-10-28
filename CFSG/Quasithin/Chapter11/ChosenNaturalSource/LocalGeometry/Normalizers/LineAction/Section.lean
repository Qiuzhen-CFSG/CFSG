module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.Frattini
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership

/-!
# Components and Sylows of the original line section kernel

Under C_G(U) ≤ N_G(L), the literal residual A = N_L(U)^infinity is
normal in C_G(U). Its preceding local-family membership therefore makes it
a C-component of N_G(U). The source orbit bound and T-invariance make it
normal there. On A⋁T, the actual conjugation action on A/O₂(A) has kernel
O₂(A⋁T), because the quotient is centerless. Intersecting with C_G(U) and
using the preceding radical-centralization identity identifies T intersect
lineSectionKernel with the original R. Normality then makes R Sylow in that
literal kernel. No alternative quotient or ambient normality is used.

The retained inputs are preceding rank-one flag identities: the PSL₂(q)
quotient and centralization of U by A and R. They belong to the flag/Cartan
producer, not the new component and Sylow assertions proved here.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.3(2), printed p.769, using 1.2.1(3) and the opening of 11.1.
-/

open Subgroup
open CFSG.Quasithin.Chapter12.Section02
set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- A T-invariant component of the line normalizer is normal there. -/
theorem chosen_first_normalized_of_component
    (hA : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) (f.Li 0)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) := by
  let Y := normalizer (f.Vi 0 : Set G)
  let A := (f.Li 0).subgroupOf Y
  let P : Sylow 2 Y := T.subtype (show (T : Subgroup G) ≤ Y from f.invariant 0)
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    (pCore 2 Y) pCore_isPGroup
  have hPA : (P : Subgroup Y) ≤ normalizer (A : Set Y) := by
    rw [← subgroupOf_normalizer_eq hA.1]
    exact comap_mono (f.sylow_normalizes_Li 0)
  have hn : A.Normal := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hA.2 with hn | hi
    · exact hn
    · change (normalizer (A : Set Y)).index = 2 at hi
      exact (P.not_dvd_index (by simpa only [hi] using index_dvd_of_le hPA)).elim
  exact (normal_subgroupOf_iff_le_normalizer hA.1).mp hn

/-- Restrict local component membership to the residual itself, then use its
normality in the line centralizer and that centralizer's normality in Y. -/
theorem chosen_first_component_of_centralizer_le
    (hlocal : f.Li 0 ∈ Chapter1.L G T)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    Source.ComponentIn (normalizer (f.Vi 0 : Set G)) (f.Li 0) := by
  let Y := normalizer (f.Vi 0 : Set G)
  let C := centralizer (f.Vi 0 : Set G)
  let A := f.Li 0
  have hCY : C ≤ Y := Subgroup.centralizer_le_normalizer _
  have hAY : A ≤ Y := hfix.trans hCY
  have hCA : C ≤ normalizer (A : Set G) :=
    ((le_inf hC (hCY.trans Y.le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have htop : (⊤ : Subgroup A).IsCComponent := by
    have hh := hlocal.1.subgroupOf_of_le (K := A) le_rfl le_sup_left
    change (A.subgroupOf A).IsCComponent at hh
    simpa only [subgroupOf_self] using hh
  have hAC : (A.subgroupOf C).IsCComponent := by
    let e : A ≃* A.subgroupOf C := (subgroupOfEquivOfLe hfix).symm
    have ht : (⊤ : Subgroup (A.subgroupOf C)).IsCComponent := by
      have he : (⊤ : Subgroup A).map e.toMonoidHom = ⊤ :=
        (MonoidHom.range_eq_map e.toMonoidHom).symm.trans
          (MonoidHom.range_eq_top.mpr e.surjective)
      exact he ▸ htop.map_equiv e
    have hn : (A.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hfix).mpr hCA
    simpa only [← MonoidHom.range_eq_map, range_subtype] using ht.map_subtype hn.isSubnormal
  let e : C ≃* C.subgroupOf Y := (subgroupOfEquivOfLe hCY).symm
  have hmap : (A.subgroupOf C).map e.toMonoidHom =
      (A.subgroupOf Y).subgroupOf (C.subgroupOf Y) := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact hb
    · intro ha
      exact ⟨⟨a.val.val,a.property⟩,ha,rfl⟩
  have hcomp := hmap ▸ hAC.map_equiv e
  have hnC : (C.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCY).mpr (normalizer_le_normalizer_centralizer _)
  refine ⟨hAY, ?_⟩
  have hAYC : A.subgroupOf Y ≤ C.subgroupOf Y := comap_mono hfix
  simpa only [map_subgroupOf_eq_of_le hAYC] using hcomp.map_subtype hnC.isSubnormal

/-- Identify the section centralizer inside the original Sylow. The action
is exactly conjugation on A/O₂(A), not on a replacement quotient. -/
theorem chosen_section_intersection
    (hc : center (f.Li 0 ⧸ pCore 2 (f.Li 0)) = ⊥)
    (hfixR : f.Ri 0 ≤ centralizer (f.Vi 0 : Set G)) :
    (T : Subgroup G) ⊓ lineSectionKernel (f.Vi 0) (f.Li 0) = f.Ri 0 := by
  let A := f.Li 0
  let J := A ⊔ (T : Subgroup G)
  have hn : J ≤ normalizer (A : Set G) := sup_le A.le_normalizer (f.sylow_normalizes_Li 0)
  let a := (coreQuotientAction A).comp (inclusion hn)
  have he : a = pCoreJoinAction 2 (f.sylow_normalizes_Li 0) := by
    ext g x
    induction x using Quotient.inductionOn with
    | h x => rfl
  have hk : a.ker = pCore 2 J := by
    rw [he]
    exact pCoreJoinAction_kernel 2 (f.sylow_normalizes_Li 0) T.isPGroup' hc
  apply le_antisymm
  · rintro g ⟨hgT, _, hgK⟩
    have hgJ : g ∈ J := (le_sup_right : (T : Subgroup G) ≤ J) hgT
    have hga : (⟨g,hgJ⟩ : J) ∈ a.ker := by
      obtain ⟨b,hb,hbg⟩ := hgK
      have hb' : b = inclusion hn ⟨g,hgJ⟩ := Subtype.ext hbg
      change inclusion hn ⟨g,hgJ⟩ ∈ (coreQuotientAction A).ker
      exact hb' ▸ hb
    rw [hk] at hga
    exact mem_map_of_mem J.subtype hga
  · intro g hgR
    refine ⟨localRadical_le_sylow _ hgR, hfixR hgR, ?_⟩
    obtain ⟨r,hr,hrg⟩ := hgR
    refine ⟨inclusion hn r, ?_, hrg⟩
    change r ∈ a.ker
    rwa [hk]

/-- The exact Sylow intersection supplies the original radical as a Sylow image. -/
theorem chosen_section_sylow_of_intersection
    (hA : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) (f.Li 0))
    (hR : (T : Subgroup G) ⊓ lineSectionKernel (f.Vi 0) (f.Li 0) = f.Ri 0) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
      ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
        (P : Subgroup _).map (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0 := by
  have hn := chosen_first_normalized_of_component S f hA
  refine ⟨hn, ?_⟩
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T
    (lineSectionKernel (f.Vi 0) (f.Li 0))
    ((f.invariant 0).trans (lineSectionKernel_normalized hn))
  refine ⟨P, ?_⟩
  rw [hP, subgroupOf_map_subtype]
  exact hR

/-- The preceding PSL₂(q) identification supplies centerlessness of the
literal residual quotient, including all nonbinary fields. -/
theorem chosen_first_quotient_center
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree)) :
    center (f.Li 0 ⧸ pCore 2 (f.Li 0)) = ⊥ := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hm
  have hfour : 4 ≤ Nat.card E := by
    rw [hE]
    exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (f.Li 0 ⧸ pCore 2 (f.Li 0)) := e.isSimpleGroup
  rcases (inferInstance : (center (f.Li 0 ⧸ pCore 2 (f.Li 0))).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative (f.Li 0 ⧸ pCore 2 (f.Li 0))
      (center_eq_top_iff.mp ht)).elim

/-- The actual hpositive input for 11.2.3. All component, orbit and Sylow
arguments are proved; only the preceding rank-one flag identities remain. -/
theorem chosen_line_positive_steps_of_flag_geometry
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfixR : f.Ri 0 ≤ centralizer (f.Vi 0 : Set G))
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
      ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
        (P : Subgroup _).map (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0 :=
  chosen_section_sylow_of_intersection S f
    (chosen_first_component_of_centralizer_le S f
      (Components.flag_mem_local_of_model D S f 0 hm) hfix hC)
    (chosen_section_intersection S f (chosen_first_quotient_center S f hm) hfixR)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
