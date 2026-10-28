module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.FixedSpace
public import CFSG.Quasithin.Chapter10.SourceFullModuleFusion
public import CFSG.Quasithin.Chapter10.SourceA5OffenderNormalization

/-!
# The full-module fusion branch of the fixed-space argument

If J(T) centralizes V, fusion in V is controlled by M. A nonidentity
intersection point in V∩Wˣ then corrects x by an element of M to an element
of C_G(w)≤M. Hence V∩Wˣ=1 for every x outside M. The displacement lies
in that intersection, so it vanishes without a residual or quotient-kernel
calculation. This gives a shorter route for the centralizing-Thompson rows.

`FixedVectors` supplies the required nonfixed fixed vector from the
component kernel, with no additional source premise. All conjugation is
literal left conjugation. Source: Aschbacher--Smith 3.2.10, 10.1.2 and 10.2.12,
printed pp.583--584,742,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A moved point in a conjugate full module forces its conjugator into M. -/
theorem fullModule_inf_conjugate_moved_eq_bot
    (c : Context D)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {x : G} (hx : x ∉ D.maximalLocal) :
    D.fullModule ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨hv,w,hw,rfl⟩
  change (MulAut.conj x) w = 1
  by_contra hne
  have hwne : w ≠ 1 := fun he => hne (by simp only [he,map_one])
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨m,hm,he⟩ := source_fullModule_element_fusion D hJ (hWV hw) hv
    (isConj_iff.mpr ⟨x,rfl⟩)
  change m*w*m⁻¹ = x*w*x⁻¹ at he
  have he' : (m⁻¹*x)*w*(m⁻¹*x)⁻¹ = w := by
    calc
      _ = m⁻¹*(x*w*x⁻¹)*m := by group
      _ = m⁻¹*(m*w*m⁻¹)*m := by rw [←he]
      _ = w := by group
  have hc : m⁻¹*x ∈ centralizer ({w} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he')
  have hm' := D.maximalLocal.mul_mem hm (c.pointCentralizers w hw hwne hc)
  exact hx (by simpa only [mul_inv_cancel_left] using hm')

/-- In the fusion branch every relevant displacement is zero immediately. -/
theorem displacement_eq_bot_of_fusion
    (c : Context D)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {x : G} (hx : x ∉ D.maximalLocal)
    {b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj x).toMonoidHom : Set G)) :
    ⁅(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ = ⊥ := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  have hd := source_nonnormal_offender_displacement_le D c.nonnormal ht htn
    (c.crossed t ht htn) c.pointCentralizers hb hbn
  apply eq_bot_iff.mpr
  exact hd.trans_eq ((inf_comm _ _).trans (fullModule_inf_conjugate_moved_eq_bot D c hJ hx))

/-- The fusion route needs only the indicated fixed-vector fact from the
module analysis, not a quotient kernel, simplicity or residual premise. -/
theorem fixedSpaceGeometry_of_fusion
    (c : Context D)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (hfixed : ∀ b ∈ D.maximalLocal,
      b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) → b ^ 2 = 1 →
      ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G)) :
    FixedSpaceGeometry D := by
  intro x hx hsmall
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj x).toMonoidHom
  let A := P ⊓ D.maximalLocal
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  obtain ⟨b,hb,hbM,hbN,hbn⟩ := exists_nonfixed_normalizing_element D c.nonnormal c.size hsmall
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b (show b ∈ P from hb)
  have hzero := displacement_eq_bot_of_fusion D c hJ hx hb hbn
  have hfix : W ⊓ centralizer ({b} : Set G) ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hzero)
  refine ⟨source_nonnormal_normalizes_moved_of_fixed_subgroup D c.nonnormal ht htn
      (c.crossed t ht htn) (W ⊓ centralizer ({b} : Set G)) A inf_le_left
      (hfixed b hbM hbN hb2) inf_le_right hfix,?_⟩
  intro a ha han
  exact le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp
    (displacement_eq_bot_of_fusion D c hJ hx ha.1 han))

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
