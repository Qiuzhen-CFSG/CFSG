module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceInternalMover
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.AlmostSpecialIntersection
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Seed

/-!
# The terminal second layer on the original normal A₆ data

The full L₁ action on U_H modulo the original point factors through its
cyclic quotient of order three. Coprime decomposition excludes every
further central L₁ section above that point. The original F.9 intersection
is V∩U_H=V₃, so the derived-subgroup bound on the two conjugate closures
puts U_H∩U_H^g in V₃. Consequently the actual second layer
V(U_H∩U_H^g) equals V.

This proves the chief-factor step of G.2.4(8) directly on the selected
original pair, without a fixed-T marking. Core-product generation and
the upper natural action still remain for the complete block conclusion.

Source: Aschbacher–Smith,G.2.4(8), printed pp.334–335, as applied in
13.5.14–15, printed pp.919–920.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSecondLayer
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem no_central_section (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (A B : Subgroup G) (hpoint : D.V₁ ≤ A) (hAU : A ≤ D.UH)
    (hnA : D.L₁ ≤ normalizer (A : Set G)) (hBU : B ≤ D.UH)
    (hBA : ⁅B,D.L₁⁆ ≤ A) : B ≤ A := by
  have hcore : D.L₁.pCoreIn 2 ≤ D.QH := (local_core_intersection h hn).symm.le.trans inf_le_right
  have hcubic : Nat.card (D.L₁ ⧸ pCore 2 D.L₁)=3 := SourceStar.original_residual_quotient_card d h e
  have hLU : D.L₁ ≤ normalizer (D.UH : Set G) :=
    (le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hUU : ⁅D.UH, D.UH⁆ ≤ A :=
    (derived_le_of_frattini_image_le h.g2_hypothesis.U_isPGroup h.frattini_UH_le_point).trans hpoint
  have hUA : D.UH ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr ((commutator_mono hAU le_rfl).trans hUU)
  let hN : (A.subgroupOf D.UH).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAU).mpr hUA
  let := hN
  have hUC : ⁅D.UH, D.L₁.pCoreIn 2⁆ ≤ A := by
    rw [commutator_comm]
    exact ((commutator_mono hcore le_rfl).trans (commutator_comm D.UH D.QH ▸ h.commutator_UH_QH_le_point)).trans hpoint
  obtain ⟨ρ, hρ, hk, hf⟩ := exists_quotient_conjugation_full_action
    D.L₁ D.UH A D.L₁ (D.L₁.pCoreIn 2) hLU hnA hN le_rfl
    (closure_reduction h hseed hn).1.symm hUC
  let W := D.UH ⧸ A.subgroupOf D.UH
  let q := QuotientGroup.mk' (A.subgroupOf D.UH)
  have hker : pCore 2 D.L₁ ≤ ρ.ker := by
    intro x hx
    exact hk (mem_map_of_mem D.L₁.subtype hx)
  let σ : (D.L₁ ⧸ pCore 2 D.L₁) →* MulAut W :=
    QuotientGroup.lift (pCore 2 D.L₁) ρ hker
  have hrange : σ.range = ρ.range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.L₁) x
      exact ⟨l, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 D.L₁) l, rfl⟩
  have hthree : IsPGroup 3 ρ.range := by
    rw [← hrange]
    exact (IsPGroup.of_card (n := 1) hcubic).of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
  have htwo : IsPGroup 2 W := (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).to_quotient (A.subgroupOf D.UH)
  have habelian : IsMulCommutative W := by
    apply (_root_.commutator_eq_bot_iff W).mp
    apply bot_unique
    have hm : ⁅(⊤ : Subgroup D.UH), ⊤⁆ ≤ A.subgroupOf D.UH := by
      intro x hx
      have hh := mem_map_of_mem D.UH.subtype hx
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hh
      exact hUU hh
    have hh := map_mono (f := q) hm
    rw [map_commutator, map_top_of_surjective q (QuotientGroup.mk'_surjective _),
      QuotientGroup.map_mk'_self] at hh
    exact hh
  let := habelian
  have hcop : Nat.Coprime (Nat.card ρ.range) (Nat.card W) := by
    have hh := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      ρ.range (⊤ : Subgroup W) hthree (htwo.to_subgroup ⊤)
    simpa only [card_top] using hh
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := W) (A := ρ.range) (Group.isSolvable_of_comm fun a b => mul_comm a b) hcop habelian
  have hfull' : commutatorAction ρ.range W = ⊤ := by
    have he : (D.L₁.subgroupOf D.L₁).map ρ = ρ.range := by
      ext a
      exact ⟨fun ⟨x, _, he⟩ => ⟨x, he⟩, fun ⟨x, he⟩ => ⟨x, x.property, he⟩⟩
    rwa [he] at hf
  have hfixed : FixedPoints.subgroup ρ.range W = ⊥ := by
    have hd := hcompl.disjoint
    rw [hfull'] at hd
    exact disjoint_top.mp hd
  intro b hb
  let bU : D.UH := ⟨b, hBU hb⟩
  have hbfix : q bU ∈ FixedPoints.subgroup ρ.range W := by
    rintro ⟨a, l, rfl⟩
    change ρ l (q bU) = q bU
    rw [hρ]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (l : G) * b * (l : G)⁻¹ / b ∈ A
    have hh : ⁅(l : G), b⁆ ∈ A := by
      rw [commutator_comm] at hBA
      exact hBA (commutator_mem_commutator l.property hb)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh
  have hbq : q bU = 1 := by simpa only [hfixed, mem_bot] using hbfix
  exact (QuotientGroup.eq_one_iff bU).mp hbq

theorem seed_intersection (h : D.Hypothesis) (hU : ¬ IsMulCommutative D.UH) :
    D.V ⊓ D.UH = D.Vplus := by
  have hi : D.Vplus.relIndex D.V=2 := by
    have hc := (D.Vplus.subgroupOf D.V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe h.plus_le).toEquiv,
      d.seed_card,ReturningPlane.module_card d] at hc
    change (D.Vplus.subgroupOf D.V).index=2
    omega
  have hh := LocalGeometry.seed_eq_intersection_core h hi hU
  apply le_antisymm ((inf_le_inf_left D.V h.UH_le_QH).trans_eq hh)
  exact le_inf h.plus_le (le_conjugateSpanBy _ _)

theorem intersection_commutator_le_module (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) :
    ⁅D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g.val,NormalBranch.K D g.val⁆ ≤ D.V := by
  have hpoint : D.V₁ ≤ D.V := h.point_lt.le.trans h.plus_le
  have hd : ⁅D.UH,D.UH⁆ ≤ D.V :=
    (derived_le_of_frattini_image_le h.g2_hypothesis.U_isPGroup h.frattini_UH_le_point).trans hpoint
  have hnV : D.L ≤ normalizer (D.V : Set G) := le_sup_left.trans d.normalizes_V
  have hc : ⁅ChapterG.Section02.Setup.conjugate D.UH g.val,
      ChapterG.Section02.Setup.conjugate D.UH g.val⁆ ≤ D.V := by
    have hm := map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hd
    have he : D.V.map (MulAut.conj g.val⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (D.V : Set G)).inv_mem (hnV g.property))
    rw [map_commutator,he] at hm
    exact hm
  exact intersection_commutator_sup_le hd hc (hK.trans hnV)

theorem intersection_le_seed (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val) :
    D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g.val ≤ D.Vplus := by
  have hLU : D.L₁ ≤ normalizer (D.UH : Set G) :=
    (le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hBA : ⁅D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g.val,D.L₁⁆ ≤ D.Vplus := by
    rw [←seed_intersection d h hU]
    exact le_inf ((commutator_mono le_rfl hL).trans (intersection_commutator_le_module d h g hK))
      ((commutator_mono inf_le_left le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hLU))
  exact no_central_section d h e hseed hn D.Vplus _ h.point_lt.le
    (le_conjugateSpanBy _ _) (le_sup_left.trans h.local_normalizes) inf_le_left hBA

theorem second_eq_module (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val) :
    D.V ⊔ (D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g.val : Subgroup G) = D.V :=
  sup_eq_left.mpr ((intersection_le_seed d h e hseed hn hU g hK hL).trans h.plus_le)

/-- Direct source consumer of the internal pair and the cubic chief-factor step. -/
theorem exists_original_second_layer (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ g : D.L, g.val ∉ D.Gz ∧ g.val ∈ NormalBranch.K D g.val ∧
      NormalBranch.K D g.val ≤ D.L ∧ D.L₁ ≤ NormalBranch.K D g.val ∧
      IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      conjugateSpanBy D.V₁ (NormalBranch.K D g.val) = D.V ∧
      D.V ⊔ (D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g.val : Subgroup G) = D.V := by
  obtain ⟨a,g,hg,hgK,hK,hL,hp,hr,hs,_⟩ :=
    SourceInternalMover.exists_original_internal_pair d h e hseed hn hU
  exact ⟨g,hg,hgK,hK,hL,hp,hr,hs,second_eq_module d h e hseed hn hU g hK hL⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSecondLayer
end
