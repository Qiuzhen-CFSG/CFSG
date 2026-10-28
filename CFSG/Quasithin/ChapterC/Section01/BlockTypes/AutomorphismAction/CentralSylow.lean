module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Sylow fixers modulo the center of a short group

A faithful block module detects the core-quotient action of an automorphism
fixing a Sylow subgroup modulo the center. Its remaining displacement lies
in U(L). Averaging its cocycle over the odd Sylow index makes the automorphism
inner by a Sylow-fixed block vector, using perfection to remove the central
error. Distinct automorphisms give distinct vectors in the actual module.

This internal continuation of AutomorphismAction uses its hidden actor body
only in proofs. The existing public action boundary is unchanged.
Source: Aschbacher--Smith 15.1.22(**), printed p.1099, and A.1.39.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L A W : Type*} [Group L] [Finite L] [Group A] [CommGroup W]
variable {ρ : A →* MulAut W}

omit [Finite L] in
private theorem moduleAction_eq_one_of_central_sylow
    (m : BlockModuleModel L ρ) (P : Sylow 2 L) (a : MulAut L)
    (ha : ∀ x ∈ P, a x * x⁻¹ ∈ center L) : m.moduleAction a = 1 := by
  ext w
  obtain ⟨u,rfl⟩ := m.moduleIso.surjective.comp
    (QuotientGroup.mk'_surjective (blockFixed L)) w
  dsimp only [Function.comp_apply]
  rw [m.moduleAction_mk]
  apply congrArg m.moduleIso
  apply QuotientGroup.eq_iff_div_mem.mpr
  simp only [div_eq_mul_inv]
  change a (u : L) * (u : L)⁻¹ ∈ center L
  exact ha u (pCore_isPGroup.le_sylow_of_normal P (blockU_le_core u.property))

/-- Sylow fixation modulo the center forces innerness by a fixed block vector. -/
theorem IsShort.automorphism_eq_conj_of_central_sylow [Group.IsPerfect L]
    (hs : IsShort L) (m : BlockModuleModel L ρ) (hρ : Function.Injective ρ)
    (P : Sylow 2 L) (a : MulAut L)
    (ha : ∀ x ∈ P, a x * x⁻¹ ∈ center L) :
    ∃ u : blockU L, a = MulAut.conj (u : L) ∧
      ∀ x ∈ P, ρ (m.actor x) (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)) =
        m.moduleIso (QuotientGroup.mk' (blockFixed L) u) := by
  have hm := moduleAction_eq_one_of_central_sylow m P a ha
  have hq : m.quotientAction a = 1 := by
    ext g
    apply hρ
    ext w
    have hh := m.actions_compatible a g w
    rw [hm] at hh
    exact hh.symm
  have hd (x : L) : a x * x⁻¹ ∈ blockU L := by
    have hc (y : L) : a y * y⁻¹ ∈ pCore 2 L := by
      have hh := m.quotientAction_actor a y
      rw [hq] at hh
      have he := m.quotientIso.injective hh.symm
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
    have hh := DFunLike.congr_fun (hs.quotient_blockU_aut_eq_one a hc)
      (QuotientGroup.mk' (blockU L) x)
    rw [quotientAut_apply_mk] at hh
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hh
  let c : L → W := fun x => m.moduleIso (QuotientGroup.mk' (blockFixed L) ⟨a x*x⁻¹,hd x⟩)
  let r : L →* MulAut W := ρ.comp m.actor
  have hc (x y : L) : c (x*y) = c x * r x (c y) := by
    have hh := m.intertwining x (⟨a y*y⁻¹,hd y⟩ : blockU L)
    change m.moduleIso _ = m.moduleIso _ * ρ (m.actor x) (m.moduleIso _)
    dsimp only [BlockModuleModel.actor,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    rw [←hh,←map_mul,←map_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, blockConjugate, map_mul]
    group
  have he (w : W) : w^2=1 := by
    obtain ⟨v,rfl⟩ := m.moduleIso.surjective w
    let : IsElementaryAbelian 2 (BlockModule L) := hs.module_elementary
    rw [←map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (BlockModule L)) v,map_one]
  have hcP (x : L) (hx : x ∈ P) : c x = 1 := by
    apply m.moduleIso.map_eq_one_iff.mpr
    exact (QuotientGroup.eq_one_iff _).mpr (ha x hx)
  obtain ⟨w,hw⟩ := binary_cocycle_trivial_of_sylow r c hc he P hcP
  obtain ⟨u,hu⟩ := m.moduleIso.surjective.comp
    (QuotientGroup.mk'_surjective (blockFixed L)) w
  refine ⟨u,?_,?_⟩
  · apply MulAut.quotient_center_injective
    ext q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center L) q
    rw [quotientAut_apply_mk,quotientAut_apply_mk]
    have hh := hw x
    rw [←hu] at hh
    change ρ (m.actor x) (m.moduleIso _) * m.moduleIso _ = m.moduleIso _ at hh
    dsimp only [BlockModuleModel.actor,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] at hh
    rw [mul_comm,←m.intertwining,←map_mul,←map_mul] at hh
    have hc' := QuotientGroup.eq_iff_div_mem.mp (m.moduleIso.injective hh)
    simp only [div_eq_mul_inv] at hc'
    change ((a x*x⁻¹)*(x*(u:L)*x⁻¹))*(u:L)⁻¹ ∈ center L at hc'
    apply QuotientGroup.eq_iff_div_mem.mpr
    convert hc' using 1
    simp only [div_eq_mul_inv,MulAut.conj_apply]
    group
  · intro x hx
    have hh := hw x
    rw [hcP x hx,mul_one,←hu] at hh
    exact hh
/-- Distinct Sylow fixers modulo the center have distinct natural fixed vectors. -/
theorem IsShort.central_sylow_fixers_card_le [Group.IsPerfect L] [Finite W]
    (hs : IsShort L) (m : BlockModuleModel L ρ) (hρ : Function.Injective ρ)
    (P : Sylow 2 L) (B : Subgroup (MulAut L))
    (hB : ∀ a ∈ B, ∀ x ∈ P, a x * x⁻¹ ∈ center L) :
    Nat.card B ≤ Nat.card {w : W // ∀ x ∈ P, ρ (m.actor x) w = w} := by
  classical
  choose u hu hfix using fun a : B =>
    hs.automorphism_eq_conj_of_central_sylow m hρ P a.val (hB a a.property)
  let f : B → {w : W // ∀ x ∈ P, ρ (m.actor x) w = w} :=
    fun a => ⟨m.moduleIso (QuotientGroup.mk' (blockFixed L) (u a)),hfix a⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  have he := m.moduleIso.injective (congrArg Subtype.val hab)
  have hz0 : (u a)⁻¹ * (u b) ∈ blockFixed L := QuotientGroup.eq.mp he
  have hz : ((u a : L)⁻¹ * (u b : L)) ∈ center L := hz0
  apply Subtype.ext
  rw [hu a,hu b]
  have hh : MulAut.conj ((u a : L)⁻¹ * (u b : L)) = 1 := by
    ext x
    change ((u a : L)⁻¹ * (u b : L)) * x * ((u a : L)⁻¹ * (u b : L))⁻¹ = x
    rw [←mem_center_iff.mp hz x,mul_inv_cancel_right]
  rw [map_mul,map_inv,inv_mul_eq_one] at hh
  exact hh
end CFSG.Quasithin.ChapterC
