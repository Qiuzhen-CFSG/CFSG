module
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Inner small-displacement involutions in a perfect normal subgroup

Every constituent of a nontrivial normal perfect subgroup in a faithful
irreducible binary action has degree at least three. An involution of
rank at most two therefore preserves each constituent. If its action on
the subgroup is inner, remove the inner representative. The remaining
centralizing involution is a square-zero intertwining displacement on every
simple constituent, hence zero by Schur's lemma. Clifford spanning makes
it trivial on the whole module, placing the original involution in the
subgroup without assuming irreducibility of the subgroup restriction.

Source: Clifford theory and the representation argument in Aschbacher–Smith
15.2.27(2), printed p.1119. The actual component-normalizer application is in
Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.NormalizerIrreducible.
-/

public section
open Subgroup
namespace Representation.PerfectInvolutionExtension
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A rank-at-most-two involution inducing an inner component action lies in that component. -/
theorem inner_square_one_mem_of_small_displacement
    (ρ : Representation (ZMod 2) G V) (hi : IsIrreducible ρ)
    (hf : Function.Injective ρ) (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hK : K ≠ ⊥) (hz : center K = ⊥)
    (a : G) (ha : a ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2)
    (hinner : ∃ k : K, MulAut.conjNormal (H := K) a = MulAut.conj k) : a ∈ K := by
  obtain ⟨k,hk⟩ := hinner
  have hk2 : k ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hz
    rw [map_pow, ←hk, ←map_pow, ha, map_one, map_one]
  have hcomm : Commute a (k : G) := by
    have hh := congrArg (fun f : MulAut K => (f k : G)) hk
    change a * k * a⁻¹ = k * k * (k : G)⁻¹ at hh
    rw [mul_inv_cancel_right] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let y := a * (k : G)⁻¹
  have hy2 : y ^ 2 = 1 := by
    rw [hcomm.inv_right.mul_pow,ha,inv_pow,
      show (k : G)^2 = 1 from congrArg K.subtype hk2,inv_one,mul_one]
  have hyc : y ∈ centralizer (K : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    change MulAut.conjNormal (H := K) (a * (k : G)⁻¹) = 1
    rw [map_mul,map_inv,MulAut.conjNormal_val,hk,mul_inv_cancel]
  have hn : ¬ K ≤ ρ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf]
    exact fun hh => hK (bot_unique hh)
  have hfix (J : Subrepresentation (ρ.comp K.subtype))
      (hJ : IsIrreducible J.toRepresentation) :
      ∀ v ∈ J.toSubmodule, ρ y v = v := by
    have hd := constituent_dimension ρ hi K hn J hJ
    have hstable := map_constituent_eq_self_of_displacement_lt ρ K a J hJ
      (show Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) <
        Module.finrank (ZMod 2) J.toSubmodule from lt_of_le_of_lt hr (by omega))
    have hY (v : V) (hv : v ∈ J.toSubmodule) : ρ y v ∈ J.toSubmodule := by
      change ρ (a * (k : G)⁻¹) v ∈ J.toSubmodule
      rw [map_mul,Module.End.mul_apply]
      exact hstable.le ⟨ρ (k : G)⁻¹ v,J.apply_mem_toSubmodule k⁻¹ hv,rfl⟩
    let f : J.toRepresentation.IntertwiningMap J.toRepresentation := {
      toLinearMap := (ρ y - 1).restrict (fun v hv => J.toSubmodule.sub_mem (hY v hv) hv)
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        change ρ y (ρ g v) - ρ g v = ρ g (ρ y v - v)
        rw [map_sub]
        have hh := congrArg (fun b : G => ρ b v) (hyc g g.property)
        simp only [map_mul,Module.End.mul_apply] at hh
        rw [hh] }
    have hff (v : J.toSubmodule) : f (f v) = 0 := by
      apply Subtype.ext
      change ρ y (ρ y v - v) - (ρ y v - v) = 0
      rw [map_sub,←Module.End.mul_apply,←map_mul,←pow_two,hy2,map_one,Module.End.one_apply]
      have htwo (w : V) : w + w = 0 := by
        rw [←two_smul (ZMod 2),show (2 : ZMod 2) = 0 from rfl,zero_smul]
      have hneg (w : V) : -w = w := neg_eq_iff_add_eq_zero.mpr (htwo w)
      simp only [sub_eq_add_neg,hneg]
      rw [add_assoc, ←add_assoc (ρ y v),htwo,zero_add,htwo]
    let := hJ
    have hf0 : f = 0 := by
      rcases IsIrreducible.injective_or_eq_zero f with hfi | hzero
      · apply IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        change f v = 0
        apply hfi
        simpa only [map_zero] using hff v
      · exact hzero
    intro v hv
    exact sub_eq_zero.mp (congrArg (fun F : J.toRepresentation.IntertwiningMap J.toRepresentation =>
      (F ⟨v,hv⟩ : V)) hf0)
  let Y : Subrepresentation (ρ.comp K.subtype) := {
    toSubmodule := LinearMap.ker (ρ y - 1)
    apply_mem_toSubmodule g v hv := by
      change ρ y (ρ g v) - ρ g v = 0
      have hh := congrArg (fun b : G => ρ b v) (hyc g g.property)
      simp only [map_mul,Module.End.mul_apply] at hh
      rw [←hh,show ρ y v = v from sub_eq_zero.mp hv,sub_self] }
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have htop : (⊤ : Subrepresentation (ρ.comp K.subtype)) ≤ Y := by
    rw [←iSup_conjugateSubrepresentations_eq_top ρ K hi J hJ]
    apply iSup_le
    intro g
    have hc : IsIrreducible (conjugateSubrepresentation ρ K J g).toRepresentation := by
      apply (Subrepresentation.irreducible_iff_isAtom _).mpr
      simpa using ((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff J).mpr
        ((Subrepresentation.irreducible_iff_isAtom J).mp hJ)
    intro v hv
    exact sub_eq_zero.mpr (hfix _ hc v hv)
  have hy : y = 1 := hf (by
    apply LinearMap.ext
    intro v
    exact (sub_eq_zero.mp (htop (show v ∈ (⊤ : Subrepresentation (ρ.comp K.subtype)) from
      Submodule.mem_top))).trans (by simp))
  exact (mul_inv_eq_one.mp hy) ▸ k.property

end Representation.PerfectInvolutionExtension
