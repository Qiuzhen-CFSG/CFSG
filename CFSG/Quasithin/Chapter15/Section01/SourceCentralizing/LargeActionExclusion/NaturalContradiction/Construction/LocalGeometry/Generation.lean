module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry
public import Theory.GroupAction.FourPerfectImage

/-!
# Generation by the first natural parabolic residual

The original residual O²(C_M(Z₁)) fixes the first source summand. Its
image on the moving four-group has order dividing three, and the full
movement by Y₀ makes the image of Y₀ equal to that residual image.
The discrepancy between any residual element and its Y₀ representative
therefore centralizes both summands, hence all of V. The original Sylow
supplement and M = ⟨C_M(Z₁),T⟩ give the literal set product
M = ⟨Y₀,T⟩ C_M(V).

The final theorem applies this argument to the first residual of the
already marked natural flag. No orbit or maximal-overgroup conclusion
is assumed. Source: Aschbacher--Smith 15.1.16 and 15.1.29, printed
pp.1092 and 1104 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- A subgroup of the actual marked residual moving the entire four-group
has the same action as that residual, modulo the full module centralizer. -/
theorem NineSource.residual_le_moving_sup_centralizer (s : d.NineSource)
    (h : PreparedChosenModule T M V) {Y : Subgroup G}
    (hYR : Y ≤ d.nineResidual) (hmove : ⁅d.nineMovingPlane,Y⁆ = d.nineMovingPlane) :
    d.nineResidual ≤ Y ⊔ (M ⊓ centralizer (V : Set G)) := by
  let R := d.nineResidual
  let W := d.nineMovingPlane
  have hWM : W ≤ V := le_sup_right.trans_eq s.planes_sup
  let : IsElementaryAbelian 2 V := h.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion hWM) (inclusion_injective hWM)
  have hn : R ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  let f := actionHom R W hn
  have hdiv : Nat.card f.range ∣ 3 := MulAut.card_range_dvd_three_of_twoPerfect
    (isPPerfect_embedded_pResidual 2 (M ⊓ d.G1)) s.moving_card f
  let B := Y.subgroupOf R
  have hBne : B.map f ≠ ⊥ := by
    intro hz
    have hYC : Y ≤ centralizer (W : Set G) := by
      intro y hy w hw
      have hfy : f ⟨y,hYR hy⟩ = 1 := hz.le (mem_map_of_mem f hy)
      have he := congrArg (fun a : MulAut W => (a ⟨w,hw⟩ : G)) hfy
      change y * w * y⁻¹ = w at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hzW : W = ⊥ := hmove.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hYC))
    have hc := s.moving_card
    rw [show d.nineMovingPlane = ⊥ from hzW,card_bot] at hc
    omega
  have hBcard : Nat.card (B.map f) = 3 := by
    have hd := (card_dvd_of_le (map_le_range f B)).trans hdiv
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
    · exact (hBne (card_eq_one.mp he)).elim
    · exact he
  have heq : B.map f = f.range := eq_of_le_of_card_ge (map_le_range f B) (by
    rw [hBcard]
    exact Nat.le_of_dvd (by decide) hdiv)
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  have hRC : R ≤ centralizer (d.nineFixedPlane : Set G) :=
    le_centralizer_iff.mp inf_le_right
  intro r hr
  have him : f ⟨r,hr⟩ ∈ B.map f := heq.symm ▸ (show f ⟨r,hr⟩ ∈ f.range from ⟨⟨r,hr⟩,rfl⟩)
  obtain ⟨y,hy,hey⟩ := him
  have hcR : y.val⁻¹ * r ∈ R := R.mul_mem (R.inv_mem y.property) hr
  have hcW : y.val⁻¹ * r ∈ centralizer (W : Set G) := by
    have he : f ⟨y.val⁻¹ * r,hcR⟩ = 1 := by
      change f (y⁻¹ * ⟨r,hr⟩) = 1
      rw [map_mul,map_inv,hey,inv_mul_cancel]
    intro w hw
    have hh := congrArg (fun a : MulAut W => (a ⟨w,hw⟩ : G)) he
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcV : y.val⁻¹ * r ∈ centralizer (V : Set G) := by
    apply mem_centralizer_iff.mpr
    intro v hv
    have hv' : v ∈ d.nineFixedPlane ⊔ W := s.planes_sup.symm ▸ hv
    have hle : d.nineFixedPlane ⊔ W ≤ centralizer ({y.val⁻¹ * r} : Set G) := by
      apply sup_le
      · intro z hz c hc
        rw [Set.mem_singleton_iff.mp hc]
        exact (hRC hcR z hz).symm
      · intro z hz c hc
        rw [Set.mem_singleton_iff.mp hc]
        exact (hcW z hz).symm
    exact (hle hv' _ (Set.mem_singleton _)).symm
  have hm := (Y ⊔ (M ⊓ centralizer (V : Set G))).mul_mem
    (mem_sup_left hy) (mem_sup_right ⟨hRM hcR,hcV⟩)
  simpa only [Subgroup.subtype_apply,mul_inv_cancel_left] using hm

/-- The source generation argument in 15.1.16 for the actual moving residual. -/
theorem NineSource.product_of_moving_residual (s : d.NineSource)
    (hM : IsOrderingMaximal T M) (h : PreparedChosenModule T M V)
    {Y : Subgroup G} (hYR : Y ≤ d.nineResidual)
    (hmove : ⁅d.nineMovingPlane,Y⁆ = d.nineMovingPlane) :
    ∀ m ∈ M, ∃ x ∈ Y ⊔ (T : Subgroup G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), x * c = m := by
  let C := M ⊓ centralizer (V : Set G)
  let H := Y ⊔ (T : Subgroup G)
  have hYM : Y ≤ M := hYR.trans ((map_subtype_le _).trans inf_le_left)
  have hHM : H ≤ M := sup_le hYM hM.1.2
  have hHC : H ≤ normalizer (C : Set G) := hHM.trans
    ((le_inf M.le_normalizer
      (h.normalized.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf)
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict
    (le_inf (d.S_le_T.trans hM.1.2) d.S_le_G1) inf_le_right
  have hCeq : M ⊓ d.G1 = d.nineResidual ⊔ d.S := by
    have he := congrArg (map (M ⊓ d.G1).subtype) (pResidual_sup_sylow_eq_top P)
    rw [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype] at he
    exact he.symm
  have hcover : M ≤ H ⊔ C := by
    rw [d.M_eq_centralizer_sup_sylow]
    apply sup_le
    · change M ⊓ d.G1 ≤ H ⊔ C
      rw [hCeq]
      exact sup_le ((s.residual_le_moving_sup_centralizer h hYR hmove).trans
        (sup_le_sup (show Y ≤ H from le_sup_left) le_rfl))
        (d.S_le_T.trans (le_sup_right.trans le_sup_left))
    · exact le_sup_right.trans le_sup_left
  intro m hm
  have hh : m ∈ (H : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right H C hHC]
    exact hcover hm
  exact hh

namespace NaturalFlag
/-- The same first-node residual supplies the literal set product required
by the source maximal-overgroup argument. -/
theorem first_product (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ∀ m ∈ M, ∃ x ∈ a.parabolics.Y0 ⊔ (T : Subgroup G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), x * c = m := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  have hY : a.parabolics.Y0 ≤ d.nineResidual := embedded_pResidual_mono 2
    (le_inf (a.first_le_selected hG hM hJ hu h hfull hs ht htS hnat)
      (a.parabolics_le.1.trans (sup_le d.L_component.1 d.S_le_G1)))
  exact s.product_of_moving_residual hM h hY
    (a.first_moves_movingPlane hG hM hu h hs ht htS hnat)
end NaturalFlag
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
