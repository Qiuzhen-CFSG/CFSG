module

public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Order.Displacement
public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Definitions
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Four independent directions in the original J.4 span

The binary section S/V descends to S/U. In the actual W/U, the displacement
plane is disjoint from the central line, and the selected involution lies
outside Q/U. Their join therefore has order sixteen. Its intersection with
the original five-displacement image is exactly the displacement plane.

Source: Aschbacher–Smith, J.4.2(2–3), printed p.440.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

theorem hat_S_elementary : IsElementaryAbelian 2 (hat d d.toTypeRuSetup.S) := by
  have hlift (x : hat d d.toTypeRuSetup.S) :
      ∃ q : d.toTypeRuSetup.S, hatMap d (inclusion d.S_le_H q) = (x:Hat d) := by
    obtain ⟨h,hh,he⟩ := x.property
    exact ⟨⟨h,hh⟩,he⟩
  have hs (q : d.toTypeRuSetup.S) : (q:G)^2 ∈ d.toTypeRuSetup.U := by
    change ((q^2 : d.toTypeRuSetup.S):G) ∈ d.toTypeRuSetup.U
    apply le_conjugateSpan _ _
    apply (d.ru1.steinberg.coordinates_eq_one_iff (q^2)).mp
    rw [map_pow]
    change (2:ℕ) • (d.ru1.steinberg.coordinates q).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]
  refine {toIsMulCommutative := ⟨⟨?_⟩⟩,exponent_dvd_p := ?_}
  · intro x y
    obtain ⟨a,ha⟩ := hlift x
    obtain ⟨b,hb⟩ := hlift y
    apply Subtype.ext
    change (x:Hat d)*(y:Hat d) = (y:Hat d)*(x:Hat d)
    rw [← ha,← hb,← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
    apply (hatMap_eq_one d _).mpr
    apply le_conjugateSpan _ _
    apply (d.ru1.steinberg.coordinates_eq_one_iff ⁅a,b⁆).mp
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨a,ha⟩ := hlift x
    apply Subtype.ext
    change (x:Hat d)^2 = 1
    rw [← ha,← map_pow]
    exact (hatMap_eq_one d _).mpr (hs a)

theorem Plane.hat_W_elementary (p : Plane d) : IsElementaryAbelian 2 (hat d p.W) := by
  let := hat_S_elementary (d:=d)
  exact IsElementaryAbelian.of_le (hat_mono d p.W_le_S)

theorem Plane.W₀_le_W (p : Plane d) : p.W₀ ≤ p.W := by
  intro x hx
  change x∈(p.W:Set G)
  rw [p.W_eq_product]
  exact ⟨x,hx,1,(Q₀ d).one_mem,mul_one x⟩

theorem SourceChoice.Uα_le_W₀ (s : SourceChoice p) : s.Uα ≤ p.W₀ := by
  rw [p.W₀_eq_conjugateSpanBy,conjugateSpanBy_eq_iSup_conj]
  exact le_iSup (fun l : p.L₂ => d.toTypeRuSetup.U.map (MulAut.conj (l:G)).toMonoidHom)
    ⟨s.g,s.in_residual⟩

theorem SourceChoice.displacement_le_W₀ (s : SourceChoice p) : s.displacement ≤ p.W₀ := by
  have hQT : d.toTypeRuSetup.Q ≤ (d.T : Subgroup G) := p.R₂_sup_Q ▸ le_sup_right
  rw [SourceChoice.displacement,commutator_comm]
  exact (commutator_mono s.Uα_le_W₀ le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (hQT.trans (p.sylow_le_parabolic.trans p.W₀_normalized)))

abbrev SourceChoice.centralDisplacement (s : SourceChoice p) : Subgroup (Hat d) :=
  hat d s.displacement ⊔ center (Hat d)

theorem SourceChoice.centralDisplacement_le_hat_W (s : SourceChoice p) :
    s.centralDisplacement ≤ hat d p.W :=
  sup_le (hat_mono d (s.displacement_le_W₀.trans p.W₀_le_W)) p.center_le_hat_W

theorem SourceChoice.centralDisplacement_le_hat_Q (s : SourceChoice p) :
    s.centralDisplacement ≤ hat d d.toTypeRuSetup.Q :=
  sup_le (hat_mono d s.displacement_le_Q) (center_le_hat_Q d)

theorem SourceChoice.centralDisplacement_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card s.centralDisplacement=8 := by
  have hc : center (Hat d) ≤ hat d d.toTypeRuSetup.HC := by
    rw [← hat_Q₀]
    exact hat_mono d (Q₀_le_HC d)
  have hn : center (Hat d) ≤ normalizer (hat d s.displacement : Set (Hat d)) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    exact mem_centralizer_iff.mpr (fun y _ => mem_center_iff.mp hx y)
  rw [SourceChoice.centralDisplacement,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn
    ((s.hat_displacement_disjoint_HC B5 hi).mono_right hc),
    s.hat_displacement_card B5 hi,center_hat_card]

theorem SourceChoice.hat_v_mem_W (s : SourceChoice p) :
    hatMap d s.vH ∈ hat d p.W :=
  mem_map.mpr ⟨s.vH,p.W₀_le_W (s.Uα_le_W₀ s.v_mem),rfl⟩

theorem SourceChoice.hat_v_not_Q (s : SourceChoice p) :
    hatMap d s.vH ∉ hat d d.toTypeRuSetup.Q := by
  intro h
  have hh : hatStar d (hatMap d s.vH)=1 := by
    exact MonoidHom.mem_ker.mp (hatStar_kernel d ▸ h)
  rw [hatStar_apply] at hh
  have hk : s.vH∈d.ru2.quotientMap.ker := hh
  rw [d.ru2.quotient_kernel] at hk
  exact s.v_not_Q hk

abbrev SourceChoice.spanFour (s : SourceChoice p) : Subgroup (Hat d) :=
  s.centralDisplacement ⊔ zpowers (hatMap d s.vH)

theorem SourceChoice.spanFour_le_hat_W (s : SourceChoice p) : s.spanFour ≤ hat d p.W :=
  sup_le s.centralDisplacement_le_hat_W (zpowers_le.mpr s.hat_v_mem_W)

theorem SourceChoice.spanFour_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card s.spanFour = 16 := by
  let := p.hat_W_elementary
  have hn : hatMap d s.vH ∈ normalizer (s.centralDisplacement : Set (Hat d)) := by
    apply Subgroup.centralizer_le_normalizer
    exact mem_centralizer_iff.mpr (fun y hy =>
      setLike_mul_comm (s.centralDisplacement_le_hat_W hy) s.hat_v_mem_W)
  have hv2 : (hatMap d s.vH)^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian _ s.hat_v_mem_W
  rw [SourceChoice.spanFour,card_sup_zpowers_of_normalizing_involution _ _ hv2
    (fun h => s.hat_v_not_Q (s.centralDisplacement_le_hat_Q h)) hn,
    s.centralDisplacement_card B5 hi]

theorem SourceChoice.spanFour_inf_hat_Q₅ (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    s.spanFour ⊓ hat d (Q₅ d B5) = hat d s.displacement := by
  let := p.hat_W_elementary
  have hn : zpowers (hatMap d s.vH) ≤ normalizer (s.centralDisplacement : Set (Hat d)) := by
    apply zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    exact mem_centralizer_iff.mpr (fun y hy =>
      setLike_mul_comm (s.centralDisplacement_le_hat_W hy) s.hat_v_mem_W)
  have hc : center (Hat d) ≤ normalizer (hat d s.displacement : Set (Hat d)) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact fun x hx => mem_centralizer_iff.mpr (fun y _ => mem_center_iff.mp hx y)
  have hvorder : orderOf (hatMap d s.vH)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ s.hat_v_mem_W)
    (fun h => s.hat_v_not_Q (h ▸ (hat d d.toTypeRuSetup.Q).one_mem))
  have hvdis := (hat d d.toTypeRuSetup.Q).disjoint_zpowers_of_prime_order_not_mem
    _ hvorder s.hat_v_not_Q
  have hdis : Disjoint (hat d (Q₅ d B5)) (center (Hat d)) := by
    apply (hat_Q_split d B5).2.symm.mono_right
    rw [← hat_HC_eq_hat_CQ]
    rw [← hat_Q₀]
    exact hat_mono d (Q₀_le_HC d)
  apply le_antisymm
  · intro x hx
    have hxprod : x∈(s.centralDisplacement:Set (Hat d))*
        (zpowers (hatMap d s.vH):Set (Hat d)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
      exact hx.1
    obtain ⟨a,ha,b,hb,hab⟩ := hxprod
    have hbQ : b ∈ hat d d.toTypeRuSetup.Q := by
      have he : b=a⁻¹*x := by rw [← hab]; group
      rw [he]
      exact mul_mem (inv_mem (s.centralDisplacement_le_hat_Q ha))
        (hat_mono d (Q₅_le_Q d B5) hx.2)
    have hbe : b=1 := disjoint_def.mp hvdis hbQ hb
    have hax : a=x := by simpa only [hbe,mul_one] using hab
    have haprod : a∈(hat d s.displacement:Set (Hat d))*(center (Hat d):Set (Hat d)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hc]
      exact ha
    obtain ⟨e,he,z,hz,hez⟩ := haprod
    have hzQ5 : z∈hat d (Q₅ d B5) := by
      have heq : z=e⁻¹*x := by rw [← hax,← hez]; group
      rw [heq]
      exact mul_mem (inv_mem (hat_mono d (s.commutator_Q_Uα_le_Q₅ B5 hi) he)) hx.2
    have hze : z=1 := disjoint_def.mp hdis hzQ5 hz
    have hex : e=x := by simpa only [hze,mul_one] using hez.trans hax
    exact hex ▸ he
  · exact le_inf (le_sup_left.trans le_sup_left)
      (hat_mono d (s.commutator_Q_Uα_le_Q₅ B5 hi))

end CFSG.Quasithin.ChapterJ.RuSubgroup
