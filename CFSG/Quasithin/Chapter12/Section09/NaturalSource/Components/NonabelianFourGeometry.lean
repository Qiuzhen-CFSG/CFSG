module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianRadicals
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.Representation.BinaryHyperplaneDisplacement.NormalFour
public import Theory.Representation.BinaryPermutation.EightMarkedDisplacement

/-!
# The irreducible conjugate-center four-group in 12.9.4

The original point residual acts as the full GL₃(2) on the seed. Its literal
intersection with the dotted point stabilizer lies in the original H ∩ G₂
image, so it normalizes the conjugate center. Hyperplane displacement encodes
that center in a two-dimensional dual annihilator, bounding its order by four.
An order-two invariant subgroup would give an invariant plane for the full
GL₃(2) point stabilizer. Thus the center image is an irreducible four-group.

The original conjugation-induced quotient equivalence then gives order four
for Z(U) modulo its intersection with Z(U)ᵍ and V₁, as in source equation (*).
This proves the order and irreducibility used in the orthogonal branch without
enumerating both whole parabolic radicals. The original minimal-parabolic
transport and contradiction, catalogue exhaustion and LocalControlInput remain
with the natural-branch assembly owner.

Source: Aschbacher--Smith 12.8.10--13 and 12.9.4, printed pp.854--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original conjugate-center image embeds into the two-dimensional
annihilator of the seed in its centralizer hyperplane. -/
theorem nonabelian_caseFive_center_card_le_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    Nat.card (F.terminalDot (conjugate F.ZU g)) ≤ 4 := by
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,htrans,hfull,hfixed,hWX,hperp,hrank⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  obtain ⟨_,he,hd⟩ := nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5
  obtain ⟨q,c,e,hequiv⟩ := nonabelian_caseFive_marking h hn earlier F hne B₀ h5
  let D := F.terminalDot (conjugate F.ZU g)
  have hDX : D ≤ F.terminalDot (F.X g) := map_mono (comap_mono (F.conjugate_ZU_le_X g))
  let ρ := F.terminalRepresentation.comp D.subtype
  have hlower (a : D) (ha : a ≠ 1) :
      2 ≤ finrank (ZMod 2) (ρ a - LinearMap.id).range := by
    apply BinaryPermutation.EightOrthogonalActors.marked_two_le_displacement
      F.terminalRepresentation e c.toLinearEquiv hequiv a
      (fun hh => ha (Subtype.ext hh))
    exact elemPow_eq_one_of_isElementaryAbelian (A := F.terminalDot (F.X g)) (p := 2) a (hDX a.property)
  have hWH : hatSpace F V ≤ hatSpace F F.W := by
    rw [hperp]
    intro w hw
    exact hiso v v.property w (he.symm ▸ hw)
  have hBv : B (v : Additive F.Uhat) ≠ 0 := by
    intro hz
    apply hv
    exact hB.1 _ (fun w => LinearMap.congr_fun hz w)
  have hH := Module.Dual.finrank_ker_add_one_of_ne_zero hBv
  rw [←hperp] at hH
  have hfix (a : D) (w : Additive F.Uhat) (hw : w ∈ hatSpace F V) : ρ a w = w :=
    nonabelian_caseFive_center_fixes_intersection h hn earlier F hne g hgP hgH B₀ h5
      a a.property w (he.symm ▸ hw)
  have hmove (a : D) (w : Additive F.Uhat) (hw : w ∈ hatSpace F F.W) :
      ρ a w - w ∈ Submodule.span (ZMod 2) {(v : Additive F.Uhat)} := by
    rw [←hline]
    exact nonabelian_center_hyperplane_displacement h earlier F hne g hgP hgH a a.property w hw
  have hc := BinaryHyperplaneDisplacement.card_le_of_fixed_seed
    ρ hlower (hatSpace F V) (hatSpace F F.W) hWH hH v hv hfix hmove
  have hseed : finrank (ZMod 2) (hatSpace F V) = 3 := he ▸ hd
  have hhyper : finrank (ZMod 2) (hatSpace F F.W) = 5 := by rw [h5.1] at hH; omega
  simpa [hseed,hhyper,D] using hc



/-- Nontriviality and the binary order bound leave only orders two and four. -/
theorem nonabelian_caseFive_center_order
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    Nat.card (F.terminalDot (conjugate F.ZU g)) = 2 ∨
      Nat.card (F.terminalDot (conjugate F.ZU g)) = 4 := by
  obtain ⟨hX,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  have hDX : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hp := (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g))).of_injective
    (inclusion hDX) (inclusion_injective hDX)
  have hlo := (one_lt_card_iff_ne_bot _).mpr
    (nonabelian_caseFive_center h hn earlier F hne g hgP hgH B₀ h5).2
  have hhi := nonabelian_caseFive_center_card_le_four h hn earlier F hne g hgP hgH B₀ h5
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  rw [hk] at hlo hhi ⊢
  have hk2 : k ≤ 2 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ k)
    norm_num at hh'
    omega
  interval_cases k <;> norm_num at *

private theorem plane_normalizer_of_fixed_hat
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (a : F.H) (haV : (a:G) ∈ normalizer (V : Set G))
    (haf : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v = v) :
    (a:G) ∈ F.Gi 2 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  have forward (b : F.H) (hbV : (b:G) ∈ normalizer (V : Set G))
      (hbf : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker b) v = v)
      (w : G) (hw : w ∈ F.Vi 2) : (b:G)*w*(b:G)⁻¹ ∈ F.Vi 2 := by
    let u : F.U := ⟨w,(F.le_seed 2).trans (le_conjugateSpanBy V F.H) hw⟩
    have hu : hatElement F u ∈ hatSpace F (F.Vi 2) := ⟨u,hw,rfl⟩
    rw [hline] at hu
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hu
    have hh : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker b)
        (hatElement F u) = hatElement F u := by rw [←hc,map_smul,hbf]
    have hq := congrArg Additive.toMul hh
    rw [F.terminalRepresentation_apply_mk] at hq
    change F.terminalHatAction b (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U) u at hq
    rw [F.terminalHatAction_apply_mk] at hq
    have hz : F.uAction b u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hq
    have hzG : ((F.uAction b u / u : F.U):G) ∈ F.Vi 1 := by
      rw [←hcenter]
      exact ⟨V.div_mem ((mem_normalizer_iff.mp hbV w).mp (F.le_seed 2 hw))
        (F.le_seed 2 hw),mem_map_of_mem F.U.subtype hz⟩
    have hhG := (F.Vi 2).mul_mem (F.monotone (by omega : 1 ≤ 2) hzG) hw
    simpa only [Subgroup.coe_div,F.uAction_apply,u,div_mul_cancel] using hhG
  apply mem_normalizer_iff.mpr
  intro w
  constructor
  · exact forward a haV haf w
  · intro hw
    have hfi : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a⁻¹) v = v := by
      have hh := congrArg (F.terminalRepresentation
        (QuotientGroup.mk' F.terminalHatAction.ker a)⁻¹) haf
      simpa only [map_inv,Representation.inv_self_apply] using hh.symm
    have hh := forward a⁻¹ ((normalizer (V : Set G)).inv_mem haV) hfi
      ((a:G)*w*(a:G)⁻¹) hw
    simpa only [Subgroup.coe_inv,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh

/-- The literal intersection of the two parabolics lies in the original
point-plane image, with no change to the quotient map. -/
theorem nonabelian_parabolic_intersection_le_dot_H2
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ F.terminalPointCentralizer v ≤
      F.terminalDot (F.H ⊓ F.Gi 2) := by
  have hnorm : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
    sup_le (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
      (h.sylow_normalizes_seed earlier.structural)
  rintro _ ⟨⟨a,ha,rfl⟩,hfix⟩
  exact ⟨a,⟨a.property,plane_normalizer_of_fixed_hat h F hne v hline a (hnorm ha) hfix⟩,rfl⟩

/-- The conjugate-center image is normal relative to the exact intersection
of the seed and point parabolics. This is the action group for the remaining
order-two exclusion, not ambient normality. -/
theorem nonabelian_caseFive_center_normal_in_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∃ v : Additive F.Uhat, v ≠ 0 ∧
      hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      F.terminalDot (conjugate F.ZU g) ≤
        F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ F.terminalPointCentralizer v ∧
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf
        (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ F.terminalPointCentralizer v)).Normal := by
  obtain ⟨v,hv,hline,_,hle⟩ := nonabelian_caseFive_center_le_twoCores h hn earlier F hne g hgP hgH B₀ h5
  have hDP := hle.trans (inf_le_inf (pCoreIn_le _ _) (pCoreIn_le _ _))
  obtain ⟨_,_,hDH,hDN⟩ := nonabelian_actors_normal h earlier F hne g hgP
  refine ⟨v,hv,hline,hDP,(normal_subgroupOf_iff_le_normalizer hDP).mpr ?_⟩
  exact (nonabelian_parabolic_intersection_le_dot_H2 h earlier F hne v hline).trans
    ((normal_subgroupOf_iff_le_normalizer hDH).mp hDN)



private theorem surjective_of_full_core_quotient
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hk : IsPGroup 2 f.ker)
    (hc : Nat.card (A ⧸ pCore 2 A) = Nat.card B) : Function.Surjective f := by
  have hk' : IsPGroup 2 f.rangeRestrict.ker := by
    let eK := MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict f)
    exact hk.of_injective eK.toMonoidHom eK.injective
  let e := f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hk'
  have hq : Nat.card (f.range ⧸ pCore 2 f.range) = Nat.card B :=
    (Nat.card_congr e.toEquiv).symm.trans hc
  have hle : Nat.card B ≤ Nat.card f.range := by
    rw [←hq]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 f.range))
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq f.range
    (Nat.le_antisymm f.range.card_le_card_group hle))

/-- The original point residual induces every linear automorphism on the
unchanged three-dimensional seed in the central quotient. -/
theorem nonabelian_caseFive_full_seed_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∀ φ : hatSpace F V ≃ₗ[ZMod 2] hatSpace F V,
      ∃ a : F.terminalDot (F.Li L 1), ∀ w : hatSpace F V,
        F.terminalRepresentation a w = (φ w : Additive F.Uhat) := by
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,_⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  obtain ⟨hn4,he,hd⟩ := nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5
  let W := hatSpace F V
  let C := F.terminalDot (F.Li L 1)
  let S := BinaryOffender.subspaceStabilizer F.terminalRepresentation W
  have hdim : finrank (ZMod 2) W = 3 := by
    change finrank (ZMod 2) (hatSpace F V) = 3
    rw [←he]
    exact hd
  have hCS : C ≤ S := by
    change C ≤ BinaryOffender.subspaceStabilizer F.terminalRepresentation (hatSpace F V)
    rw [←(nonabelian_caseFive_seed_stabilizer h hn earlier F hne g hgP hgH B₀ h5).1]
    exact map_mono (comap_mono le_sup_left)
  have hW : W = B.orthogonal W := by
    have hl : W ≤ B.orthogonal W := by
      intro w hw u hu
      exact hiso u (he.symm ▸ hu) w (he.symm ▸ hw)
    apply Submodule.eq_of_le_of_finrank_eq hl
    rw [LinearMap.BilinForm.finrank_orthogonal hB,h5.1,hdim]
  let f : C →* (W ≃ₗ[ZMod 2] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
      ((BinaryOffender.stabilizerRepresentation F.terminalRepresentation W).asGroupHom.comp
        (inclusion hCS))
  have hfeval (a : C) (w : W) : (f a w : Additive F.Uhat) = F.terminalRepresentation a w := rfl
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* BinaryOffender.subspaceKernel F.terminalRepresentation W C :=
      { toFun := fun a => ⟨a.val.val,a.val.property,by
          intro w hw
          have hh := congrArg (fun t : W ≃ₗ[ZMod 2] W => (t ⟨w,hw⟩ : Additive F.Uhat)) a.property
          exact hh⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    exact (BinaryIsometryRadicals.halfSpace_kernel_isPGroup F.terminalRepresentation
      F.terminalRepresentation_injective B hInv W hW C).of_injective j
        (by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun x : BinaryOffender.subspaceKernel F.terminalRepresentation W C =>
            (x : F.TerminalHdot)) hab)
  have hc : Nat.card (C ⧸ pCore 2 C) = Nat.card (W ≃ₗ[ZMod 2] W) := by
    rw [Theory.LinearAlgebra.BinaryFourPointStabilizer.card_linearGroup_three hdim]
    have hh := point_hat_core_card h hn F hne
    rw [if_pos hn4] at hh
    exact hh
  have hf := surjective_of_full_core_quotient f hk hc
  intro φ
  obtain ⟨a,ha⟩ := hf φ
  refine ⟨a,?_⟩
  intro w
  rw [←hfeval,ha]



/-- The conjugate center is an irreducible four-group under the exact
intersection of the point and seed parabolics. All action and normality
premises are constructed from the original nonabelian flag. -/
theorem nonabelian_caseFive_center_four_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∃ v : Additive F.Uhat, v ≠ 0 ∧
      hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      IsElementaryAbelian 2 (F.terminalDot (conjugate F.ZU g)) ∧
      Nat.card (F.terminalDot (conjugate F.ZU g)) = 4 ∧
      let J := F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ F.terminalPointCentralizer v
      F.terminalDot (conjugate F.ZU g) ≤ J ∧
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf J).Normal ∧
      ∀ A : Subgroup F.TerminalHdot, A ≤ F.terminalDot (conjugate F.ZU g) →
        J ≤ normalizer (A : Set F.TerminalHdot) → A = ⊥ ∨ A = F.terminalDot (conjugate F.ZU g) := by
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,htrans,hfull,hfixed,hWX,hperp,hrank⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  obtain ⟨_,he,hd⟩ := nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5
  obtain ⟨q,c,e,hequiv⟩ := nonabelian_caseFive_marking h hn earlier F hne B₀ h5
  let W := hatSpace F V
  let P := F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))
  let D := F.terminalDot (conjugate F.ZU g)
  let J := P ⊓ F.terminalPointCentralizer v
  have hdim : finrank (ZMod 2) W = 3 := by
    change finrank (ZMod 2) (hatSpace F V) = 3
    rw [←he]
    exact hd
  have hvW : (v : Additive F.Uhat) ∈ W := by
    change (v : Additive F.Uhat) ∈ hatSpace F V
    rw [←he]
    exact v.property
  have hW : W = B.orthogonal W := by
    have hl : W ≤ B.orthogonal W := by
      intro w hw u hu
      exact hiso u (he.symm ▸ hu) w (he.symm ▸ hw)
    apply Submodule.eq_of_le_of_finrank_eq hl
    rw [LinearMap.BilinForm.finrank_orthogonal hB,h5.1,hdim]
  have hDX : D ≤ F.terminalDot (F.X g) := map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hfix : ∀ a ∈ D, ∀ w ∈ W, F.terminalRepresentation a w = w := by
    intro a ha w hw
    exact nonabelian_caseFive_center_fixes_intersection h hn earlier F hne g hgP hgH B₀ h5
      a ha w (he.symm ▸ hw)
  have hDJ : D ≤ J := le_inf (hDX.trans (map_mono (comap_mono (hXT.trans le_sup_right))))
    (fun a ha => hfix a ha v hvW)
  obtain ⟨_,_,hDH,hDN⟩ := nonabelian_actors_normal h earlier F hne g hgP
  have hJD : J ≤ normalizer (D : Set F.TerminalHdot) :=
    (nonabelian_parabolic_intersection_le_dot_H2 h earlier F hne v hline).trans
      ((normal_subgroupOf_iff_le_normalizer hDH).mp hDN)
  have noTwo (A : Subgroup F.TerminalHdot) (hAD : A ≤ D)
      (hJA : J ≤ normalizer (A : Set F.TerminalHdot)) : Nat.card A ≠ 2 := by
    apply BinaryHyperplaneDisplacement.not_card_two_of_full_seed_action
      F.terminalRepresentation B hB hInv W hdim hW ⟨v,hvW⟩ hv P A
    · intro φ
      obtain ⟨a,ha⟩ := nonabelian_caseFive_full_seed_action h hn earlier F hne g hgP hgH B₀ h5 φ
      exact ⟨a,map_mono (comap_mono le_sup_left) a.property,ha⟩
    · intro s hs hsv
      exact hJA ⟨hs,hsv⟩
    · intro a ha
      exact hfix a (hAD ha)
    · intro a ha w hw
      rw [←hline]
      apply nonabelian_center_hyperplane_displacement h earlier F hne g hgP hgH a (hAD ha)
      rwa [hperp]
    · intro a ha ha1
      exact BinaryPermutation.EightOrthogonalActors.marked_two_le_displacement
        F.terminalRepresentation e c.toLinearEquiv hequiv a ha1
        (elemPow_eq_one_of_isElementaryAbelian (A := F.terminalDot (F.X g)) (p := 2)
          a (hDX (hAD ha)))
  have hc : Nat.card D = 4 :=
    (nonabelian_caseFive_center_order h hn earlier F hne g hgP hgH B₀ h5).resolve_left
      (noTwo D le_rfl hJD)
  have hDE : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.of_injective (inclusion hDX) (inclusion_injective hDX)
  refine ⟨v,hv,hline,hDE,hc,hDJ,(normal_subgroupOf_iff_le_normalizer hDJ).mpr hJD,?_⟩
  intro A hAD hJA
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  have hlo := (one_lt_card_iff_ne_bot A).mpr hbot
  have hhi := card_le_of_le hAD
  have hdvd := card_dvd_of_le hAD
  rw [hc] at hhi hdvd
  have htwo := noTwo A hAD hJA
  have hAc : Nat.card A = 4 := by
    by_contra hh
    have h3 : Nat.card A = 3 := by omega
    rw [h3] at hdvd
    norm_num at hdvd
  apply eq_of_le_of_card_ge hAD
  rw [hc,hAc]

/-- The symmetry quotient in the source equation (*) has order four under
the unchanged original conjugation map. -/
theorem nonabelian_caseFive_center_quotient_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    Nat.card (F.ZU ⧸ ((F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1).subgroupOf F.ZU) = 4 := by
  obtain ⟨v,hv,hline,_,hc,_⟩ := nonabelian_caseFive_center_four_geometry h hn earlier F hne g hgP hgH B₀ h5
  rw [nonabelian_center_quotient_card h earlier F hne g hgP hgH]
  exact hc

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
