module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CenterSpan
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Action
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients
public import Theory.ElementaryAbelian.Join

/-!
# The two original conjugate closures meet in V

The preceding Frattini theorem identifies the Frattini subgroups of U and
U^g with distinct flag points. Their intersection is therefore elementary.
Its image in U/Z(U) is isotropic in the nondegenerate four-dimensional
commutator space, so has order at most four. The cyclic center contributes
only its unique involution, giving intersection order at most eight.
The original seed already has order eight and lies in both closures.

The result concerns U intersect U^g itself, as required at the start of
14.3.33, and also identifies the previously defined E=W intersect W^g.
All structural predecessors are at the original G,T; the only local-model
input is the preceding LocalStructure. Source: Aschbacher--Smith,
14.3.33, printed p.1004, using 12.8.4 and 12.8.11.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Square-one elements in the original cyclic center form the marked point. -/
theorem center_involution_mem_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    {x : G} (hx : x ∈ F.ZU) (hx2 : x ^ 2 = 1) : x ∈ F.Vi 1 := by
  obtain ⟨e⟩ := s.core_shape.center_model
  let := e.isCyclic.mpr inferInstance
  have hc : Nat.card (center F.U) = 4 :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  rw [← center_squares_eq_point h F s]
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨u, (mem_centralSquares_iff hc u).mpr ⟨hu, Subtype.ext hx2⟩, rfl⟩

private theorem elementary_extension_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hVA : V ≤ A) (hAU : A ≤ F.U) :
    A = V := by
  let := h.chosen.elementary
  have hp : IsPGroup 2 F.U := IsPGroup.of_card (n := 6) s.core_shape.card
  let := F.uhat_elementary_of_point (by decide) hp hphi
  let B := F.uhatBilinearForm (by decide) hp hphi
  have hi : ∀ x ∈ hatSpace F A, ∀ y ∈ hatSpace F A, B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, hea⟩ := (show x.toMul ∈ hatImage F A from hx)
    obtain ⟨b, hb, heb⟩ := (show y.toMul ∈ hatImage F A from hy)
    have hab : Commute a b := by
      apply Subtype.ext
      exact congrArg (fun v : A => (v : G)) (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
    have hz : F.uhatCommutator hp (QuotientGroup.mk' (center F.U) a)
        (QuotientGroup.mk' (center F.U) b) = 1 := by
      apply Subtype.ext
      rw [F.uhatCommutator_apply_mk]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hab.eq
    change B (Additive.ofMul x.toMul) (Additive.ofMul y.toMul) = 0
    rw [← hea, ← heb, F.uhatBilinearForm_apply, hz]
    simp only [map_one]
    rfl
  have hb := B.twice_finrank_le_of_isotropic
    (F.uhatBilinearForm_nondegenerate (by decide) hp hphi) (hatSpace F A) hi
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod] at hh
    have hc : Nat.card F.Uhat = 16 := NaturalCoordinates.card_uhat F s.natural
    have he : 2 ^ 4 = 2 ^ Module.finrank (ZMod 2) (Additive F.Uhat) := hc.symm.trans hh
    exact (Nat.pow_right_injective (by decide) he).symm
  rw [hd] at hb
  have hk : (hatMap F A hAU).ker = (F.Vi 1).subgroupOf A := by
    rw [hatMap_ker]
    ext x
    change (x : G) ∈ F.ZU ↔ (x : G) ∈ F.Vi 1
    exact ⟨fun hx => center_involution_mem_point h F s hx
      (elemPow_eq_one_of_isElementaryAbelian _ x.property), fun hx => F.point_le_ZU (by decide) hx⟩
  have hkc : Nat.card (hatMap F A hAU).ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe ((F.le_seed 1).trans hVA)).toEquiv]
    simpa using F.card 1 (by decide)
  have hAc := (hatMap F A hAU).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (hatMap_surjective F A hAU), card_top, hkc] at hAc
  have himg : Nat.card (hatImage F A) ≤ 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F A)
    rw [Nat.card_zmod] at hh
    change Nat.card (hatSpace F A) ≤ 2 ^ 2
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hvc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  exact (eq_of_le_of_card_ge hVA (by omega)).symm


/-- The literal conjugate closures have exactly the original seed in common. -/
theorem closure_intersection_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.U ⊓ conjugate F.U g = V := by
  let := h.chosen.elementary
  have hp : IsPGroup 2 F.U := IsPGroup.of_card (n := 6) s.core_shape.card
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L
    (normalizer (L : Set G)) (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives) hne
  have hVZ : V ⊓ F.ZU = F.Vi 1 := by
    let := F.localKernel_tilde_seed_elementary
    exact F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne
  have hgV := F.P_le_seed_normalizer L h.chosen.normalizes hgP
  let A := F.U ⊓ conjugate F.U g
  have hVA : V ≤ A := by
    apply le_inf (le_conjugateSpanBy V F.H)
    exact ((conjugate_eq_iff V g).mpr hgV).symm.le.trans
      (map_mono (le_conjugateSpanBy V F.H))
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi, map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
      (F.le_seed 1).trans (le_conjugateSpanBy V F.H))]
  have hdis : Disjoint (conjugate (F.Vi 1) g) (F.Vi 1) :=
    (disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) hVZ g hgV hgH)).mono_right
      (F.point_le_ZU (by decide))
  have hPhiA : frattini A = ⊥ := by
    apply frattini_eq_bot_of_disjoint_images hp (hp.map (MulAut.conj g⁻¹).toMonoidHom)
      (show A ≤ F.U from inf_le_left) (show A ≤ conjugate F.U g from inf_le_right)
    rw [frattini_image_map F.U _ (MulAut.conj g⁻¹).injective, hPhi]
    exact hdis.symm
  let : Fact (IsPGroup 2 A) := ⟨hp.to_le inf_le_left⟩
  let : IsElementaryAbelian 2 A := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hPhiA
  exact elementary_extension_eq_seed h F s hphi A hVA inf_le_left

/-- Apply the full-intersection result to the literal parabolic E=W∩W^g. -/
theorem parabolic_intersection_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  let := h.chosen.elementary
  apply le_antisymm
  · exact (le_inf (show F.E g ≤ F.U from inf_le_left.trans inf_le_left)
      (inf_le_right.trans (map_mono (show F.W ≤ F.U from inf_le_left)))).trans_eq
        (closure_intersection_eq_seed h structural alternatives F s hne g hgP hgH)
  · exact F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L h.chosen.normalizes hgP)

/-- The original seed has centralizer VZ(U) inside U. -/
theorem seed_centralizer_in_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    F.U ⊓ centralizer (V : Set G) = V ⊔ F.ZU := by
  let := h.chosen.elementary
  have hp : IsPGroup 2 F.U := IsPGroup.of_card (n := 6) s.core_shape.card
  let : Fact (IsPGroup 2 F.U) := ⟨hp⟩
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L
    (normalizer (L : Set G)) (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives) hne
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  have hZU : F.ZU ≤ F.U := map_subtype_le _
  have hZC : F.ZU ≤ centralizer (V : Set G) :=
    (centerIn_le_centralizer F.U).trans (centralizer_le hVU)
  apply le_antisymm
  · intro x hx
    have hx2 : (x⁻¹) ^ 2 ∈ F.Vi 1 := by
      have hh := pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x, hx.1⟩ : F.U)⁻¹
      rw [hphi] at hh
      exact hh
    have hxroot : (x⁻¹) ^ 2 ∈ (centralSquares F.U).map F.U.subtype :=
      (center_squares_eq_point h F s).symm ▸ hx2
    obtain ⟨a, ha, hea⟩ := hxroot
    obtain ⟨z, rfl⟩ := mem_centralSquares.mp ha
    have hz : (z.val : G) ∈ F.ZU := mem_map_of_mem F.U.subtype z.property
    have hroot : (z.val : G) ^ 2 = (x⁻¹) ^ 2 := hea
    let y : G := x * z.val
    have hyU : y ∈ F.U := F.U.mul_mem hx.1 (hZU hz)
    have hxy : Commute x (z.val : G) := by
      exact (centerIn_le_centralizer F.U hz x hx.1)
    have hy2 : y ^ 2 = 1 := by
      change (x * (z.val : G)) ^ 2 = 1
      rw [hxy.mul_pow, hroot, inv_pow, mul_inv_cancel]
    have hyC : y ∈ centralizer (V : Set G) :=
      (centralizer (V : Set G)).mul_mem hx.2 (hZC hz)
    let : IsElementaryAbelian 2 (zpowers y) := IsElementaryAbelian.zpowers_of_pow_eq_one hy2
    let : IsElementaryAbelian 2 (V ⊔ zpowers y : Subgroup G) :=
      IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hyC)
    have he := elementary_extension_eq_seed h F s hphi (V ⊔ zpowers y)
      le_sup_left (sup_le hVU (zpowers_le.mpr hyU))
    have hyv : y ∈ V := he ▸ (mem_sup_right (mem_zpowers y))
    have hh := (V ⊔ F.ZU).mul_mem (mem_sup_left hyv) (mem_sup_right (F.ZU.inv_mem hz))
    simpa only [y, mul_inv_cancel_right] using hh
  · exact sup_le (le_inf hVU (le_centralizer V)) (le_inf hZU hZC)

/-- The center span meets the original closure in precisely VZ(U). -/
theorem centerSpan_inf_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    centerSpan L F ⊓ F.U = V ⊔ F.ZU := by
  apply le_antisymm
  · exact (le_inf inf_le_right (inf_le_left.trans
      ((centerSpan_le_core h structural F s).trans h.chosen.core_centralizes))).trans_eq
        (seed_centralizer_in_closure h structural alternatives F s hne)
  · exact sup_le (le_inf (seed_le_centerSpan h F) (le_conjugateSpanBy V F.H))
      (le_inf (le_conjugateSpanBy F.ZU L) (map_subtype_le _))

/-- The original center span has intersection of order sixteen with U. -/
theorem centerSpan_inf_closure_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) : Nat.card (centerSpan L F ⊓ F.U : Subgroup G) = 16 := by
  let := h.chosen.elementary
  have hVZ : V ⊓ F.ZU = F.Vi 1 := by
    apply le_antisymm
    · intro v hv
      exact center_involution_mem_point h F s hv.2
        (elemPow_eq_one_of_isElementaryAbelian v hv.1)
    · exact le_inf (F.le_seed 1) (F.point_le_ZU (by decide))
  obtain ⟨e⟩ := center_model F s
  have hz : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hn : F.ZU ≤ normalizer (V : Set G) :=
    ((centerIn_le_centralizer F.U).trans (centralizer_le (le_conjugateSpanBy V F.H))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes V F.ZU hn
  rw [hVZ, hz, hv, hp] at hc
  rw [centerSpan_inf_closure h structural alternatives F s hne]
  omega

/-- The literal O₂(LT) intersection needed for the marked G.2.5 core product. -/
theorem join_core_inf_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ F.U = V ⊔ F.ZU := by
  let := h.chosen.elementary
  have hU : F.U ≤ L ⊔ (T : Subgroup G) := (closure_le_sylow F s).trans le_sup_right
  rw [← h.centralizer_LT_at structural]
  have he : ((L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G)) ⊓ F.U =
      F.U ⊓ centralizer (V : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hU hx.1, hx.2⟩, hx.1⟩⟩
  exact he.trans (seed_centralizer_in_closure h structural alternatives F s hne)

/-- The same sixteen is the original core intersection, before identifying the whole core. -/
theorem join_core_inf_closure_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ F.U : Subgroup G) = 16 := by
  rw [join_core_inf_closure h structural alternatives F s hne,
    ← centerSpan_inf_closure h structural alternatives F s hne]
  exact centerSpan_inf_closure_card h structural alternatives F s hne

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
