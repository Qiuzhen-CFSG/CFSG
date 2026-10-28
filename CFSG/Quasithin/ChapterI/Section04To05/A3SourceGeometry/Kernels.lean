module

public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry.Local
public import Theory.GroupTheory.MinimalFourCoreKernel
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# Unique A₃ lines and a faithful point action

The point-line core product gives index two for the point-core line kernel.
If the point group normalized this kernel, its image in a plane parabolic
would have order at most two inside an irreducible four-group. The image
must vanish, contradicting the nontrivial line action. Maximality then
separates the kernels on different lines. The three-point kernel argument
gives unique lines, and D4 makes the point action faithful.

Source: Aschbacher–Smith I.5.7(6)–I.5.8, printed p.421. As in the C₃
proof in Residues.KernelNonNormal, the required index is in Q₀, correcting
the printed index in Q₁. All actions are on the original coset spaces.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] (S : DSystem .A3 G)

theorem a3_point_line_kernel_card :
    Nat.card (S.Q 0) = Nat.card (S.Q 0 ⊓ S.Q 1 : Subgroup G) * 2 := by
  have h := S.a3_core_card_product 0 1
  rw [← S.a3_point_line_core_join] at h
  have hc := S.a3_line_pair_core_card 0 (Or.inl rfl)
  have hc' : Nat.card ((S.pair 0 1).pCoreIn 2) = Nat.card (S.Q 1) * 2 := by
    simpa only [pair, inf_comm] using hc
  rw [hc'] at h
  let : Finite (S.Q 1) := Finite.of_injective
    (inclusion ((S.family 1).pCoreIn_le 2)) (inclusion_injective _)
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := S.Q 1))
  calc
    Nat.card (S.Q 0) * Nat.card (S.Q 1) = _ := h
    _ = (Nat.card (S.Q 0 ⊓ S.Q 1 : Subgroup G) * 2) * Nat.card (S.Q 1) := by ring

theorem a3_point_core_not_le_lineCore : ¬ S.Q 0 ≤ S.Q 1 := by
  intro h
  have hc := S.a3_point_line_kernel_card
  rw [inf_eq_left.mpr h] at hc
  let : Finite (S.Q 0) := Finite.of_injective
    (inclusion ((S.family 0).pCoreIn_le 2)) (inclusion_injective _)
  have hp := Nat.card_pos (α := S.Q 0)
  omega

theorem a3_point_core_not_le_planeCore : ¬ S.Q 0 ≤ S.Q 2 := by
  intro h
  apply S.a3_point_core_not_le_lineCore
  intro g hg
  have hk : g ∈ S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y S.baseLine} := by
    refine ⟨hg, (mem_fixingSubgroup_iff G).mpr ?_⟩
    intro y hy
    exact S.core_fixes_incident_coset 2 0 (by decide) (h hg)
      (CosetGeometry.Incident.symm S.family (S.point_line_plane hy
        (show S.Inc S.baseLine S.basePlane from ⟨1, rfl, rfl⟩)))
  rw [S.point_core_line_kernel] at hk
  exact hk.2

theorem a3_point_line_kernel_not_normalized :
    ¬ S.family 0 ≤ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) := by
  intro hn
  let N := S.Q 0 ⊓ S.Q 1
  have hN2 : N ≤ S.Q 2 := by
    apply (S.le_neighborCore_of_normalized_line_kernel N inf_le_left hn ?_).trans
      S.neighborCore_le_planeCore
    change S.Q 0 ⊓ S.Q 1 ≤ _
    rw [← S.point_core_line_kernel]
    exact inf_le_right
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  let f := S.pairQuotientMap 2 0 e
  have h0 : S.Q 0 ≤ S.pair 2 0 :=
    le_inf ((S.Q_le_T 0).trans (S.T_le 2)) ((S.family 0).pCoreIn_le 2)
  have hN : N ≤ S.pair 2 0 := inf_le_left.trans h0
  let Q := (S.Q 0).subgroupOf (S.pair 2 0)
  let R := N.subgroupOf (S.pair 2 0)
  let : Finite (S.pair 2 0) := Finite.of_injective
    (inclusion (show S.pair 2 0 ≤ S.family 2 from inf_le_left)) (inclusion_injective _)
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer h0).mpr
    (inf_le_right.trans (S.family_le_normalizer_Q 0))
  have hc : Nat.card Q = Nat.card R * 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h0).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv]
    exact S.a3_point_line_kernel_card
  have hRk : R ≤ f.ker := by
    rw [S.pairQuotientMap_ker]
    exact fun a ha => hN2 ha
  have hdata : Nat.card (pCore 2
      ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e))) = 4 ∧
      ∀ A : Subgroup ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e)),
        A.Normal → A ≤ pCore 2 _ → A = ⊥ ∨ A = pCore 2 _ := by
    rcases he with he | he
    · rw [he.1]
      refine ⟨Matrix.PSL3Two.pointParabolic_core_data.2, ?_⟩
      intro A hn hA
      let := hn
      exact Matrix.PSL3Two.pointParabolic_normal_le_core A hA
    · rw [he.1]
      refine ⟨Matrix.PSL3Two.lineParabolic_core_data.2, ?_⟩
      intro A hn hA
      let := hn
      exact Matrix.PSL3Two.lineParabolic_normal_le_core A hA
  have hQ := f.normal_two_le_ker_of_index_two (S.pairQuotientMap_surjective 2 0 e)
    Q R (((S.family 0).isPGroup_pCoreIn 2).comap_subtype)
    (fun _ ha => ha.1) hRk hc hdata.1 hdata.2
  rw [S.pairQuotientMap_ker] at hQ
  apply S.a3_point_core_not_le_planeCore
  intro g hg
  exact hQ (show (⟨g, h0 hg⟩ : S.pair 2 0) ∈ Q from hg)

theorem a3_point_fixer_fixes_lines
    (hunique : ∀ {x y : S.Point}, x ≠ y → ∀ {l m : S.Line},
      S.Inc x l → S.Inc y l → S.Inc x m → S.Inc y m → l = m)
    {g : G} (hg : ∀ x : S.Point, g • x = x) (l : S.Line) : g • l = l := by
  have hc := S.line_points_card l
  let : Finite {x : S.Point // S.Inc x l} := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  let : Nontrivial {x : S.Point // S.Inc x l} := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne {x : S.Point // S.Inc x l}
  apply hunique (x := x.val) (y := y.val) (fun he => hxy (Subtype.ext he))
  · simpa only [hg] using x.property.smul S g
  · simpa only [hg] using y.property.smul S g
  · exact x.property
  · exact y.property

theorem a3_faithful_points_of_unique_lines
    (hunique : ∀ {x y : S.Point}, x ≠ y → ∀ {l m : S.Line},
      S.Inc x l → S.Inc y l → S.Inc x m → S.Inc y m → l = m) :
    FaithfulSMul G S.Point := by
  let N := (MulAction.toPermHom G S.Point).ker
  have hNQ : N ≤ S.Q 0 := by
    intro g hg
    have hfix (x : S.Point) : g • x = x := Equiv.congr_fun hg x
    have hg0 : g ∈ S.family 0 := by
      rw [← S.stabilizer_basePoint]
      exact hfix S.basePoint
    let a : S.family 0 := ⟨g, hg0⟩
    have ha : a ∈ pCore 2 (S.family 0) := by
      rw [← S.a3_point_line_parabolic_normalCore, Subgroup.normalCore_eq_ker]
      apply Equiv.Perm.ext
      intro q
      apply (S.pointedCosetEquiv 0 1 (by decide)).injective
      apply Subtype.ext
      change (S.pointedCosetEquiv 0 1 (by decide) (a • q)).val = _
      rw [S.pointedCosetEquiv_smul]
      exact S.a3_point_fixer_fixes_lines hunique hfix _
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hbot : N = ⊥ := S.normal_eq_bot N (hNQ.trans (S.Q_le_T 0))
  have hinj := (MulAction.toPermHom G S.Point).ker_eq_bot_iff.mp hbot
  constructor
  intro g h he
  exact hinj (Equiv.ext he)

theorem a3_faithful_points_of_kernel_separation
    (hsep : ∀ l m : S.Line, S.Inc S.basePoint l → S.Inc S.basePoint m →
      S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z l} =
        S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z m} → l = m) :
    FaithfulSMul G S.Point :=
  S.a3_faithful_points_of_unique_lines (S.unique_line_of_kernel_separation hsep)

theorem a3_point_line_kernel_conjugate (l : S.Line) {a : G} (ha : a ∈ S.family 0) :
    (S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l}).map (MulAut.conj a).toMonoidHom =
      S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y (a • l)} := by
  have hset : a • {y : S.Point | S.Inc y l} = {y : S.Point | S.Inc y (a • l)} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change S.Inc (a⁻¹ • y) l ↔ S.Inc y (a • l)
    constructor
    · intro h
      simpa only [smul_inv_smul] using h.smul S a
    · intro h
      simpa only [inv_smul_smul] using h.smul S a⁻¹
  have hq : (S.Q 0).map (MulAut.conj a).toMonoidHom = S.Q 0 :=
    mem_normalizer_iff_map_conj_eq.mp (S.family_le_normalizer_Q 0 ha)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective, hq,
    SubMulAction.fixingSubgroup_map_conj_eq hset]

theorem a3_pair_normalizes_point_line_kernel :
    S.pair 0 1 ≤ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) :=
  (le_inf (inf_le_left.trans (S.family_le_normalizer_Q 0))
    (inf_le_right.trans (S.family_le_normalizer_Q 1))).trans
      inf_normalizer_le_normalizer_inf

theorem a3_base_line_eq_of_point_kernel_eq {l : S.Line} (hl : S.Inc S.basePoint l)
    (he : S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y S.baseLine} =
      S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l}) : S.baseLine = l := by
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hl
  have hline : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hc := S.a3_point_line_kernel_conjugate S.baseLine ha
  rw [hline, ← he, S.point_core_line_kernel] at hc
  have han : a ∈ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mpr hc
  let N := (normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G)).subgroupOf (S.family 0)
  have hPN : localParabolic S.family 0 1 ≤ N := by
    intro b hb
    exact S.a3_pair_normalizes_point_line_kernel ⟨b.property, hb⟩
  rcases S.point_parabolics.left_maximal.le_iff.mp hPN with htop | hpar
  · have hn : S.family 0 ≤ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) := by
      intro b hb
      exact (show (⟨b, hb⟩ : S.family 0) ∈ N from htop ▸ mem_top _)
    exact (S.a3_point_line_kernel_not_normalized hn).elim
  · have haP : (⟨a, ha⟩ : S.family 0) ∈ localParabolic S.family 0 1 := hpar ▸ han
    have hfix : a • S.baseLine = S.baseLine := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [S.stabilizer_baseLine]
      exact haP
    exact hfix.symm.trans hline

/-- The exact missing premise of the original unique-line reduction. -/
theorem a3_point_line_kernel_separation (l m : S.Line)
    (hl : S.Inc S.basePoint l) (hm : S.Inc S.basePoint m)
    (he : S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l} =
      S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y m}) : l = m := by
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hl
  have hline : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have ha' := (S.family 0).inv_mem ha
  have hp : a⁻¹ • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hm' : S.Inc S.basePoint (a⁻¹ • m) := by
    simpa only [hp] using hm.smul S a⁻¹
  have he' := congrArg (Subgroup.map (MulAut.conj a⁻¹).toMonoidHom) he
  rw [S.a3_point_line_kernel_conjugate l ha', S.a3_point_line_kernel_conjugate m ha',
    ← hline, inv_smul_smul] at he'
  have hh := S.a3_base_line_eq_of_point_kernel_eq hm' he'
  have h := congrArg (a • ·) hh
  simpa only [hline, smul_inv_smul] using h

/-- I.5.8(1), for the original A₃ coset geometry and no further premise. -/
theorem a3_unique_line {x y : S.Point} (hxy : x ≠ y) {l m : S.Line}
    (hxl : S.Inc x l) (hyl : S.Inc y l) (hxm : S.Inc x m) (hym : S.Inc y m) : l = m :=
  S.unique_line_of_kernel_separation S.a3_point_line_kernel_separation hxy hxl hyl hxm hym

/-- I.5.8(2), for the original point action. -/
theorem a3_faithful_points : FaithfulSMul G S.Point :=
  S.a3_faithful_points_of_kernel_separation S.a3_point_line_kernel_separation

end Quasithin.I5.DSystem
