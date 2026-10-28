module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import Theory.Mathieu.M12.Properties.Order
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M23Table
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Separation of the five Mathieu residual families

The exact centralizer extensions in 16.1.5 determine their orders. Their
indices then determine the Sylow-center marking of the projected inner actor:
the central rows of M₁₂, M₂₂ and M₂₄ have orders 192, 384 and 21504.
The other M₁₂ rows have a factor five, the outer M₂₂ rows a factor seven
or five, and the other M₂₄ row has no factor seven. These primes survive
the covering kernel and either branch of the modified residual.

Every involutory M₁₁ or M₂₃ action is two-central, by innerness together
with the odd indices 165 and 3795. Their proved model tables are used here.
The exact universal M₁₂, M₂₂ and M₂₄ tables remain explicit inputs; no
marking, prime separation or residual nonisomorphism is assumed.

All equivalences concern the full modified residuals, and all central
covers are retained, including the possible order-four center over M₂₂.
No covering-order bound or ambient order-two assumption is needed beyond
the specified order-two action. Source: Aschbacher–Smith, combined manuscript
of 1 March 2004, 16.1.2 and 16.1.5(3)–(7), printed pp.1170–1172, and
Notation 16.5.5 and the row comparison in 16.5.6(4), printed p.1197.
-/

public section

open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.Mathieu

private theorem twoCentral_of_odd_index {S : Type*} [Group S] [Finite S]
    (x : S) (hx : orderOf x = 2) (hi : Odd (centralizer ({x} : Set S)).index) :
    TwoCentral x := by
  have ht : IsTwoCentralIn (⊤ : Subgroup S) x :=
    twoCentral_iff_odd_index.mpr ⟨hx, mem_top x, by
      change Odd ((centralizer ({x} : Set S)).relIndex ⊤)
      rwa [relIndex_top_right]⟩
  exact ((twoCentralIn_coe_iff (⟨x, mem_top x⟩ : (⊤ : Subgroup S))).mp ht).2.map topEquiv

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} [IsQuasisimple L]
variable {S : Type*} [Group S] [Finite S]

omit [Finite G] [Finite S] in
private theorem model_action_order (e : L ⧸ center L ≃* S)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2) :
    orderOf (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)) = 2 :=
  (orderOf_injective (MulAut.centralQuotientAction e)
    (MulAut.centralQuotientAction_injective e) _).trans ((action_order u).trans hu)

private theorem action_twoCentral_iff_fixed_index (e : L ⧸ center L ≃* S)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      (∃ g, MulAut.centralQuotientAction e (L.normalizerMonoidHom u) = MulAut.conj g) ∧
      Odd (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup.index := by
  constructor
  · intro hc
    obtain ⟨_, k, hk, hkc⟩ := (action_twoCentral_iff u).mp hc
    refine ⟨(MulAut.centralQuotientAction_inner_iff e _).mpr ⟨k, hk⟩, ?_⟩
    rw [hk, MulAut.centralQuotientAction_conj, MulAut.fixedSubgroup_conj]
    exact Nat.not_even_iff_odd.mp (fun he =>
      (hkc.map e).not_dvd_centralizer_index (even_iff_two_dvd.mp he))
  · rintro ⟨hi, hc⟩
    obtain ⟨k, hk⟩ := (MulAut.centralQuotientAction_inner_iff e _).mp hi
    have hq : orderOf (QuotientGroup.mk' (center L) k) = 2 := by
      rw [← orderOf_injective quotientConj quotientConj_injective,
        quotientConj_mk, ← hk, action_order, hu]
    rw [hk, MulAut.centralQuotientAction_conj, MulAut.fixedSubgroup_conj] at hc
    have htc := twoCentral_of_odd_index _ ((e.orderOf_eq _).trans hq) hc
    apply (action_twoCentral_iff u).mpr
    refine ⟨hu, k, hk, ?_⟩
    simpa only [MulEquiv.symm_apply_apply] using htc.map e.symm

private theorem extension_card {N C Q : Type*} [Group N] [Group C] [Group Q]
    [Finite C] (s : GroupExtension N C Q) : Nat.card C = Nat.card N * Nat.card Q := by
  have hn : Nat.card N = Nat.card s.rightHom.ker := by
    rw [← s.range_inl_eq_ker_rightHom]
    exact Nat.card_congr (MonoidHom.ofInjective s.inl_injective).toEquiv
  have hq : Nat.card (C ⧸ s.rightHom.ker) = Nat.card Q :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ s.rightHom_surjective).toEquiv
  rw [hn, ← hq]
  exact s.rightHom.ker.card_mul_index.symm

private theorem elementary_card (n : ℕ) : Nat.card (Elementary n) = 2 ^ n := by
  simp [Elementary, C2, Nat.card_eq_fintype_card]

private theorem quaternion_extension_card {C : Type*} [Group C] [Finite C]
    (h : IsM12QuaternionExtension C) : Nat.card C = 192 := by
  obtain ⟨Q, hQn, ⟨d⟩, ⟨e⟩⟩ := h
  let := hQn
  have hc := Q.card_mul_index
  rw [d.card, index_eq_card, Nat.card_congr e.toEquiv] at hc
  norm_num [S3, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc
  omega

private theorem dihedral_square_card {C : Type*} [Group C] [Finite C]
    (h : IsDihedralSquareProduct C) : Nat.card C = 32 := by
  obtain ⟨B, D, ⟨eB⟩, ⟨eD⟩, hi, hcomm, hspan⟩ := h
  have hn : D ≤ normalizer (B : Set C) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun d hd b hb => hcomm b hb d hd
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn
  rw [Nat.card_congr eB.toEquiv, Nat.card_congr eD.toEquiv, hi, hspan,
    Nat.card_congr (topEquiv : (⊤ : Subgroup C) ≃* C).toEquiv] at hc
  norm_num [Nat.card_eq_fintype_card, DihedralGroup.card] at hc
  omega

private theorem dihedral_cube_card {C : Type*} [Group C] [Finite C]
    (h : IsDihedralCubeProduct C) : Nat.card C = 128 := by
  obtain ⟨B, D, hB, ⟨eD⟩, hi, hcomm, hspan⟩ := h
  have hn : D ≤ normalizer (B : Set C) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun d hd b hb => hcomm b hb d hd
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn
  rw [dihedral_square_card hB, Nat.card_congr eD.toEquiv, hi, hspan,
    Nat.card_congr (topEquiv : (⊤ : Subgroup C) ≃* C).toEquiv] at hc
  norm_num [Nat.card_eq_fintype_card, DihedralGroup.card] at hc
  omega

private theorem dihedral_extension_card {C : Type*} [Group C] [Finite C]
    (h : IsM24DihedralExtension C) : Nat.card C = 21504 := by
  obtain ⟨Q, hQn, hQ, ⟨e⟩⟩ := h
  let := hQn
  have hc := Q.card_mul_index
  rw [dihedral_cube_card hQ, index_eq_card, Nat.card_congr e.toEquiv,
    Matrix.PSL3Two.card_PSL] at hc
  omega

private theorem m12_cards (r : MulAut M12) (h : M12InvolutionAlternative r) :
    ((∃ g, r = MulAut.conj g) ∧ Nat.card r.fixedSubgroup = 192) ∨
      Nat.card r.fixedSubgroup = 240 ∨ Nat.card r.fixedSubgroup = 120 := by
  rcases h with ⟨hi, hq | hp⟩ | ⟨_, hp⟩
  · exact Or.inl ⟨hi, quaternion_extension_card hq⟩
  · right; left
    obtain ⟨e⟩ := hp
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [C2, S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · right; right
    obtain ⟨e⟩ := hp
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    change Nat.card C2 * Nat.card (alternatingGroup (Fin 5)) = 120
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [C2, Nat.card_eq_fintype_card, Nat.factorial]

private theorem m22_cards (r : MulAut M22) (h : M22InvolutionAlternative r) :
    ((∃ g, r = MulAut.conj g) ∧ Nat.card r.fixedSubgroup = 384) ∨
      ((¬ ∃ g, r = MulAut.conj g) ∧
        (Nat.card r.fixedSubgroup = 1344 ∨ Nat.card r.fixedSubgroup = 320)) := by
  rcases h with ⟨hi, he⟩ | ⟨hi, he | he⟩
  · left; refine ⟨hi, ?_⟩
    obtain ⟨e⟩ := he
    rw [extension_card e, elementary_card]
    norm_num [S4, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · right; refine ⟨hi, Or.inl ?_⟩
    obtain ⟨e⟩ := he
    rw [extension_card e, elementary_card, Matrix.PSL3Two.card_PSL]
    norm_num
  · right; refine ⟨hi, Or.inr ?_⟩
    obtain ⟨e⟩ := he
    rw [extension_card e, elementary_card, BenderSuzuki.MatrixGroups.suzukiZero_card]
    norm_num

private theorem m23_card (r : MulAut M23) (h : M23InvolutionAlternative r) :
    Nat.card r.fixedSubgroup = 2688 := by
  obtain ⟨e⟩ := h.2
  rw [extension_card e, elementary_card, Matrix.PSL3Two.card_PSL]
  norm_num

private theorem m24_cards (r : MulAut M24) (h : M24InvolutionAlternative r) :
    (∃ g, r = MulAut.conj g) ∧
      (Nat.card r.fixedSubgroup = 21504 ∨ Nat.card r.fixedSubgroup = 7680) := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with h | he
  · exact Or.inl (dihedral_extension_card h)
  · right
    obtain ⟨e⟩ := he
    rw [extension_card e, elementary_card]
    norm_num [S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem index_of_card {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) {m n k : ℕ} (hC : Nat.card C = m) (hH : Nat.card H = n)
    (h : m * k = n) : C.index = k := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C))
  rw [C.card_mul_index, hC, hH, h]

private theorem m12_marking (e : L ⧸ center L ≃* M12)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2)
    (ht : M12InvolutionAlternative (MulAut.centralQuotientAction e (L.normalizerMonoidHom u))) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup = 192 := by
  let r := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  rcases m12_cards r ht with ⟨hi, hc⟩ | hc | hc
  · have hj := index_of_card r.fixedSubgroup hc m12_order (show 192 * 495 = 95040 from rfl)
    rw [action_twoCentral_iff_fixed_index e u hu]
    change ((∃ g, r = MulAut.conj g) ∧ Odd r.fixedSubgroup.index) ↔ _
    rw [hj, hc]
    exact iff_of_true ⟨hi, by decide⟩ rfl
  · have hj := index_of_card r.fixedSubgroup hc m12_order (show 240 * 396 = 95040 from rfl)
    rw [action_twoCentral_iff_fixed_index e u hu]
    change ((∃ g, r = MulAut.conj g) ∧ Odd r.fixedSubgroup.index) ↔ _
    rw [hj, hc]
    norm_num
  · have hj := index_of_card r.fixedSubgroup hc m12_order (show 120 * 792 = 95040 from rfl)
    rw [action_twoCentral_iff_fixed_index e u hu]
    change ((∃ g, r = MulAut.conj g) ∧ Odd r.fixedSubgroup.index) ↔ _
    rw [hj, hc]
    norm_num

private theorem m22_marking (e : L ⧸ center L ≃* M22)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2)
    (ht : M22InvolutionAlternative (MulAut.centralQuotientAction e (L.normalizerMonoidHom u))) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      ∃ g, MulAut.centralQuotientAction e (L.normalizerMonoidHom u) = MulAut.conj g := by
  let r := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  rcases m22_cards r ht with ⟨hi, hc⟩ | ⟨hi, _⟩
  · have hj := index_of_card r.fixedSubgroup hc m22_order (show 384 * 1155 = 443520 from rfl)
    rw [action_twoCentral_iff_fixed_index e u hu]
    change ((∃ g, r = MulAut.conj g) ∧ Odd r.fixedSubgroup.index) ↔ _
    rw [hj]
    exact and_iff_left (by decide)
  · rw [action_twoCentral_iff_fixed_index e u hu]
    exact iff_of_false (fun h => hi h.1) hi

private theorem m24_marking (e : L ⧸ center L ≃* M24)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2)
    (ht : M24InvolutionAlternative (MulAut.centralQuotientAction e (L.normalizerMonoidHom u))) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup = 21504 := by
  let r := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  obtain ⟨hi, hc | hc⟩ := m24_cards r ht
  · have hj := index_of_card r.fixedSubgroup hc m24_order (show 21504 * 11385 = 244823040 from rfl)
    rw [action_twoCentral_iff_fixed_index e u hu]
    change ((∃ g, r = MulAut.conj g) ∧ Odd r.fixedSubgroup.index) ↔ _
    rw [hj, hc]
    exact iff_of_true ⟨hi, by decide⟩ rfl
  · have hj := index_of_card r.fixedSubgroup hc m24_order (show 7680 * 31878 = 244823040 from rfl)
    rw [action_twoCentral_iff_fixed_index e u hu]
    change ((∃ g, r = MulAut.conj g) ∧ Odd r.fixedSubgroup.index) ↔ _
    rw [hj, hc]
    norm_num

/-- Every involutory action on an M₁₁ central quotient is two-central in L*.
The order-48 fixed group has odd index 165; innerness alone is not the argument. -/
theorem m11_action_twoCentral (e : L ⧸ center L ≃* M11)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) := by
  let r := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  have hr : orderOf r = 2 := model_action_order e u hu
  have hc : Nat.card r.fixedSubgroup = 48 := by
    rw [Nat.card_congr (m11InvolutoryAutFixedEquiv r hr).toEquiv, Matrix.card_GL_field]
    decide
  have hj := index_of_card r.fixedSubgroup hc m11_order (show 48 * 165 = 7920 from rfl)
  apply (action_twoCentral_iff_fixed_index e u hu).mpr
  obtain ⟨g, hg⟩ := m11_automorphism_inner r
  exact ⟨⟨g, hg.symm⟩, hj ▸ (by decide)⟩

/-- The noncentral M₁₁ row is impossible, hence cannot share a modified residual. -/
theorem m11_no_equiv (e : L ⧸ center L ≃* M11)
    (u v : normalizer (L : Set G)) (hv : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hnv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) :=
  (hnv (m11_action_twoCentral e v hv)).elim

/-- M₁₂'s central quaternion row has no factor five; both other rows have one.
The input is the exact universal source table, with actual extensions and isomorphisms. -/
theorem m12_no_equiv (hodd : pPrimeCore 2 L = ⊥) (e : L ⧸ center L ≃* M12)
    (table : ∀ r : MulAut M12, orderOf r = 2 → M12InvolutionAlternative r)
    (u v : normalizer (L : Set G))
    (hu : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hv : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hcu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hnv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  have htu := table _ (model_action_order e u hu)
  have htv := table _ (model_action_order e v hv)
  have huc := (m12_marking e u hu htu).mp hcu
  have hvc := mt (m12_marking e v hv htv).mpr hnv
  have hfive : 5 ∣ Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup := by
    rcases m12_cards _ htv with ⟨_, hc⟩ | hc | hc
    · exact (hvc hc).elim
    · rw [hc]; decide
    · rw [hc]; decide
  have hnot : ¬ 5 ∣ Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup := by
    rw [huc]; decide
  rintro ⟨f⟩
  exact no_equiv_of_fixed_prime hodd e v u (by decide : Nat.Prime 5) (by decide) (by decide)
    hfive hnot ⟨f.symm⟩

/-- Every inner M₂₂ row is two-central. The two outer rows have, respectively,
a factor seven or five absent from the inner row; centers of order four are retained. -/
theorem m22_no_equiv (hodd : pPrimeCore 2 L = ⊥) (e : L ⧸ center L ≃* M22)
    (table : ∀ r : MulAut M22, orderOf r = 2 → M22InvolutionAlternative r)
    (u v : normalizer (L : Set G))
    (hu : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hv : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hcu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hnv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  have htu := table _ (model_action_order e u hu)
  have htv := table _ (model_action_order e v hv)
  have hui := (m22_marking e u hu htu).mp hcu
  have hvi := mt (m22_marking e v hv htv).mpr hnv
  have huc : Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup = 384 := by
    rcases m22_cards _ htu with ⟨_, hc⟩ | ⟨hi, _⟩
    · exact hc
    · exact (hi hui).elim
  have hvc : Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup = 1344 ∨
      Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup = 320 := by
    rcases m22_cards _ htv with ⟨hi, _⟩ | ⟨_, hc⟩
    · exact (hvi hi).elim
    · exact hc
  rintro ⟨f⟩
  rcases hvc with hc | hc
  · exact no_equiv_of_fixed_prime hodd e v u (by decide : Nat.Prime 7) (by decide) (by decide)
      (by rw [hc]; decide) (by rw [huc]; decide) ⟨f.symm⟩
  · exact no_equiv_of_fixed_prime hodd e v u (by decide : Nat.Prime 5) (by decide) (by decide)
      (by rw [hc]; decide) (by rw [huc]; decide) ⟨f.symm⟩

/-- Every involutory M₂₃ action is two-central: its exact E₁₆ extension has
order 2688 and odd index 3795. The model table is proved upstream. -/
theorem m23_action_twoCentral (e : L ⧸ center L ≃* M23)
    (u : normalizer (L : Set G)) (hu : orderOf (actionMap (L := L) le_rfl u) = 2) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) := by
  let r := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  have ht := m23_involution_alternative r (model_action_order e u hu)
  have hc := m23_card r ht
  have hj := index_of_card r.fixedSubgroup hc m23_order (show 2688 * 3795 = 10200960 from rfl)
  apply (action_twoCentral_iff_fixed_index e u hu).mpr
  exact ⟨ht.1, hj ▸ (by decide)⟩

/-- The noncentral M₂₃ row is impossible, hence cannot share a modified residual. -/
theorem m23_no_equiv (e : L ⧸ center L ≃* M23)
    (u v : normalizer (L : Set G)) (hv : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hnv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) :=
  (hnv (m23_action_twoCentral e v hv)).elim

/-- M₂₄'s two-central dihedral row has a factor seven; its noncentral E₆₄
row does not. Both are inner, and their markings come from their actual indices. -/
theorem m24_no_equiv (hodd : pPrimeCore 2 L = ⊥) (e : L ⧸ center L ≃* M24)
    (table : ∀ r : MulAut M24, orderOf r = 2 → M24InvolutionAlternative r)
    (u v : normalizer (L : Set G))
    (hu : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hv : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hcu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hnv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  have htu := table _ (model_action_order e u hu)
  have htv := table _ (model_action_order e v hv)
  have huc := (m24_marking e u hu htu).mp hcu
  have hvc := mt (m24_marking e v hv htv).mpr hnv
  have hother : Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup = 7680 :=
    (m24_cards _ htv).2.resolve_left hvc
  exact no_equiv_of_fixed_prime hodd e u v (by decide : Nat.Prime 7) (by decide) (by decide)
    (by rw [huc]; decide) (by rw [hother]; decide)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.Mathieu
