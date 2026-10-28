module
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition
public import CFSG.Quasithin.ChapterG.Section02.Binary.SourceAssembly
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupAction.CoprimeEightFixedLine
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# The fixed central line in the opposite binary intersection

If the closure U has center of order four inside its actual opposite
intersection, center(U) together with the natural four-plane is an
abelian eight. The common core centralizes this eight. The cubic actor
has a fixed complementary line, which lies in center(U) and is preserved
by both original parabolics. Perfectness of the normal component makes
that line a common normal two-subgroup, contradicting the trivial core
of the generated amalgam.

Source: Aschbacher–Smith 14.2.16, F.1.12 and G.2.3,
printed pp.985–986, 262–264 and 333–334.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

 theorem binary_plane_fixed_free (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    D.V ⊓ centralizer (D.L : Set G) = ⊥ := by
  have hn : D.L ≤ normalizer (D.V ⊓ centralizer (D.L : Set G) : Set G) :=
    (le_inf b.L_normalizes_V
      (D.L.le_normalizer.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  rcases b.irreducible _ inf_le_left hn with hz | heq
  · exact hz
  · have hVL : D.V ≤ centralizer (D.L : Set G) := heq.ge.trans inf_le_right
    have hLV : D.L ≤ centralizer (D.V : Set G) := le_centralizer_iff.mp hVL
    exact (hgN ((hLV.trans ((centralizer_le h.point_le).trans (Subgroup.centralizer_le_normalizer _))) hgL)).elim

 theorem binary_center_plane_geometry
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hne : ¬ IsMulCommutative D.U)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hC4 : Nat.card (center D.U) = 4)
    (hCE : (center D.U).map D.U.subtype ≤ D.S₂ g) :
    let C := (center D.U).map D.U.subtype
    let A := C ⊔ D.V
    Nat.card A = 8 ∧ IsElementaryAbelian 2 A ∧
      D.I g ≤ normalizer (A : Set G) ∧ D.T ≤ normalizer (A : Set G) ∧
      D.S g ≤ centralizer (A : Set G) ∧ ⁅A,D.L⁆ ≤ D.V := by
  let C := (center D.U).map D.U.subtype
  let A := C ⊔ D.V
  have hCU : C ≤ D.U := map_subtype_le _
  have hCC : C ≤ centralizer (D.U : Set G) := by
    exact (map_center_subtype_eq_inf_centralizer D.U).le.trans inf_le_right
  have hHC : D.H ≤ normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy D.V D.H).trans
      (normalizer_le_normalizer_characteristic_image D.U (center D.U))
  have hTC : D.T ≤ normalizer (C : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer h.U_normal_in_T.1).mp h.U_normal_in_T.2).trans
      (normalizer_le_normalizer_characteristic_image D.U (center D.U))
  have hZC : D.V₁ ≤ C := by
    rw [show C = D.U ⊓ centralizer (D.U : Set G) from
      map_center_subtype_eq_inf_centralizer D.U]
    exact le_inf (h.point_le.trans (le_conjugateSpanBy _ _))
      (le_centralizer_iff.mp h.U_le_centralizer_point)
  have hnot : ¬ D.V ≤ C := by
    intro hv
    have he : D.U = C := le_antisymm (conjugateSpanBy_le hv hHC) hCU
    apply hne
    rw [he]
    exact map_isMulCommutative (center D.U) D.U.subtype
  have hCv : Nat.card C = 4 := by
    exact (card_map_of_injective D.U.subtype_injective).trans hC4
  have hcap2 : Nat.card (C ⊓ D.V : Subgroup G) = 2 := by
    have hd : Nat.card (C ⊓ D.V : Subgroup G) ∣ Nat.card D.V := card_dvd_of_le inf_le_right
    have hl : 2 ≤ Nat.card (C ⊓ D.V : Subgroup G) := by
      rw [← b.point_card]
      exact Nat.card_le_card_of_injective (inclusion (le_inf hZC h.point_le))
        (inclusion_injective _)
    have hd' : Nat.card (C ⊓ D.V : Subgroup G) ∣ 2^2 := by simpa only [b.card_V,show 2^2 = (4:ℕ) by norm_num] using hd
    obtain ⟨k,hk,hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
    have hkne : k ≠ 2 := by
      intro he
      have heq : C ⊓ D.V = D.V := eq_of_le_of_card_ge inf_le_right (by
        rw [hkc,he,b.card_V]; norm_num)
      exact hnot (heq.ge.trans inf_le_left)
    have hk1 : k = 1 := by
      by_cases hz : k = 0
      · simp only [hkc,hz,pow_zero] at hl
        omega
      · omega
    rw [hkc,hk1]
    norm_num
  have hcA : Nat.card A = 8 := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes C D.V
      (((show D.V ≤ D.U from le_conjugateSpanBy _ _).trans (le_centralizer_iff.mp hCC)).trans (Subgroup.centralizer_le_normalizer _))
    rw [hCv,b.card_V,hcap2] at hc
    change 4 * 4 = 2 * Nat.card A at hc
    omega
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI,⟨eqv⟩,hnorm,hindex,hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨_,_,_,_,hS,_,hVE,_,hVC,_,_,hcomm,hE,_⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI eqv hnorm hindex
  have hAE : A ≤ D.S₂ g := sup_le hCE hVE
  have hAI : A ≤ D.I g := hAE.trans (inf_le_left.trans le_sup_left)
  have hmv : ⁅A,D.I g⁆ ≤ D.V := (commutator_mono hAE le_rfl).trans hcomm
  have hIA : D.I g ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hmv.trans le_sup_right)
  have hTA : D.T ≤ normalizer (A : Set G) :=
    (le_inf hTC h.T_normalizes_V).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hWA : D.W g ≤ centralizer (A : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (le_centralizer_iff.mp hCC)))
      (le_centralizer_iff.mp (inf_le_right.trans (le_centralizer_iff.mp (hVC.trans inf_le_right))))
  have hconj : conjugate (D.W g) g ≤ centralizer (A : Set G) := by
    rintro x ⟨w,hw,rfl⟩
    have hn := (normalizer_le_normalizer_centralizer A) (hIA hgI)
    exact (mem_normalizer_iff.mp ((normalizer (centralizer (A : Set G) : Set G)).inv_mem hn) w).mp
      (hWA hw)
  exact ⟨hcA,(by let := hE; exact IsElementaryAbelian.of_le hAE),hIA,hTA,by simpa only [hS] using sup_le hWA hconj,
    (commutator_mono le_rfl (le_sup_left.trans hI.ge)).trans hmv⟩

 theorem binary_center_card_ne_four_of_opposite
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hne : ¬ IsMulCommutative D.U)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hCE : (center D.U).map D.U.subtype ≤ D.S₂ g)
    (hquot : Nat.card (D.L ⧸ pCore 2 D.L) = 3)
    (K : Subgroup D.H) [Group.IsPerfect K]
    (hgen : K.map D.H.subtype ⊔ D.T = D.H)
    (hzero : pCore 2 (D.H ⊔ (D.L ⊔ D.T) : Subgroup G) = ⊥) :
    Nat.card (center D.U) ≠ 4 := by
  intro hC4
  let C := (center D.U).map D.U.subtype
  let A := C ⊔ D.V
  let E := A ⊓ centralizer (D.L : Set G)
  obtain ⟨hcA,hEA,hIA,hTA,hSA,hmove⟩ :=
    binary_center_plane_geometry h b hne g hgL hgN hC4 hCE
  change Nat.card A = 8 at hcA
  change IsElementaryAbelian 2 A at hEA
  let := hEA
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI,_,_,_,_⟩ := binary_source_inputs h b hUT g hgL hgN
  have hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  have hIL : D.I g ≤ normalizer (D.L : Set G) := by
    rw [hI]
    exact sup_le D.L.le_normalizer (hUT.trans h.T_normalizes_L)
  have hodd := odd_conjugation_image_of_cubic_two_core_quotient A D.L
    (hLI.trans hIA) hquot
    ((pCoreIn_mono_of_normalizes hLI hIL).trans hSA)
  obtain ⟨hE2,hVE,hd,hIE⟩ := fixed_line_of_odd_image_and_fixed_free_plane
    A D.V D.L (D.I g) le_sup_right hcA b.card_V (hLI.trans hIA) hodd hmove
      (binary_plane_fixed_free h b g hgL hgN) hIA hIL
  change Nat.card E = 2 at hE2
  change D.I g ≤ centralizer (E : Set G) at hIE
  have hEU : E ≤ D.U := inf_le_left.trans (sup_le (map_subtype_le _)
    (le_conjugateSpanBy _ _))
  have hEC : E ≤ C := by
    rw [show C = D.U ⊓ centralizer (D.U : Set G) from
      map_center_subtype_eq_inf_centralizer D.U]
    exact le_inf hEU (le_centralizer_iff.mp (le_sup_left.trans hIE))
  have hTE : D.T ≤ normalizer (E : Set G) :=
    (le_inf hTA (h.T_normalizes_L.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hHC : D.H ≤ normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy D.V D.H).trans
      (normalizer_le_normalizer_characteristic_image D.U (center D.U))
  have hCH : C ≤ D.H := (map_subtype_le _).trans h.U_le_H
  let C0 := C.subgroupOf D.H
  let : C0.Normal := (normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
  have hcC0 : Nat.card C0 = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCH).toEquiv).trans
      ((card_map_of_injective D.U.subtype_injective).trans hC4)
  have hKC0 := le_centralizer_of_isPerfect_of_card_le_four K C0 hcC0.le
  have hKC : K.map D.H.subtype ≤ centralizer (C : Set G) := by
    rintro k ⟨k,hk,rfl⟩ c hc
    exact congrArg Subtype.val (hKC0 hk ⟨c,hCH hc⟩ hc)
  have hHE : D.H ≤ normalizer (E : Set G) := by
    rw [← hgen]
    exact sup_le ((hKC.trans (centralizer_le hEC)).trans
      (Subgroup.centralizer_le_normalizer _)) hTE
  have hJE : D.H ⊔ (D.L ⊔ D.T) ≤ normalizer (E : Set G) :=
    sup_le hHE (sup_le ((hLI.trans hIE).trans
      (Subgroup.centralizer_le_normalizer _)) hTE)
  have hEB : E ≤ (D.H ⊔ (D.L ⊔ D.T)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 A |>.to_le inf_le_left)
      (hEU.trans (h.U_le_H.trans le_sup_left)) hJE
  have hbot : E = ⊥ := bot_unique (by simpa only [pCoreIn,hzero,Subgroup.map_bot] using hEB)
  have hcE : Nat.card E = 1 := by rw [hbot]; exact Nat.card_unique
  omega
end CFSG.Quasithin.ChapterG.Section02.Setup
