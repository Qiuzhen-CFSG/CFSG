module

public import Theory.GroupTheory.CentralCommutatorEightCenter
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Correcting lifts over an elementary abelian subgroup

When the derived subgroup lies in an elementary abelian subgroup D and in a
center of order two, every square is central. If D is self-centralizing,
each element outside D admits an involutory D-correction. Independent
representatives admit corrections that are both involutory and commute:
their commutator characters on D can be separated, so commutation can be
corrected without changing the square of the second lift.

For a normal D of order eight in a group of order thirty-two, the corrected
lifts generate the group together with D. This supplies the lift-correction
step of the central-commutator elementary-eight supplement construction.
-/

open scoped commutatorElement IsMulCommutative

namespace Subgroup

private theorem center_two_nonidentity_eq
    {G : Type*} [Group G] (hcenter : Nat.card (center G) = 2)
    {left right : G} (hleft : left ∈ center G) (hright : right ∈ center G)
    (hleftne : left ≠ 1) (hrightne : right ≠ 1) : left = right := by
  obtain ⟨unique, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : center G)).mp hcenter
  have hfirst := huniq ⟨left, hleft⟩ (fun heq => hleftne (congrArg Subtype.val heq))
  have hsecond := huniq ⟨right, hright⟩ (fun heq => hrightne (congrArg Subtype.val heq))
  exact congrArg Subtype.val (hfirst.trans hsecond.symm)

private theorem central_commutator_mul_left
    {G : Type*} [Group G] (D : Subgroup G)
    (hderived : _root_.commutator G ≤ D ⊓ center G) (left right other : G) :
    ⁅left * right, other⁆ = ⁅right, other⁆ * ⁅left, other⁆ := by
  have hcentral := (hderived (commutator_mem_commutator
    (mem_top right) (mem_top other))).2
  rw [commutatorElement_mul_left_eq_conj_mul, mem_center_iff.mp hcentral left]
  simp only [mul_inv_cancel_right]

private theorem central_commutator_mul_right
    {G : Type*} [Group G] (D : Subgroup G)
    (hderived : _root_.commutator G ≤ D ⊓ center G) (other left right : G) :
    ⁅other, left * right⁆ = ⁅other, left⁆ * ⁅other, right⁆ := by
  have hcentral := (hderived (commutator_mem_commutator
    (mem_top other) (mem_top right))).2
  rw [commutatorElement_mul_right_eq_mul_conj,
    mul_assoc ⁅other, left⁆ left ⁅other, right⁆,
    mem_center_iff.mp hcentral left]
  simp only [← mul_assoc, mul_inv_cancel_right]

private theorem square_mul_of_central_commutator
    {G : Type*} [Group G] (D : Subgroup G)
    (hderived : _root_.commutator G ≤ D ⊓ center G) (left right : G) :
    (left * right) ^ 2 = ⁅right, left⁆ * left ^ 2 * right ^ 2 := by
  have hcentral := (hderived (commutator_mem_commutator
    (mem_top right) (mem_top left))).2
  have hswap : right * left = ⁅right, left⁆ * (left * right) := by
    simp [commutatorElement_def, mul_assoc]
  calc
    (left * right) ^ 2 = left * (right * left) * right := by
      simp only [pow_two, mul_assoc]
    _ = left * (⁅right, left⁆ * (left * right)) * right := by rw [hswap]
    _ = ⁅right, left⁆ * left ^ 2 * right ^ 2 := by
      rw [← mul_assoc left, mem_center_iff.mp hcentral left]
      simp only [pow_two, mul_assoc]

public theorem exists_involutory_correction_of_central_commutator
    {G : Type*} [Group G] (D : Subgroup G)
    (hD : IsElementaryAbelian 2 D)
    (hderived : _root_.commutator G ≤ D ⊓ center G)
    (hcentralizer : centralizer (D : Set G) = D)
    (hcenter : Nat.card (center G) = 2)
    (element : G) (hout : element ∉ D) :
    ∃ correction ∈ D, (element * correction) ^ 2 = 1 := by
  classical
  let := hD
  by_cases hsquare : element ^ 2 = 1
  · exact ⟨1, D.one_mem, by simpa using hsquare⟩
  have hexists : ∃ correction ∈ D, ⁅correction, element⁆ ≠ 1 := by
    by_contra! hnone
    apply hout
    rw [← hcentralizer]
    intro correction hcorrection
    exact commutatorElement_eq_one_iff_mul_comm.mp (hnone correction hcorrection)
  obtain ⟨correction, hcorrection, hnontrivial⟩ := hexists
  have heq : ⁅correction, element⁆ = element ^ 2 :=
    center_two_nonidentity_eq hcenter
      (hderived (commutator_mem_commutator (mem_top correction) (mem_top element))).2
      (square_mem_center_of_elementary_central_commutator D hD hderived element)
      hnontrivial hsquare
  refine ⟨correction, hcorrection, ?_⟩
  rw [square_mul_of_central_commutator D hderived, heq,
    elemPow_eq_one_of_isElementaryAbelian (p := 2) correction hcorrection, mul_one,
    ← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (element ^ 2)
    (heq ▸ (hderived (commutator_mem_commutator
      (mem_top correction) (mem_top element))).1)

private theorem exists_separating_commutator
    {G : Type*} [Group G] (D : Subgroup G)
    (hD : IsElementaryAbelian 2 D)
    (hderived : _root_.commutator G ≤ D ⊓ center G)
    (hcentralizer : centralizer (D : Set G) = D)
    (hcenter : Nat.card (center G) = 2)
    (first second : G) (hfirst : first ∉ D)
    (hsecond : second ∉ D ⊔ zpowers first) :
    ∃ correction ∈ D, ⁅correction, second⁆ = 1 ∧ ⁅correction, first⁆ ≠ 1 := by
  classical
  let := hD
  have hpow (left right : G) : ⁅left, right⁆ * ⁅left, right⁆ = 1 := by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _
      (hderived (commutator_mem_commutator (mem_top left) (mem_top right))).1
  by_contra! hnone
  have hpivot : ∃ pivot ∈ D, ⁅pivot, first⁆ ≠ 1 := by
    by_contra! htrivial
    apply hfirst
    rw [← hcentralizer]
    intro member hmember
    exact commutatorElement_eq_one_iff_mul_comm.mp (htrivial member hmember)
  obtain ⟨pivot, hpivot, hpivotfirst⟩ := hpivot
  have hpivotsecond : ⁅pivot, second⁆ ≠ 1 := fun heq =>
    hpivotfirst (hnone pivot hpivot heq)
  have hpivoteq : ⁅pivot, first⁆ = ⁅pivot, second⁆ :=
    center_two_nonidentity_eq hcenter
      (hderived (commutator_mem_commutator (mem_top pivot) (mem_top first))).2
      (hderived (commutator_mem_commutator (mem_top pivot) (mem_top second))).2
      hpivotfirst hpivotsecond
  have hequal (member : G) (hmember : member ∈ D) :
      ⁅member, first⁆ = ⁅member, second⁆ := by
    by_cases hsecondone : ⁅member, second⁆ = 1
    · exact (hnone member hmember hsecondone).trans hsecondone.symm
    have hsecondpivot : ⁅member, second⁆ = ⁅pivot, second⁆ :=
      center_two_nonidentity_eq hcenter
        (hderived (commutator_mem_commutator (mem_top member) (mem_top second))).2
        (hderived (commutator_mem_commutator (mem_top pivot) (mem_top second))).2
        hsecondone hpivotsecond
    have hproduct : ⁅member * pivot, second⁆ = 1 := by
      rw [central_commutator_mul_left D hderived, hsecondpivot, hpow]
    have hproductfirst := hnone (member * pivot) (D.mul_mem hmember hpivot) hproduct
    rw [central_commutator_mul_left D hderived] at hproductfirst
    have hfirstpivot : ⁅member, first⁆ = ⁅pivot, first⁆ :=
      mul_left_cancel (hproductfirst.trans (hpow pivot first).symm)
    exact hfirstpivot.trans (hpivoteq.trans hsecondpivot.symm)
  have hproductD : second * first ∈ D := by
    rw [← hcentralizer]
    intro member hmember
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [central_commutator_mul_right D hderived, hequal member hmember, hpow]
  apply hsecond
  have hmem : second * first * first⁻¹ ∈ D ⊔ zpowers first :=
    mul_mem (mem_sup_left hproductD)
      (inv_mem (mem_sup_right (mem_zpowers first)))
  simpa only [mul_inv_cancel_right] using hmem

public theorem exists_commuting_involutory_correction_of_central_commutator
    {G : Type*} [Group G] (D : Subgroup G)
    (hD : IsElementaryAbelian 2 D)
    (hderived : _root_.commutator G ≤ D ⊓ center G)
    (hcentralizer : centralizer (D : Set G) = D)
    (hcenter : Nat.card (center G) = 2)
    (first second : G) (hfirst : first ∉ D)
    (hsecond : second ∉ D ⊔ zpowers first) :
    ∃ correction ∈ D, (second * correction) ^ 2 = 1 ∧
      Commute first (second * correction) := by
  classical
  let := hD
  obtain ⟨initial, hinitial, hsquare⟩ :=
    exists_involutory_correction_of_central_commutator D hD hderived
      hcentralizer hcenter second (fun hmem => hsecond (mem_sup_left hmem))
  let lifted := second * initial
  have hlifted : lifted ∉ D ⊔ zpowers first := by
    intro hmem
    apply hsecond
    have hmul := (D ⊔ zpowers first).mul_mem hmem
      ((D ⊔ zpowers first).inv_mem (mem_sup_left hinitial))
    simpa only [lifted, mul_inv_cancel_right] using hmul
  by_cases hcommute : Commute first lifted
  · exact ⟨initial, hinitial, hsquare, hcommute⟩
  obtain ⟨extra, hextra, hextralifted, hextrafirst⟩ :=
    exists_separating_commutator D hD hderived hcentralizer hcenter
      first lifted hfirst hlifted
  have hfirstextra : ⁅first, extra⁆ ≠ 1 := by
    intro heq
    exact hextrafirst (commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp heq).symm)
  have hfirstlifted : ⁅first, lifted⁆ ≠ 1 := fun heq =>
    hcommute (commutatorElement_eq_one_iff_commute.mp heq)
  have heq : ⁅first, extra⁆ = ⁅first, lifted⁆ :=
    center_two_nonidentity_eq hcenter
      (hderived (commutator_mem_commutator (mem_top first) (mem_top extra))).2
      (hderived (commutator_mem_commutator (mem_top first) (mem_top lifted))).2
      hfirstextra hfirstlifted
  refine ⟨initial * extra, D.mul_mem hinitial hextra, ?_, ?_⟩
  · rw [← mul_assoc]
    change (lifted * extra) ^ 2 = 1
    rw [(commutatorElement_eq_one_iff_commute.mp hextralifted).symm.mul_pow,
      hsquare, elemPow_eq_one_of_isElementaryAbelian (p := 2) extra hextra, one_mul]
  · rw [← mul_assoc]
    change Commute first (lifted * extra)
    apply commutatorElement_eq_one_iff_commute.mp
    rw [central_commutator_mul_right D hderived, heq, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _
      (hderived (commutator_mem_commutator (mem_top first) (mem_top lifted))).1

public theorem exists_corrected_lifts_of_central_commutator
    {G : Type*} [Group G] [Finite G] (D : Subgroup G) [D.Normal]
    (hD : IsElementaryAbelian 2 D) (hDcard : Nat.card D = 8)
    (hGcard : Nat.card G = 32)
    (hderived : _root_.commutator G ≤ D ⊓ center G)
    (hcentralizer : centralizer (D : Set G) = D)
    (hcenter : Nat.card (center G) = 2)
    (first second : G) (hfirst : first ∉ D)
    (hsecond : second ∉ D ⊔ zpowers first) :
    ∃ firstCorrection ∈ D, ∃ secondCorrection ∈ D,
      (first * firstCorrection) ^ 2 = 1 ∧
      (second * secondCorrection) ^ 2 = 1 ∧
      Commute (first * firstCorrection) (second * secondCorrection) ∧
      D ⊔ zpowers (first * firstCorrection) ⊔
        zpowers (second * secondCorrection) = ⊤ := by
  obtain ⟨firstCorrection, hfirstCorrection, hfirstSquare⟩ :=
    exists_involutory_correction_of_central_commutator D hD hderived
      hcentralizer hcenter first hfirst
  have hfirstOut : first * firstCorrection ∉ D := by
    intro hmem
    apply hfirst
    simpa only [mul_inv_cancel_right] using
      D.mul_mem hmem (D.inv_mem hfirstCorrection)
  have hjoin : D ⊔ zpowers (first * firstCorrection) = D ⊔ zpowers first := by
    apply le_antisymm
    · exact sup_le le_sup_left (zpowers_le.mpr
        (mul_mem (mem_sup_right (mem_zpowers first)) (mem_sup_left hfirstCorrection)))
    · refine sup_le le_sup_left (zpowers_le.mpr ?_)
      have hmem := (D ⊔ zpowers (first * firstCorrection)).mul_mem
        (mem_sup_right (mem_zpowers (first * firstCorrection)))
        ((D ⊔ zpowers (first * firstCorrection)).inv_mem (mem_sup_left hfirstCorrection))
      simpa only [mul_inv_cancel_right] using hmem
  have hsecondOut : second ∉ D ⊔ zpowers (first * firstCorrection) := by
    rwa [hjoin]
  obtain ⟨secondCorrection, hsecondCorrection, hsecondSquare, hcommute⟩ :=
    exists_commuting_involutory_correction_of_central_commutator D hD hderived
      hcentralizer hcenter (first * firstCorrection) second hfirstOut hsecondOut
  refine ⟨firstCorrection, hfirstCorrection, secondCorrection, hsecondCorrection,
    hfirstSquare, hsecondSquare, hcommute, ?_⟩
  let intermediate : Subgroup G := D ⊔ zpowers (first * firstCorrection)
  have hintermediate : Nat.card intermediate = 16 := by
    rw [card_sup_zpowers_of_normalizing_involution D _ hfirstSquare hfirstOut
      (by rw [normalizer_eq_top]; trivial), hDcard]
  have hindex : intermediate.index = 2 := by
    have hmul := intermediate.index_mul_card
    rw [hintermediate, hGcard] at hmul
    omega
  let : intermediate.Normal := normal_of_index_eq_two hindex
  have hsecondCorrectedOut : second * secondCorrection ∉ intermediate := by
    intro hmem
    apply hsecondOut
    have hmul := intermediate.mul_mem hmem (intermediate.inv_mem
      (mem_sup_left hsecondCorrection))
    simpa only [mul_inv_cancel_right] using hmul
  apply eq_top_of_card_eq
  rw [card_sup_zpowers_of_normalizing_involution intermediate _ hsecondSquare
    hsecondCorrectedOut (by rw [normalizer_eq_top]; trivial), hintermediate, hGcard]

end Subgroup

