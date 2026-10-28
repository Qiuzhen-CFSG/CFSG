module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionEnvelope
public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.GroupTheory.ThreeStepChainCentralizerTwoCore

/-!
# Replacement in the support-exchanging partner-core branch

A maximum elementary subgroup acting on the actual intersection W=V∩Q
has action index at most four. The support exchange makes every nontrivial
action have fixed index at least four. Equality in the replacement count
then puts W inside J(Q). The characteristic envelope centralizes W; full
support projections subsequently force it to centralize V.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem maxJ_contains_elementary_of_large_fixed_index
    (S W : Subgroup G) [IsElementaryAbelian 2 W] (hWS : W≤S)
    (hindex : ∀A∈elementaryAbelianMaxSubgroups S,
      ¬A≤centralizer (W : Set G) →
      (centralizer (W : Set G)).relIndex A≤(centralizer (A : Set G)).relIndex W) :
    W≤elementaryAbelianMaxJ S := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  let : IsElementaryAbelian 2 A := hA.2.1
  by_cases hAC : A≤centralizer (W : Set G)
  · exact (maxElementary_contains_elementary_centralizer S A W hA hWS
      (le_centralizer_iff.mp hAC)).trans (le_sSup hA)
  let C := A⊓centralizer (W : Set G)
  let I := W⊓C
  let H := W⊓centralizer (A : Set G)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (W⊔C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (show C≤centralizer (W : Set G) from inf_le_right)
  have hjoinS : W⊔C≤S := sup_le hWS (inf_le_left.trans hA.1)
  have hIH : I≤H := le_inf inf_le_left
    ((inf_le_right.trans inf_le_left).trans A.le_centralizer)
  have hci : Nat.card I≤Nat.card H := card_le_of_le hIH
  have hca : Nat.card C*(centralizer (W : Set G)).relIndex A=Nat.card A := by
    simpa only [C,relIndex_bot_left,inf_relIndex_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) C A bot_le inf_le_left
  have hcw : Nat.card H*(centralizer (A : Set G)).relIndex W=Nat.card W := by
    simpa only [H,relIndex_bot_left,inf_relIndex_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) H W bot_le inf_le_left
  have hlow : Nat.card I*(centralizer (W : Set G)).relIndex A≤Nat.card W := by
    rw [←hcw]
    exact Nat.mul_le_mul hci (hindex A hA hAC)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes W C
    ((show C≤centralizer (W : Set G) from inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _))
  change Nat.card W*Nat.card C=Nat.card I*Nat.card (W⊔C : Subgroup G) at hprod
  have hl : Nat.card A≤Nat.card (W⊔C : Subgroup G) := by
    have hh : Nat.card I*Nat.card A≤Nat.card I*Nat.card (W⊔C : Subgroup G) := by
      rw [←hprod,←hca]
      simpa only [mul_assoc,mul_comm,mul_left_comm] using Nat.mul_le_mul_right (Nat.card C) hlow
    exact (mul_le_mul_iff_right₀ (Nat.card_pos (α:=I))).mp hh
  have hB : W⊔C∈elementaryAbelianMaxSubgroups S :=
    ⟨hjoinS,inferInstance,fun B hBS hBe => (hA.2.2 B hBS hBe).trans hl⟩
  exact le_sup_left.trans (le_sSup hB)

omit [Finite G] in
private theorem fixes_of_fixes_exchanged_displacement
    (A B : Subgroup G) (hd : Disjoint A B)
    (hAB : A≤centralizer (B : Set G))
    (k : G) (hkA : k∈normalizer (A : Set G)) (hkB : k∈normalizer (B : Set G))
    (q : G) (hqA : A.map (MulAut.conj q).toMonoidHom=B)
    (a : G) (ha : a∈A) (hfix : k*⁅q,a⁆*k⁻¹=⁅q,a⁆) : k*a*k⁻¹=a := by
  let b := q*a*q⁻¹
  have hb : b∈B := hqA ▸ mem_map_of_mem (MulAut.conj q).toMonoidHom ha
  have hca : k*a⁻¹*k⁻¹∈A := (mem_normalizer_iff.mp hkA _).mp (A.inv_mem ha)
  have hcb : k*b*k⁻¹∈B := (mem_normalizer_iff.mp hkB _).mp hb
  have hab : a⁻¹*b=⁅q,a⁆ := by
    rw [show a⁻¹*b=b*a⁻¹ from (hAB (A.inv_mem ha) b hb).symm]
    rfl
  have he : (k*a⁻¹*k⁻¹)*(k*b*k⁻¹)=a⁻¹*b := by
    calc
      _ = k*(a⁻¹*b)*k⁻¹ := by group
      _ = a⁻¹*b := by rwa [hab]
  have hu := mul_injective_of_disjoint hd
    (a₁:=(⟨k*a⁻¹*k⁻¹,hca⟩,⟨k*b*k⁻¹,hcb⟩))
    (a₂:=(⟨a⁻¹,A.inv_mem ha⟩,⟨b,hb⟩)) he
  have hi : k*a⁻¹*k⁻¹=a⁻¹ := congrArg (fun x:A×B => (x.1:G)) hu
  have hh := congrArg Inv.inv hi
  simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh

omit [Finite G] in
private theorem centralizes_summand_of_centralizes_exchanged_displacement
    (A B W K : Subgroup G) (hd : Disjoint A B)
    (hAB : A≤centralizer (B : Set G))
    (hKA : K≤normalizer (A : Set G)) (hKB : K≤normalizer (B : Set G))
    (hKW : K≤centralizer (W : Set G))
    (q : G) (hqA : A.map (MulAut.conj q).toMonoidHom=B)
    (hdisp : ∀a∈A, ⁅q,a⁆∈W) : K≤centralizer (A : Set G) := by
  intro k hk a ha
  have hfix : k*⁅q,a⁆*k⁻¹=⁅q,a⁆ := by
    rw [←hKW hk _ (hdisp a ha),mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp
    (fixes_of_fixes_exchanged_displacement A B hd hAB k (hKA hk) (hKB hk) q hqA a ha hfix)).symm

private theorem fixed_index_le_of_exchanged_displacement
    (A B W K : Subgroup G) [IsMulCommutative A] (hd : Disjoint A B)
    (hAB : A≤centralizer (B : Set G))
    (hKA : K≤normalizer (A : Set G)) (hKB : K≤normalizer (B : Set G))
    (q : G) (hqA : A.map (MulAut.conj q).toMonoidHom=B)
    (hdisp : ∀a∈A, ⁅q,a⁆∈W) :
    (centralizer (K : Set G)).relIndex A≤(centralizer (K : Set G)).relIndex W := by
  let f : A→*G := {
    toFun := fun a => ⁅q,(a:G)⁆
    map_one' := by simp
    map_mul' := by
      intro a b
      have hc : (b:G)⁻¹*(a:G)⁻¹=(a:G)⁻¹*(b:G)⁻¹ :=
        congrArg Subtype.val (mul_comm (b⁻¹) (a⁻¹))
      have hqb : q*(b:G)*q⁻¹∈B := hqA ▸ mem_map_of_mem (MulAut.conj q).toMonoidHom b.property
      have hx := hAB (A.inv_mem a.property) _ hqb
      change ⁅q,(a:G)*(b:G)⁆=⁅q,(a:G)⁆*⁅q,(b:G)⁆
      simp only [commutatorElement_def]
      calc
        _ = (q*(a:G)*q⁻¹)*(q*(b:G)*q⁻¹)*((b:G)⁻¹*(a:G)⁻¹) := by group
        _ = (q*(a:G)*q⁻¹)*(q*(b:G)*q⁻¹)*((a:G)⁻¹*(b:G)⁻¹) := by rw [hc]
        _ = _ := by rw [mul_assoc,←mul_assoc (q*(b:G)*q⁻¹),hx]; group }
  have hr : f.range≤W := by rintro _ ⟨a,rfl⟩; exact hdisp a a.property
  have hc : (centralizer (K : Set G)).comap f≤(centralizer (K : Set G)).subgroupOf A := by
    intro a ha k hk
    have hfix : k*⁅q,(a:G)⁆*k⁻¹=⁅q,(a:G)⁆ := by
      have hh : k*⁅q,(a:G)⁆=⁅q,(a:G)⁆*k := ha k hk
      rw [hh,mul_inv_cancel_right]
    exact mul_inv_eq_iff_eq_mul.mp
      (fixes_of_fixes_exchanged_displacement A B hd hAB k (hKA hk) (hKB hk) q hqA a a.property hfix)
  calc
    _ ≤ ((centralizer (K : Set G)).comap f).index := index_antitone hc
    _ = (centralizer (K : Set G)).relIndex f.range := index_comap _ _
    _ ≤ _ := relIndex_le_of_le_right hr ((centralizer (K : Set G)).subgroupOf W).index_ne_zero_of_finite

/-- An exchanged pair of supports transfers their fixed-point indices to
an elementary intersection. Maximum elementary replacement then places that
intersection in J(Q), so its Thompson-center envelope centralizes both supports. -/
theorem DecomposableMarker.maxJ_envelope_centralizes_of_exchanged_supports
    (Q V W A B F : Subgroup G) [IsElementaryAbelian 2 V]
    (hWV : W≤V) (hWQ : W≤Q) (hV : A⊔B=V) (hd : Disjoint A B)
    (hFJ : F≤elementaryAbelianMaxJ Q)
    (hFC : F≤centralizer (elementaryAbelianMaxJ Q : Set G))
    (hact : ∀H∈elementaryAbelianMaxSubgroups Q,
      H≤normalizer (A : Set G) ∧ H≤normalizer (B : Set G) ∧
      (centralizer (V : Set G)).relIndex H≤4 ∧
      (¬H≤centralizer (V : Set G) →
        4≤(centralizer (H : Set G)).relIndex A ∨
        4≤(centralizer (H : Set G)).relIndex B))
    (q : G) (hqA : A.map (MulAut.conj q).toMonoidHom=B)
    (hqB : B.map (MulAut.conj q).toMonoidHom=A)
    (hdisp : ∀v∈V, ⁅q,v⁆∈W) :
    W≤elementaryAbelianMaxJ Q ∧ F≤centralizer (V : Set G) := by
  have hAV : A≤V := hV ▸ le_sup_left
  have hBV : B≤V := hV ▸ le_sup_right
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAV
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hAB : A≤centralizer (B : Set G) :=
    hAV.trans (V.le_centralizer.trans (centralizer_le hBV))
  have hWJ : W≤elementaryAbelianMaxJ Q := by
    apply maxJ_contains_elementary_of_large_fixed_index Q W hWQ
    intro H hH hn
    obtain ⟨hHA,hHB,hi,hm⟩ := hact H hH
    have hlow : 4≤(centralizer (H : Set G)).relIndex W := by
      rcases hm (fun hh => hn (hh.trans (centralizer_le hWV))) with ha | hb
      · exact ha.trans (fixed_index_le_of_exchanged_displacement A B W H hd hAB
          hHA hHB q hqA (fun a ha => hdisp a (hAV ha)))
      · exact hb.trans (fixed_index_le_of_exchanged_displacement B A W H hd.symm
          (le_centralizer_iff.mp hAB) hHB hHA q hqB (fun b hb => hdisp b (hBV hb)))
    exact (relIndex_le_of_le_left (centralizer_le hWV)
      ((centralizer (V : Set G)).subgroupOf H).index_ne_zero_of_finite).trans (hi.trans hlow)
  have hFA : F≤normalizer (A : Set G) :=
    hFJ.trans (sSup_le fun H hH => (hact H hH).1)
  have hFB : F≤normalizer (B : Set G) :=
    hFJ.trans (sSup_le fun H hH => (hact H hH).2.1)
  have hFW : F≤centralizer (W : Set G) := hFC.trans (centralizer_le hWJ)
  have hCA : F≤centralizer (A : Set G) :=
    centralizes_summand_of_centralizes_exchanged_displacement A B W F hd hAB
      hFA hFB hFW q hqA (fun a ha => hdisp a (hAV ha))
  have hCB : F≤centralizer (B : Set G) :=
    centralizes_summand_of_centralizes_exchanged_displacement B A W F hd.symm
      (le_centralizer_iff.mp hAB) hFB hFA hFW q hqB (fun b hb => hdisp b (hBV hb))
  refine ⟨hWJ,le_centralizer_iff.mp ?_⟩
  rw [←hV]
  exact sup_le (le_centralizer_iff.mp hCA) (le_centralizer_iff.mp hCB)

end CFSG.Quasithin.Chapter15.Section01
