module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSElementCentralizers
public import Theory.Representation.SL3.DualLiftRanks
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Rank bounds for the original nonblock MS core

Two commuting subgroups in opposite elementary dual lifts, each with a
nonzero image modulo U = Z(Q), have images of order at most 2^n. The
proof uses their literal coordinates in the same original MS quotient.
For any abelian subgroup of Q, the first-axis kernel and second projection
then give order at most 2^(6n). The original elementary lifts attain that
bound, proving m₂(Q) = 6n.

These are the core and commuting-subgroup bounds used in C.1.35's proof.
The larger-core equality Q = O₂(KS), MSData construction, component
geometry and terminal representation exclusion remain obligations of
qt-d-1222-rankone-uniqueness-nonblock. In particular, the rank theorem
here concerns Q and does not claim m₂(KS) = 6n.
Source: Aschbacher--Smith, C.1.35(2)--(4), printed pp.137--139,
applied in original 4.3.11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem image_card_le_field {F X : Type*} [Field F] [Finite F] [Group X]
    (p : X →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (A : Subgroup X) (f g : Module.Dual F (Fin 3 → F))
    (h : ∀ x ∈ A, ∃ a : F, (p x).toAdd = (a • f,a • g)) :
    Nat.card (A.map p) ≤ Nat.card F := by
  have hh (x : A.map p) : ∃ a : F, x.val.toAdd = (a • f,a • g) := by
    obtain ⟨y,hy,he⟩ := x.property
    rw [←he]
    exact h y hy
  choose a ha using hh
  apply Nat.card_le_card_of_injective a
  intro x y he
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  rw [ha x,ha y,he]

private theorem dualLift_coordinates (d : MSData c n)
    (p : Q c →* Multiplicative
      (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
        Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))
    (a b : d.field.Carrier) (w : Q c) (hw : (w : G) ∈ dualLift d p a b) :
    ∃ f : Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier),
      (p w).toAdd = (a • f,b • f) := by
  have hh : p w ∈ (dualDiagonal a b).range :=
    (mem_map_iff_mem (Q c).subtype_injective).mp hw
  obtain ⟨f,hf⟩ := hh
  exact ⟨f.toAdd,(congrArg Multiplicative.toAdd hf).symm⟩

/-- The two opposite elementary lifts satisfy the line bounds used in
C.1.35(3): mutually centralizing subgroups with nonzero images modulo U
have images of order at most 2^n. The quotient is the original MS quotient. -/
theorem MSData.exists_commuting_dual_lift_bounds (d : MSData c n) :
    ∃ p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧ p.ker = (U c).subgroupOf (Q c) ∧
      (∀ a b : d.field.Carrier,
        IsElementaryAbelian 2 (dualLift d p a b) ∧
        U c ≤ dualLift d p a b ∧ dualLift d p a b ≤ Q c ∧
        K c ≤ normalizer (dualLift d p a b : Set G) ∧
        (a ≠ 0 ∨ b ≠ 0 → Nat.card (dualLift d p a b) = 2^(6*n))) ∧
      ∀ A B : Subgroup G, A ≤ dualLift d p 1 0 → B ≤ dualLift d p 0 1 →
        ¬ A ≤ U c → ¬ B ≤ U c → A ≤ Subgroup.centralizer (B : Set G) →
        (U c).relIndex A ≤ 2^n ∧ (U c).relIndex B ≤ 2^n := by
  obtain ⟨p,hp,hk,hl,hc⟩ := d.exists_element_centralizers
  refine ⟨p,hp,hk,hl,?_⟩
  intro A B hA hB hAU hBU hAB
  have hAQ : A ≤ Q c := hA.trans (hl 1 0).2.2.1
  have hBQ : B ≤ Q c := hB.trans (hl 0 1).2.2.1
  obtain ⟨x,hx,hxu⟩ := SetLike.not_le_iff_exists.mp hAU
  obtain ⟨y,hy,hyu⟩ := SetLike.not_le_iff_exists.mp hBU
  let xQ : Q c := ⟨x,hAQ hx⟩
  let yQ : Q c := ⟨y,hBQ hy⟩
  have hfirst (w : Q c) (hw : (w : G) ∈ A) : (p w).toAdd.2 = 0 := by
    obtain ⟨f,hf⟩ := dualLift_coordinates d p 1 0 w (hA hw)
    rw [hf,zero_smul]
  have hsecond (w : Q c) (hw : (w : G) ∈ B) : (p w).toAdd.1 = 0 := by
    obtain ⟨f,hf⟩ := dualLift_coordinates d p 0 1 w (hB hw)
    rw [hf,zero_smul]
  have hy0 : (p yQ).toAdd.2 ≠ 0 := by
    intro he
    have hpy : p yQ = 1 := by
      apply Multiplicative.toAdd.injective
      exact Prod.ext (hsecond yQ hy) he
    have hh : yQ ∈ p.ker := hpy
    rw [hk] at hh
    exact hyu hh
  have hind (C : Subgroup G) (hC : C ≤ Q c) :
      (U c).relIndex C = Nat.card ((C.subgroupOf (Q c)).map p) := by
    have hh := (U c).relIndex_comap (Q c).subtype (C.subgroupOf (Q c))
    rw [map_subgroupOf_eq_of_le hC] at hh
    rw [←hh]
    change ((U c).subgroupOf (Q c)).relIndex (C.subgroupOf (Q c)) = _
    rw [←hk,relIndex_ker]
  have hF : Nat.card d.field.Carrier = 2^n := by rw [d.field.card_eq,d.degree_eq]
  constructor
  · rw [hind A hAQ,←hF]
    apply image_card_le_field p (A.subgroupOf (Q c)) (p yQ).toAdd.2 0
    intro w hw
    have hwA : (w : G) ∈ A := hw
    by_cases hwu : (w : G) ∈ U c
    · have hpw : p w = 1 := show w ∈ p.ker from hk.symm ▸ hwu
      refine ⟨0,?_⟩
      rw [hpw,zero_smul,zero_smul]
      rfl
    · have hwy : Commute (w : G) (yQ : G) :=
        (mem_centralizer_iff.mp (hAB hwA) y hy).symm
      obtain ⟨a,ha⟩ := ((hc w (hA hwA) hwu).1 yQ).mp hwy
      have ha0 : a ≠ 0 := by
        intro he
        exact hy0 (by simpa only [he,zero_smul] using ha)
      refine ⟨a⁻¹,Prod.ext ?_ ?_⟩
      · rw [ha,inv_smul_smul₀ ha0]
      · rw [hfirst w hwA,smul_zero]
  · rw [hind B hBQ,←hF]
    apply image_card_le_field p (B.subgroupOf (Q c)) 0 (p xQ).toAdd.1
    intro w hw
    have hwB : (w : G) ∈ B := hw
    have hxw : Commute (xQ : G) (w : G) :=
      (mem_centralizer_iff.mp (hAB hx) w hwB).symm
    obtain ⟨a,ha⟩ := ((hc xQ (hA hx) hxu).1 w).mp hxw
    exact ⟨a,Prod.ext (by rw [hsecond w hwB,smul_zero]) ha⟩

variable [Finite G]

/-- Every abelian subgroup of the original core has order at most 2^(6n).
This uses only the original natural-center, doubled-dual marking. -/
theorem MSData.abelian_core_card_le (d : MSData c n)
    (A : Subgroup (Q c)) [IsMulCommutative A] : Nat.card A ≤ 2^(6*n) := by
  obtain ⟨p,hp,hk,hl,hc⟩ := d.exists_element_centralizers
  have hcomm (w z : Q c) (hw2 : (p w).toAdd.2 = 0)
      (hw1 : (p w).toAdd.1 ≠ 0) (hwz : Commute w z) :
      ∃ a : d.field.Carrier, (p z).toAdd.2 = a • (p w).toAdd.1 := by
    have hw : (w : G) ∈ dualLift d p 1 0 := by
      apply mem_map_of_mem (Q c).subtype
      refine ⟨Multiplicative.ofAdd (p w).toAdd.1,?_⟩
      apply Multiplicative.toAdd.injective
      change (1 • (p w).toAdd.1,0 • (p w).toAdd.1) = (p w).toAdd
      exact Prod.ext (one_smul _ _) ((zero_smul _ _).trans hw2.symm)
    have hwu : (w : G) ∉ U c := by
      intro hu
      have hwk : w ∈ p.ker := hk.symm ▸ hu
      exact hw1 (congrArg (fun v => v.toAdd.1) (show p w = 1 from hwk))
    exact ((hc w hw hwu).1 z).mp (congrArg Subtype.val hwz.eq)
  have hker : p.ker = center (Q c) := hk.trans
    ((center (Q c)).comap_map_eq_self_of_injective (Q c).subtype_injective)
  have hh := dual_abelian_subgroup_card_le p hcomm A
  rw [hker,d.center_card,d.field.card_eq,d.degree_eq] at hh
  calc
    Nat.card A ≤ (2^n)^3 * 2^(3*n) := hh
    _ = 2^(6*n) := by
      rw [←pow_mul,←pow_add]
      congr 1
      omega

/-- The original special core has two-rank exactly 6n, attained by either
elementary dual lift. No equality with O₂(KS) is used. -/
theorem MSData.core_primeRank (d : MSData c n) : primeRank 2 (Q c) = 6*n := by
  apply le_antisymm
  · apply (primeRank_le_iff_elementary_card_le (Q c)).mpr
    intro E hE
    let := hE
    exact d.abelian_core_card_le E
  · obtain ⟨A,B,hA,_,hAc,_,_,_,_,hQ⟩ := d.exists_elementary_core_decomposition
    have hAQ : A ≤ Q c := le_sup_left.trans_eq hQ
    let E := A.subgroupOf (Q c)
    let e : E ≃* A := subgroupOfEquivOfLe hAQ
    let := hA
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
    have hec : Nat.card E = 2^(6*n) := (Nat.card_congr e.toEquiv).trans hAc
    have hh := (primeRank_le_iff_elementary_card_le (p := 2)
      (n := primeRank 2 (Q c)) (Q c)).mp le_rfl E inferInstance
    rw [hec] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
