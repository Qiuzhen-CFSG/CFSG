module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCentralizerCore
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNine
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperCore
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.CharacteristicTwoSymplecticFourAction

/-!
# The original point-centralizer core of 13.5.15

Assume the established source identity O₂(LT)=V. The Sylow bound and the
original quotient H/O₂(H) of order 36 bound O₂(H) by 64. The point-centralizer
core P=O₂(Gz) is the central product of the original quaternion subgroup U_H
and an abelian subgroup of order two or four. Its center is that second
factor, its central quotient has order sixteen, and its Frattini subgroup
is the original involution subgroup V₁.

The characteristic-two centralizer condition and the preserved commutator
form give a faithful action of Gz/P on six points. In particular seven does
not divide the order of Gz. This last statement uses only O₂(LT)=V, without
a maximality premise, and is the source consumer excluding an upper A₇
component in the proof of original maximality.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.5.15(6), printed p.921; the earlier maximality application is 13.3.2.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCoreGeometry
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH) (hQ : D.LT.pCoreIn 2 = D.V)
include d h e hseed hn hU hQ

theorem original_core_card_le : Nat.card D.QH ≤ 64 := by
  have hs := SourceNine.sylow_card_eq_four_mul_core h
    (SourceStarFull.original_star_card d h e hseed hn hU hQ)
  have ht := Section03.SourceCompletion.SixMaximality.UpperCore.original_sylow_card_le_of_core_eq_module d h hQ
  omega

theorem point_factor_card :
    let C := D.Gz.pCoreIn 2 ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))
    Nat.card C = 2 ∨ Nat.card C = 4 := by
  let P := D.Gz.pCoreIn 2
  let C := P ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))
  have hz := SourceCentralizerCore.point_core_factor_overlap d h e hseed hn hU
  change D.UH ⊓ C = D.V₁ at hz
  have hzc : D.V₁ ≤ C := hz.ge.trans inf_le_right
  have hlo : 2 ≤ Nat.card C := h.point_card ▸ card_le_of_le hzc
  have hCU : C ≤ centralizer (D.UH : Set G) :=
    SourceCentralizerCore.point_core_factor_commutes h hseed hn
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.UH C
    (hCU.trans (Subgroup.centralizer_le_normalizer _))
  rw [hz,h.point_card,←SourceCentralizerCore.point_core_factorization d h e hseed hn hU,
    (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1] at hm
  have hPle : Nat.card P ≤ 64 := (card_le_of_le
    (SourceCentralizerCore.point_core_le_core h)).trans (original_core_card_le d h e hseed hn hU hQ)
  have hhi : Nat.card C ≤ 4 := by change 32 * Nat.card C = 2 * Nat.card P at hm; omega
  have hd := (isPGroup_pCoreIn 2 D.Gz).to_le (show C ≤ P from inf_le_left)
  obtain ⟨n,hncard⟩ := hd.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n)
    rw [←hncard] at hpow
    omega
  change Nat.card C = 2 ∨ Nat.card C = 4
  interval_cases n
  · have hh : Nat.card C = 1 := hncard
    omega
  · exact Or.inl hncard
  · exact Or.inr hncard

private theorem point_factor_commutative :
    IsMulCommutative (D.Gz.pCoreIn 2 ⊓
      ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) : Subgroup G) := by
  rcases point_factor_card d h e hseed hn hU hQ with hc | hc
  · let : IsCyclic (D.Gz.pCoreIn 2 ⊓
        ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) : Subgroup G) :=
      isCyclic_of_prime_card (p := 2) hc
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hc)

theorem point_core_center_image :
    (center (D.Gz.pCoreIn 2)).map (D.Gz.pCoreIn 2).subtype =
      D.Gz.pCoreIn 2 ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) := by
  let P := D.Gz.pCoreIn 2
  let C := P ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))
  let : IsMulCommutative C := point_factor_commutative d h e hseed hn hU hQ
  have hfac := SourceCentralizerCore.point_core_factorization d h e hseed hn hU
  change P = D.UH ⊔ C at hfac
  have hCU : C ≤ centralizer (D.UH : Set G) :=
    SourceCentralizerCore.point_core_factor_commutes h hseed hn
  have hzc : D.V₁ ≤ C :=
    (SourceCentralizerCore.point_core_factor_overlap d h e hseed hn hU).ge.trans inf_le_right
  have hCP : C ≤ centralizer (P : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hfac]
    exact sup_le (le_centralizer_iff.mp hCU) C.le_centralizer
  apply le_antisymm
  · rintro x ⟨x,hx,rfl⟩
    have hxU : (x : G) ∈ centralizer (D.UH : Set G) := by
      intro u hu
      exact congrArg Subtype.val (mem_center_iff.mp hx
        ⟨u,SourceCentralizerCore.closure_le_point_core d h hu⟩)
    have hm : (x : G) ∈ (D.UH : Set G) * (C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left D.UH C
        (hCU.trans (Subgroup.centralizer_le_normalizer _)),←hfac]
      exact x.property
    obtain ⟨u,hu,c,hc,huc⟩ := hm
    have huC : u ∈ centralizer (D.UH : Set G) := by
      have hh := (centralizer (D.UH : Set G)).mul_mem hxU
        ((centralizer (D.UH : Set G)).inv_mem (hCU hc))
      rwa [←huc,mul_inv_cancel_right] at hh
    have huv := (SourceQuaternionCentralizer.closure_inf_centralizer d h e hseed hn hU).le ⟨hu,huC⟩
    change (x : G) ∈ C
    rw [←huc]
    exact C.mul_mem (hzc huv) hc
  · intro x hx
    change x ∈ C at hx
    exact ⟨⟨x,hx.1⟩,mem_center_iff.mpr (fun y =>
      Subtype.ext (hCP hx y y.property)),rfl⟩

theorem point_core_center_card :
    Nat.card (center (D.Gz.pCoreIn 2)) = 2 ∨ Nat.card (center (D.Gz.pCoreIn 2)) = 4 := by
  have hc : Nat.card (center (D.Gz.pCoreIn 2)) = Nat.card (D.Gz.pCoreIn 2 ⊓
      ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) : Subgroup G) := by
    calc
      _ = Nat.card ((center (D.Gz.pCoreIn 2)).map (D.Gz.pCoreIn 2).subtype) :=
        (card_map_of_injective (D.Gz.pCoreIn 2).subtype_injective).symm
      _ = _ := by rw [point_core_center_image d h e hseed hn hU hQ]
  rw [hc]
  exact point_factor_card d h e hseed hn hU hQ

theorem point_core_central_quotient_card :
    Nat.card (D.Gz.pCoreIn 2 ⧸ center (D.Gz.pCoreIn 2)) = 16 := by
  let P := D.Gz.pCoreIn 2
  let C := P ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))
  have hCU : C ≤ centralizer (D.UH : Set G) :=
    SourceCentralizerCore.point_core_factor_commutes h hseed hn
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.UH C
    (hCU.trans (Subgroup.centralizer_le_normalizer _))
  rw [SourceCentralizerCore.point_core_factor_overlap d h e hseed hn hU,
    ←SourceCentralizerCore.point_core_factorization d h e hseed hn hU,
    (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1,h.point_card] at hh
  have hcc : Nat.card (center P) = Nat.card C := by
    calc
      _ = Nat.card ((center P).map P.subtype) :=
        (card_map_of_injective P.subtype_injective).symm
      _ = _ := by rw [point_core_center_image d h e hseed hn hU hQ]
  have hi := (center P).card_mul_index
  rw [index_eq_card,hcc] at hi
  change 32 * Nat.card C = 2 * Nat.card P at hh
  change Nat.card (P ⧸ center P) = 16
  rcases point_factor_card d h e hseed hn hU hQ with hc | hc <;>
    change Nat.card C = _ at hc <;> rw [hc] at hh hi <;> omega

private theorem point_core_squares (x : D.Gz.pCoreIn 2) : (x : G) ^ 2 ∈ D.V₁ := by
  let P := D.Gz.pCoreIn 2
  let C := P ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))
  have hzc : D.V₁ ≤ C :=
    (SourceCentralizerCore.point_core_factor_overlap d h e hseed hn hU).ge.trans inf_le_right
  let Z := D.V₁.subgroupOf C
  let : Z.Normal := normal_subgroupOf_of_le_normalizer
    ((show C ≤ D.Gz from inf_le_left.trans (pCoreIn_le 2 D.Gz)).trans
      (centralizer_le_normalizer (D.V₁ : Set G)))
  have hZcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hzc).toEquiv).trans h.point_card
  have hZidx : Z.index ∣ 2 := by
    have hh := Z.card_mul_index
    rw [hZcard] at hh
    rcases point_factor_card d h e hseed hn hU hQ with hc | hc <;>
      change Nat.card C = _ at hc <;> rw [hc] at hh
    · have hi : Z.index = 1 := by omega
      rw [hi]
      exact one_dvd 2
    · have hi : Z.index = 2 := by omega
      rw [hi]
  have hcsq (c : C) : (c : G) ^ 2 ∈ D.V₁ := by
    have hp : (QuotientGroup.mk' Z c) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        ((_root_.orderOf_dvd_natCard (QuotientGroup.mk' Z c)).trans hZidx)
    have he : QuotientGroup.mk' Z (c ^ 2) = 1 := by rw [map_pow]; exact hp
    have hm : c ^ 2 ∈ Z := (QuotientGroup.eq_one_iff _).mp he
    exact hm
  obtain ⟨_,_,hUz,_,q,_⟩ := SourceQuaternion.source13_5_15_five d h e hseed hn hU
  have husq (u : D.UH) : (u : G) ^ 2 ∈ D.V₁ := by
    have hh := q.square_mem_center u
    rw [hUz] at hh
    exact hh
  have hCU : C ≤ centralizer (D.UH : Set G) :=
    SourceCentralizerCore.point_core_factor_commutes h hseed hn
  have hm : (x : G) ∈ (D.UH : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left D.UH C
      (hCU.trans (Subgroup.centralizer_le_normalizer _)),
      ←SourceCentralizerCore.point_core_factorization d h e hseed hn hU]
    exact x.property
  obtain ⟨u,hu,c,hc,huc⟩ := hm
  have hcomm : Commute u c := hCU hc u hu
  rw [←huc,hcomm.mul_pow]
  exact D.V₁.mul_mem (husq ⟨u,hu⟩) (hcsq ⟨c,hc⟩)

theorem point_core_frattini_image :
    (frattini (D.Gz.pCoreIn 2)).map (D.Gz.pCoreIn 2).subtype = D.V₁ := by
  let P := D.Gz.pCoreIn 2
  let Z := D.V₁.subgroupOf P
  have hUP := SourceCentralizerCore.closure_le_point_core d h
  have hzU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hzP : D.V₁ ≤ P := hzU.trans hUP
  let : Z.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 D.Gz).trans (centralizer_le_normalizer (D.V₁ : Set G)))
  have hsq (q : P ⧸ Z) : q ^ 2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (point_core_squares d h e hseed hn hU hQ x)
  have hinv (q : P ⧸ Z) : q⁻¹ = q :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq q)
  have helem : IsElementaryAbelian 2 (P ⧸ Z) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc
        x * y = (x * y)⁻¹ := (hinv _).symm
        _ = y * x := by rw [mul_inv_rev,hinv,hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  apply le_antisymm
  · exact (map_mono (frattini_le_of_elementary_quotient
      (isPGroup_pCoreIn 2 D.Gz) Z helem)).trans_eq (map_subgroupOf_eq_of_le hzP)
  · obtain ⟨_,_,hUz,_,q,_⟩ := SourceQuaternion.source13_5_15_five d h e hseed hn hU
    let : IsExtraspecial 2 D.UH := q.extraspecial
    let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
    let : Fact (IsPGroup 2 P) := ⟨isPGroup_pCoreIn 2 D.Gz⟩
    have hm := map_mono (f := P.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hUP))
    rw [map_map] at hm
    change (frattini D.UH).map D.UH.subtype ≤ (frattini P).map P.subtype at hm
    rw [IsExtraspecial.frattini_eq_center (p := 2),hUz,map_subgroupOf_eq_of_le hzU] at hm
    exact hm

theorem point_core_frattini_card : Nat.card (frattini (D.Gz.pCoreIn 2)) = 2 := by
  calc
    _ = Nat.card ((frattini (D.Gz.pCoreIn 2)).map (D.Gz.pCoreIn 2).subtype) :=
      (card_map_of_injective (D.Gz.pCoreIn 2).subtype_injective).symm
    _ = Nat.card D.V₁ := by rw [point_core_frattini_image d h e hseed hn hU hQ]
    _ = 2 := h.point_card

theorem point_group_six_action :
    ∃ f : (D.Gz ⧸ pCore 2 D.Gz) →* Equiv.Perm (Fin 6), Function.Injective f := by
  let P := D.Gz.pCoreIn 2
  let a : pCore 2 D.Gz ≃* P :=
    (pCore 2 D.Gz).equivMapOfInjective D.Gz.subtype D.Gz.subtype_injective
  have hc : centralizer (pCore 2 D.Gz : Set D.Gz) ≤ pCore 2 D.Gz := by
    simpa only [SourceCentralizerCore.point_group_characteristic d h] using
      centralizer_generalizedFitting_le D.Gz
  have hphi : Nat.card (frattini (pCore 2 D.Gz)) = 2 := by
    calc
      _ = Nat.card ((frattini (pCore 2 D.Gz)).map a.toMonoidHom) :=
        (card_map_of_injective a.injective).symm
      _ = Nat.card (frattini P) := by rw [frattini_map_equiv a]
      _ = 2 := point_core_frattini_card d h e hseed hn hU hQ
  have hcenter : Nat.card (center (pCore 2 D.Gz)) = Nat.card (center P) :=
    Nat.card_congr (centerCongr a).toEquiv
  have hZ : Nat.card (center (pCore 2 D.Gz)) ≤ 4 := by
    rw [hcenter]
    rcases point_core_center_card d h e hseed hn hU hQ with hh | hh <;>
      change Nat.card (center P) = _ at hh <;> omega
  have hquot : Nat.card (pCore 2 D.Gz ⧸ center (pCore 2 D.Gz)) = 16 := by
    have hm := (center (pCore 2 D.Gz)).card_mul_index
    rw [index_eq_card,hcenter,Nat.card_congr a.toEquiv] at hm
    have hP := (center P).card_mul_index
    rw [index_eq_card,point_core_central_quotient_card d h e hseed hn hU hQ] at hP
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hm.trans hP.symm)
  exact Subgroup.exists_injective_six_action_of_pCore hc hphi hZ hquot

theorem seven_not_dvd_point_group_card : ¬7 ∣ Nat.card D.Gz := by
  obtain ⟨f,hf⟩ := point_group_six_action d h e hseed hn hU hQ
  have hquot : ¬7 ∣ Nat.card (D.Gz ⧸ pCore 2 D.Gz) := by
    intro hd
    have hh := hd.trans (card_dvd_of_injective f hf)
    rw [Nat.card_perm,Nat.card_fin] at hh
    norm_num at hh
  have hcore : ¬7 ∣ Nat.card (pCore 2 D.Gz) := by
    have htwo : IsPGroup 2 (pCore 2 D.Gz) := pCore_isPGroup
    obtain ⟨n,hn⟩ := htwo.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬7 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 7)) hd)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D.Gz)]
  intro hd
  exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp hd).elim hquot hcore

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCoreGeometry
end
