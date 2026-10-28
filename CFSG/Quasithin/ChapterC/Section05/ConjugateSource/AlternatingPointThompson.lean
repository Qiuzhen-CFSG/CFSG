module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Source

/-!
# Thompson control in the paired alternating-five point centralizer

The original action on each block extends the marked point centralizer to
its Baumann supplement. A two-subgroup normalized by the point stabilizer
has even action: an odd point-fixing permutation has a nontrivial odd-order
commutator with the alternating point stabilizer. The four-member maximum
elementary family then leaves only the original module in each factor.
Consequently the Thompson subgroup of the point-centralizer core is the
original maximum elementary core.

Source: Aschbacher--Smith, C.5.6(7) and the proof of 14.6.9,
printed pp.1025--1026 (refs/quasithin.pdf).
-/

public section
open Subgroup BinaryPermutation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

private theorem D_fixes_last : ChapterB.Offenders.D 5 ≤
    MulAction.stabilizer FivePerm (4 : Fin 5) := by
  apply (closure_le _).mpr
  rintro a ⟨i,_,rfl⟩
  change ChapterB.Offenders.pairSwap 5 i 4 = 4
  fin_cases i <;> decide +kernel

/-- The same fifth point marks the centralizer throughout the Baumann supplement. -/
theorem AlternatingPairSetup.central_point_full_marking
    (h : AlternatingPairSetup R K L) (z : G)
    (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (hout : ¬ K ≤ centralizer ({z} : Set G))
    (s : ↥(K ⊔ ChapterB.baumann R)) :
    (s : G) ∈ centralizer ({z} : Set G) ↔ h.action s 4 = 4 := by
  obtain ⟨v,_,_,hmark⟩ := h.central_point_marking z hzS hzR hout
  have hs : (s : G) ∈ (K : Set G) * (ChapterB.baumann R : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left K _ h.normalizes]
    exact s.property
  obtain ⟨k,hk,t,ht,hkt⟩ := hs
  change k * t = (s : G) at hkt
  let kN : ↥(K ⊔ ChapterB.baumann R) := inclusion le_sup_left ⟨k,hk⟩
  let tN : ↥(K ⊔ ChapterB.baumann R) := inclusion le_sup_right ⟨t,ht⟩
  have hs' : kN * tN = s := Subtype.ext hkt
  have htA : h.action tN ∈ ChapterB.Offenders.D 5 := by
    rw [←h.baumann_image]
    exact mem_map_of_mem h.action ht
  have htfix : h.action tN 4 = 4 := D_fixes_last htA
  have htcomm : z * t = t * z := (hzR t (show t ∈ R from ht.1)).symm
  rw [←hs',map_mul]
  change k*t ∈ centralizer ({z} : Set G) ↔ h.action kN (h.action tN 4) = 4
  rw [htfix,←hmark ⟨k,hk⟩]
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro hc
    apply mul_right_cancel (b := t)
    calc
      k*z*t = k*(z*t) := mul_assoc _ _ _
      _ = k*(t*z) := by rw [htcomm]
      _ = z*k*t := by rw [←mul_assoc,hc,mul_assoc]
  · intro hc
    calc
      (k*t)*z = k*(t*z) := mul_assoc _ _ _
      _ = k*(z*t) := by rw [htcomm]
      _ = z*(k*t) := by rw [←mul_assoc,hc,mul_assoc]

private theorem odd_point_commutator : ∀ a : FivePerm, a 4 = 4 →
    a.sign ≠ 1 → ∃ b : FivePerm, b 4 = 4 ∧ b.sign = 1 ∧
      ⁅a,b⁆ ^ 3 = 1 ∧ ⁅a,b⁆ ≠ 1 := by
  decide +kernel

private theorem two_point_group_even (P : Subgroup FivePerm) (hP : IsPGroup 2 P)
    (hfix : P ≤ MulAction.stabilizer FivePerm (4 : Fin 5))
    (hn : alternatingGroup (Fin 5) ⊓ MulAction.stabilizer FivePerm (4 : Fin 5) ≤
      normalizer (P : Set FivePerm)) : P ≤ alternatingGroup (Fin 5) := by
  intro a ha
  rw [Equiv.Perm.mem_alternatingGroup]
  by_contra hsign
  obtain ⟨b,hbfix,hbsign,hc3,hc1⟩ := odd_point_commutator a (hfix ha) hsign
  have hb : b ∈ normalizer (P : Set FivePerm) :=
    hn ⟨by change b ∈ alternatingGroup (Fin 5); rwa [Equiv.Perm.mem_alternatingGroup],hbfix⟩
  have hc : ⁅a,b⁆ ∈ P := by
    change a * b * a⁻¹ * b⁻¹ ∈ P
    rw [mul_assoc a b a⁻¹, mul_assoc]
    exact P.mul_mem ha ((hb a⁻¹).mp (P.inv_mem ha))
  have he : (⟨⁅a,b⁆,hc⟩ : P) = 1 :=
    (hP.powEquiv (show Nat.Coprime 2 3 from by decide)).injective (Subtype.ext (by simpa using hc3))
  exact hc1 (congrArg Subtype.val he)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- A normalized two-subgroup of the literal point centralizer has even action. -/
theorem AlternatingPairSetup.central_point_twoGroup_image_even
    (h : AlternatingPairSetup R K L) (z : G)
    (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (hout : ¬ K ≤ centralizer ({z} : Set G))
    (W : Subgroup G) (hW : IsPGroup 2 W)
    (hWC : W ≤ centralizer ({z} : Set G))
    (hn : (K ⊔ ChapterB.baumann R) ⊓ centralizer ({z} : Set G) ≤ normalizer (W : Set G)) :
    actionImage h.action W ≤ alternatingGroup (Fin 5) := by
  let N := K ⊔ ChapterB.baumann R
  let P := W.subgroupOf N
  apply two_point_group_even (P.map h.action) (hW.comap_subtype.map h.action)
  · rintro a ⟨w,hw,rfl⟩
    exact (h.central_point_full_marking z hzS hzR hout w).mp (hWC hw)
  · intro a ha
    have haK : a ∈ (K.subgroupOf N).map h.action := h.block_image.symm ▸ ha.1
    obtain ⟨k,hk,hka⟩ := haK
    have hkC : (k : G) ∈ centralizer ({z} : Set G) :=
      (h.central_point_full_marking z hzS hzR hout k).mpr (hka.symm ▸ ha.2)
    have hkW := hn ⟨k.property,hkC⟩
    have hkP : k ∈ normalizer (P : Set N) := by
      intro w
      exact hkW w
    exact (P.le_normalizer_map h.action) (hka ▸ mem_map_of_mem h.action hkP)

private theorem transposition_not_even (i : Fin 2) :
    transposition i ∉ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases i <;> decide +kernel

private theorem line_not_even (i : Fin 2) :
    ¬ line i ≤ alternatingGroup (Fin 5) :=
  fun hh => transposition_not_even i (hh (mem_zpowers _))

private theorem actor_not_even : ¬ ChapterB.Offenders.D 5 ≤ alternatingGroup (Fin 5) :=
  fun hh => transposition_not_even 0 (hh (ChapterB.Offenders.pairSwap_mem 0 (by decide)))

/-- Even action selects the module from the original four-member factor family. -/
theorem AlternatingPairSetup.conjugate_factor_even_maximum
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (A : Subgroup G)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups
      (sourceModule K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom))
    (heven : actionImage h.action A ≤ alternatingGroup (Fin 5)) : A = sourceModule K := by
  obtain ⟨B0,B1,hfam,h0,h1⟩ := h.conjugate_factor_family x hx hnc
  rw [hfam] at hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl | rfl | rfl
  · rfl
  · exact (actor_not_even (h.conjugate_action_image x hx hnc ▸ heven)).elim
  · exact (line_not_even 0 (h0 ▸ heven)).elim
  · exact (line_not_even 1 (h1 ▸ heven)).elim

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Stellmacher
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- Even action in both factors identifies the actual Thompson subgroup. -/
theorem AlternatingPairSetup.two_block_even_thompson
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (W : Subgroup G)
    (hQW : ChapterB.baumann R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) ≤ W)
    (hWR : W ≤ R)
    (heven : actionImage h.action W ≤ alternatingGroup (Fin 5))
    (heven' : actionImage h'.action W ≤ alternatingGroup (Fin 5)) :
    elementaryAbelianMaxJ W = ChapterB.baumann R ⊓
      centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let F₁ := U₁ ⊔ V₁
  let F₂ := U₂ ⊔ V₂
  let Q := S ⊓ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hp := h.two_block_source_product h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hd := h.two_block_direct_product h' M T_H x hx (hMR hx) hindex hpair ht hnc
  have hQR := (h.two_block_maximum_core h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc).1
  have hD : IsElementaryAbelian 2 D := by
    let : IsElementaryAbelian 2 Q := hQR.2.1
    exact IsElementaryAbelian.of_le (show D ≤ Q from le_sup_right.trans_eq hp.1.symm)
  have hQWmax : Q ∈ elementaryAbelianMaxSubgroups W :=
    ⟨hQW,hQR.2.1,fun B hB he => hQR.2.2 B (hB.trans hWR) he⟩
  apply le_antisymm _ (le_sSup hQWmax)
  apply sSup_le
  intro A hAW
  have hAR : A ∈ elementaryAbelianMaxSubgroups R :=
    ⟨hAW.1.trans hWR,hAW.2.1,fun B hB he =>
      (hQR.2.2 B hB he).trans (hAW.2.2 Q hQW hQR.2.1)⟩
  have hAS : A ∈ elementaryAbelianMaxSubgroups (F₁ ⊔ (F₂ ⊔ D)) := by
    rw [←hd.1,baumann_maxFamily R]
    exact hAR
  obtain ⟨A₁,h1,B,hB,hAA⟩ := (maxFamily_sup_iff_of_disjoint_of_commuting F₁
    (F₂ ⊔ D) hd.2.1 hd.2.2.1 A).mp hAS
  obtain ⟨A₂,h2,D',hD',hBD⟩ := (maxFamily_sup_iff_of_disjoint_of_commuting F₂
    D hd.2.2.2.1 hd.2.2.2.2 B).mp hB
  have hD'eq : D' = D := eq_of_le_of_card_ge hD'.1 (hD'.2.2 D le_rfl hD)
  subst D'
  have hA₁W : A₁ ≤ W := (show A₁ ≤ A from hAA ▸ le_sup_left).trans hAW.1
  have hA₂W : A₂ ≤ W := (show A₂ ≤ A from hAA ▸ (hBD ▸ le_sup_left).trans le_sup_right).trans hAW.1
  have hA₁ : A₁ = U₁ := h.conjugate_factor_even_maximum x (hMR hx) hnc A₁ h1
    ((actionImage_mono h.action hA₁W).trans heven)
  have hA₂ : A₂ = U₂ := h'.conjugate_factor_even_maximum x (hMR hx) hi.second_noncommuting A₂ h2
    ((actionImage_mono h'.action hA₂W).trans heven')
  have hAQ : A = Q := by
    rw [hAA,hBD,hA₁,hA₂,←sup_assoc]
    exact hp.1.symm
  exact hAQ.le

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

