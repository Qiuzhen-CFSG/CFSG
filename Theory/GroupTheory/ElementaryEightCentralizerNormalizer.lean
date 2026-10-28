module
public import Theory.GroupTheory.ElementaryEightCoreFreePointAction
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Normalizers of elementary eights from a point centralizer

An order-192 point centralizer prevents a full automizer of an elementary
abelian eight unless that centralizer normalizes the eight. Proper automizers
with order divisible by four are solvable. For a self-centralizing eight, this
forces its normalizer two-core to have order at least 32.

The orbit-stabilizer estimate uses only the given point centralizer, so the
application to the full binary G₂ amalgam in source 14.2.22 needs no hypothesis
on other two-local subgroups.
-/

@[expose] public noncomputable section
open Subgroup MulAction

/-- A proper elementary-eight automizer with four-divisible order is solvable. -/
theorem isSolvable_of_proper_elementary_eight_automizer
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (hne : A ≠ ⊤) (hfour : 4 ∣ Nat.card A) : Group.IsSolvable A := by
  let P : Sylow 2 A := Classical.choice inferInstance
  have hd : Nat.card P ∣ 8 := by
    have hdiv : Nat.card P ∣ 8 * 21 := by
      have hh := P.toSubgroup.card_subgroup_dvd_card.trans A.card_subgroup_dvd_card
      simpa only [card_mulAut_of_elementary_eight E hE] using hh
    have hc : Nat.Coprime (Nat.card P) 21 := by
      obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 21).pow_left n
    exact hc.dvd_mul_right.mp hdiv
  have hf : 4 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 2) hfour
  have hP : Nat.card P = 4 ∨ Nat.card P = 8 := by
    have hm := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have hd8 : (8 : ℕ).divisors = {1,2,4,8} := by decide
    rw [hd8] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    have hge := Nat.le_of_dvd Nat.card_pos hf
    omega
  rcases hP with hP | hP
  · exact isSolvable_of_elementary_eight_automorphisms_sylow_four E hE A P hP
  let e : MulAut E ≃* Matrix.PSL3Two.PSL :=
    (elementaryEight_mulAut_equiv_GL E hE).some.trans
      (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)
  let H := A.map e.toMonoidHom
  let f := e.toMonoidHom.comp A.subtype
  have hf : Function.Injective f := e.injective.comp A.subtype_injective
  let R := (P : Subgroup A).map f
  have hR : Nat.card R = 8 := (card_map_of_injective hf).trans hP
  let S : Sylow 2 Matrix.PSL3Two.PSL := Sylow.ofCard R (by
    rw [hR,Matrix.PSL3Two.card_PSL]
    decide +kernel)
  have hSH : (S : Subgroup Matrix.PSL3Two.PSL) ≤ H := by
    rintro x ⟨a,_,rfl⟩
    exact ⟨a,a.property,rfl⟩
  have hHne : H ≠ ⊤ := by
    intro hh
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [← MonoidHom.range_eq_map]
    exact hh.trans (MonoidHom.range_eq_top.mpr e.surjective).symm
  obtain ⟨K,hK,hHK⟩ := (eq_top_or_exists_le_coatom H).resolve_left hHne
  obtain ⟨K1,K2,_,_,_,_,hK1,hK2,hclass⟩ := Matrix.PSL3Two.sylow_parabolics S
  have hcardK : Nat.card K = 24 := by
    rcases (hclass K hK).mp (hSH.trans hHK) with rfl | rfl
    · exact hK1
    · exact hK2
  have hdiv : Nat.card A ∣ 24 := by
    have hh := card_dvd_of_le hHK
    rw [hcardK,show Nat.card H = Nat.card A from card_map_of_injective e.injective] at hh
    exact hh
  have hi := P.toSubgroup.card_mul_index
  rw [hP] at hi
  have hbound := Nat.le_of_dvd (by decide : 0 < 24) hdiv
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact P.toSubgroup.isSolvable_of_index_le_four (by omega)

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A full elementary-eight automizer forces an order-192 point centralizer
into the normalizer. -/
theorem centralizer_le_normalizer_of_eight_full_automizer
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (z : E) (hz : z ≠ 1)
    (hC : Nat.card (centralizer ({(z : G)} : Set G)) = 192)
    (hfull : E.normalizerMonoidHom.range = ⊤) :
    centralizer ({(z : G)} : Set G) ≤ normalizer (E : Set G) := by
  let N := normalizer (E : Set G)
  let f := E.normalizerMonoidHom
  let : MulDistribMulAction N E := MulDistribMulAction.compHom E f
  have hker : 8 ≤ Nat.card f.ker := by
    have hle : E ≤ centralizer (E : Set G) := E.le_centralizer
    have hcard := card_le_of_le hle
    rw [hE] at hcard
    rw [show f.ker = (centralizer (E : Set G)).subgroupOf N from normalizerMonoidHom_ker E,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (E : Set G))).toEquiv]
    exact hcard
  have hN : 1344 ≤ Nat.card N := by
    have hprod := f.ker.card_mul_index
    rw [index_ker,hfull,card_top,card_mulAut_of_elementary_eight E hE] at hprod
    change Nat.card f.ker * 168 = Nat.card N at hprod
    omega
  have ho : Nat.card (orbit N z) ≤ 7 := by
    let j : orbit N z → {x : E // x ≠ 1} := fun x => ⟨x, by
      intro hx
      obtain ⟨g,hg⟩ := mem_orbit_iff.mp x.property
      apply hz
      apply (f g).injective
      exact hg.trans hx |>.trans (map_one _).symm⟩
    have hj : Function.Injective j := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun t : {x : E // x ≠ 1} => (t : E)) h
    have hc : Nat.card {x : E // x ≠ 1} = 7 := by
      classical
      let : Fintype E := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card]
      have he : Fintype.card E = 8 := by simpa only [Nat.card_eq_fintype_card] using hE
      simp [he]
    exact (Nat.card_le_card_of_injective j hj).trans_eq hc
  let C := centralizer ({(z : G)} : Set G)
  let K := (stabilizer N z).map N.subtype
  have hKC : K ≤ C := by
    rintro x ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have h : (g : G) * (z : G) * (g : G)⁻¹ = (z : G) := congrArg Subtype.val hg
    exact mul_inv_eq_iff_eq_mul.mp h
  have hK : 192 ≤ Nat.card K := by
    rw [card_map_of_injective N.subtype_injective]
    have hm := Nat.card_congr (orbitProdStabilizerEquivGroup N z)
    rw [Nat.card_prod] at hm
    nlinarith
  have heq : K = C := eq_of_le_of_card_ge hKC (hC ▸ hK)
  change C ≤ N
  exact (le_of_eq heq.symm).trans (map_subtype_le (stabilizer N z))

/-- Only this elementary-eight normalizer needs solvability: its point
centralizer rules out the full order-168 automizer. -/
theorem elementary_eight_automizer_solvable_of_centralizer192
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (z : E) (hz : z ≠ 1)
    (hC : Nat.card (centralizer ({(z : G)} : Set G)) = 192)
    (hn : ¬ centralizer ({(z : G)} : Set G) ≤ normalizer (E : Set G))
    (hfour : 4 ∣ Nat.card E.normalizerMonoidHom.range) :
    Group.IsSolvable E.normalizerMonoidHom.range := by
  exact isSolvable_of_proper_elementary_eight_automizer E hE E.normalizerMonoidHom.range
    (fun ht => hn (centralizer_le_normalizer_of_eight_full_automizer E hE z hz hC ht)) hfour

/-- The actual normalizer two-core has order at least 32, using only its
self-centralizing eight and the marked point-centralizer obstruction. -/
theorem elementary_eight_normalizer_core_card_of_centralizer192
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hcent : centralizer (E : Set G) = E)
    (z : E) (hz : z ≠ 1)
    (hC : Nat.card (centralizer ({(z : G)} : Set G)) = 192)
    (hn : ¬ centralizer ({(z : G)} : Set G) ≤ normalizer (E : Set G))
    (hfour : 4 ∣ Nat.card E.normalizerMonoidHom.range) :
    32 ≤ Nat.card (pCore 2 (normalizer (E : Set G))) := by
  let f := E.normalizerMonoidHom
  have hker : Nat.card f.ker = 8 := by
    rw [show f.ker = (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) from
      normalizerMonoidHom_ker E,hcent,
      Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv,hE]
  have hkp : IsPGroup 2 f.ker := by
    rw [show f.ker = (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) from
      normalizerMonoidHom_ker E,hcent]
    exact (IsElementaryAbelian.isPGroup 2 E).comap_subtype
  let : Group.IsSolvable f.range :=
    elementary_eight_automizer_solvable_of_centralizer192 E hE z hz hC hn hfour
  have hcore := four_le_card_pCore_of_solvable_elementary_eight_automorphisms E hE f.range hfour
  have hc := f.rangeRestrict.card_pCore_of_ker_isPGroup (p := 2)
    f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hkp)
  rw [MonoidHom.ker_rangeRestrict,hker] at hc
  omega
end Subgroup
