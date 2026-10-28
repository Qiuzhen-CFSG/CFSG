module

public import GorensteinWalter.DihedralPSL2Core
public import GorensteinWalter.PSL2InvolutionFusion
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# The whole linear model from a dihedral involution centralizer

For an odd-core-free finite group with a self-centralizing dihedral Sylow
subgroup of order eight and order divisible by three, unconditional
Gorenstein–Walter supplies a normal odd-index PSL2 or PGL2 subgroup.
Its characteristic PSL2 core contains the marked central involution.
Fusion inside that core gives the whole group as its product with the
marked Sylow subgroup. The original linear subgroup consequently has
index dividing eight, so its odd index is one.

No exclusion of normal index-two subgroups is assumed: PGL2 is retained.
-/

open Subgroup GorensteinWalter
noncomputable section
namespace Theory.GroupTheory.DihedralEightCentralizer
universe u
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem central_unique (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (x y : S) (hx : x ∈ center S) (hy : y ∈ center S)
    (hxne : x ≠ 1) (hyne : y ≠ 1) : x = y := by
  have hmodel : ∀ a b : DihedralGroup 4,
      a ∈ center (DihedralGroup 4) → b ∈ center (DihedralGroup 4) →
      a ≠ 1 → b ≠ 1 → a = b := by decide +kernel
  apply eS.injective
  apply hmodel
  · apply mem_center_iff.mpr
    intro z
    obtain ⟨w, rfl⟩ := eS.surjective z
    simpa only [map_mul] using congrArg eS (mem_center_iff.mp hx w)
  · apply mem_center_iff.mpr
    intro z
    obtain ⟨w, rfl⟩ := eS.surjective z
    simpa only [map_mul] using congrArg eS (mem_center_iff.mp hy w)
  · exact fun h => hxne (eS.injective (h.trans (map_one eS).symm))
  · exact fun h => hyne (eS.injective (h.trans (map_one eS).symm))

/-- The marked involution belongs to every even-order normal subgroup. -/
public theorem involution_mem_normal (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (N : Subgroup H) [N.Normal] (hN : 2 ∣ Nat.card N) : t ∈ N := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hN
  have hxH : orderOf (x : H) = 2 := (orderOf_injective N.subtype N.subtype_injective x).trans hx
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (x := (x : H)) (n := 1) (by simpa using hxH)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hyN : (y : H) ∈ N := hg ▸ (inferInstance : N.Normal).conj_mem x x.property g
  have hyne : y ≠ 1 := by
    intro h
    have hxe : (MulAut.conj g) (x : H) = 1 := hg.trans (congrArg Subtype.val h)
    have hx1 : (x : H) = 1 := (MulAut.conj g).injective (hxe.trans (map_one _).symm)
    simp [hx1] at hxH
  let B := N.subgroupOf (S : Subgroup H)
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr (by
    intro hB
    have hb : y ∈ B := hyN
    rw [hB] at hb
    exact hyne (mem_bot.mp hb))
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨z, hzne, hzcentral⟩ := exists_nontrivial_center_mem_normal B (p := 2)
  have htS : t ∈ (S : Subgroup H) := hC ▸ mem_centralizer_singleton_iff.mpr rfl
  let tS : S := ⟨t, htS⟩
  have htcentral : tS ∈ center S := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    have ha : (a : H) ∈ centralizer ({t} : Set H) := by rw [hC]; exact a.property
    exact mem_centralizer_singleton_iff.mp ha
  have htne : tS ≠ 1 := by
    intro h
    have he : t = 1 := congrArg Subtype.val h
    simp [he] at ht
  have hze : (z : S) = tS := central_unique S eS z tS hzcentral htcentral
    (fun h => hzne (Subtype.ext h)) htne
  have hzN : ((z : S) : H) ∈ N := z.property
  have he : ((z : S) : H) = t := congrArg Subtype.val hze
  rwa [he] at hzN

omit [Finite H] in
private theorem normal_sup_eq_top_of_fusion (S : Sylow 2 H)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (N : Subgroup H) [N.Normal] (htN : t ∈ N)
    (hfusion : ∀ x y : N, IsInvolution x → IsInvolution y →
      ∃ g : N, g * x * g⁻¹ = y) : (S : Subgroup H) ⊔ N = ⊤ := by
  let tN : N := ⟨t, htN⟩
  have htI : IsInvolution tN := by
    constructor
    · intro h
      have he : t = 1 := congrArg Subtype.val h
      simp [he] at ht
    · apply Subtype.ext
      exact ht ▸ pow_orderOf_eq_one t
  have hsup : (S : Subgroup H) ⊔ N = ⊤ := by
    apply top_le_iff.mp
    intro g _
    let t' : N := MulAut.conjNormal (H := N) g tN
    have ht'I : IsInvolution t' := by
      constructor
      · intro h
        exact htI.1 ((MulAut.conjNormal g).injective (h.trans (map_one _).symm))
      · simpa only [map_pow, map_one] using congrArg (MulAut.conjNormal (H := N) g) htI.2
    obtain ⟨n, hn⟩ := hfusion t' tN ht'I htI
    have hng : (n : H) * g ∈ (S : Subgroup H) := by
      rw [← hC, mem_centralizer_singleton_iff]
      have he : (n : H) * (g * t * g⁻¹) * (n : H)⁻¹ = t := congrArg Subtype.val hn
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (n * g) * t * (n * g)⁻¹ = (n : H) * (g * t * g⁻¹) * (n : H)⁻¹ := by group
        _ = t := he
    have hninv : (n : H)⁻¹ ∈ (S : Subgroup H) ⊔ N := (le_sup_right : N ≤ (S : Subgroup H) ⊔ N) (N.inv_mem n.property)
    have hng' : (n : H) * g ∈ (S : Subgroup H) ⊔ N := (le_sup_left : (S : Subgroup H) ≤ (S : Subgroup H) ⊔ N) hng
    simpa using ((S : Subgroup H) ⊔ N).mul_mem hninv hng'
  exact hsup

omit [Finite H] in
private theorem not_aSeven (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S) :
    ¬ Nonempty (H ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  have htI : IsInvolution (e t) := by
    constructor
    · intro h
      have he : t = 1 := e.injective (h.trans (map_one e).symm)
      simp [he] at ht
    · have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
      simpa using congrArg e ht2
  obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (e t) a7t htI (by constructor <;> decide +kernel)
  let f := e.trans (MulAut.conj g)
  have hft : f t = a7t := hg
  let a := f.symm a7a
  have hac : a ∈ centralizer ({t} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    apply f.injective
    simp only [map_mul, hft, a, f.apply_symm_apply]
    decide +kernel
  have haord : orderOf a = 3 := by
    rw [MulEquiv.orderOf_eq]
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  have hScard : Nat.card S = 8 := (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have hdvd : 3 ∣ Nat.card S := by
    have haS : a ∈ (S : Subgroup H) := hC ▸ hac
    have he := orderOf_injective (S : Subgroup H).subtype Subtype.val_injective (⟨a, haS⟩ : S)
    change orderOf a = orderOf (⟨a, haS⟩ : S) at he
    rw [← haord, he]
    exact orderOf_dvd_natCard (⟨a, haS⟩ : S)
  rw [hScard] at hdvd
  norm_num at hdvd

/-- A specified normal odd-field PSL2 core supplements the marked Sylow subgroup. -/
public theorem psl2_core_sup_eq_top
    (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (N : Subgroup H) [N.Normal] (eN : N ≃* PSL2 F) :
    (S : Subgroup H) ⊔ N = ⊤ := by
  have hNtwo : 2 ∣ Nat.card N := by
    let T : Sylow 2 (PSL2 F) := Classical.choice Sylow.nonempty
    obtain ⟨m, hm, ⟨eT⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF T
    have hTc : Nat.card T = 2 * 2 ^ m :=
      (Nat.card_congr eT.toEquiv).trans DihedralGroup.nat_card
    rw [Nat.card_congr eN.toEquiv]
    exact (show 2 ∣ Nat.card T by rw [hTc]; exact dvd_mul_right _ _).trans
      T.card_subgroup_dvd_card
  apply normal_sup_eq_top_of_fusion S t ht hC N
    (involution_mem_normal S eS t ht hC N hNtwo)
  intro x y hx hy
  have hmap (a : N) (ha : IsInvolution a) : IsInvolution (eN a) := by
    refine ⟨fun h => ha.1 (eN.injective (h.trans (map_one eN).symm)), ?_⟩
    simpa only [map_pow, map_one] using congrArg eN ha.2
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hF
    (eN x) (eN y) (hmap x hx) (hmap y hy)
  refine ⟨eN.symm g, ?_⟩
  apply eN.injective
  simpa only [map_mul, map_inv, eN.apply_symm_apply] using hg

/-- The actual group is an odd-field PSL2 or PGL2 model; no extension remains. -/
public theorem exists_linear_model
    (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (hO : pPrimeCore 2 H = ⊥) (hthree : 3 ∣ Nat.card H) :
    ∃ (F : Type u) (iF : Field F) (_ : Finite F),
      let : Field F := iF
      IsOddPrimePower (Nat.card F) ∧
        (Nonempty (H ≃* PSL2 F) ∨ Nonempty (H ≃* PGL2 F)) := by
  have hD : HasDihedralSylowTwo H := by
    intro T
    exact ⟨2, by decide, ⟨(Sylow.equiv T S).trans eS⟩⟩
  have hnot2 : ¬ IsPGroup 2 H := by
    intro h2
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hd : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hn ▸ hthree)
    norm_num at hd
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (G := H) hO).trans
      (QuotientGroup.quotientBot (G := H))
  rcases gorensteinWalter H hD with ⟨_, htwo⟩ | ⟨_, ⟨eA⟩⟩ |
      ⟨_, F, hF, Nq, hNq, hoddq, hmodels⟩
  · exact (hnot2 (htwo.of_equiv eQ)).elim
  · exact (not_aSeven S eS t ht hC ⟨eQ.symm.trans eA⟩).elim
  · let N := Nq.map eQ.toMonoidHom
    let eN : Nq ≃* N := Subgroup.equivMapOfInjective Nq eQ.toMonoidHom eQ.injective
    let : N.Normal := hNq.map eQ.toMonoidHom eQ.surjective
    have hodd : Odd N.index := by
      dsimp [N]
      rw [Subgroup.index_map_equiv]
      exact hoddq
    have hsup : (S : Subgroup H) ⊔ N = ⊤ := by
      rcases hmodels with hPSL | hPGL
      · exact psl2_core_sup_eq_top S eS t ht hC F hF N (eN.symm.trans hPSL.some)
      · let L := (commutator N).map N.subtype
        let : L.Normal := ConjAct.normal_of_characteristic_of_normal
        let eL : L ≃* PSL2 F :=
          (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).symm.trans
            (commutator_mulEquiv_psl2_of_mulEquiv_pgl2 F hF
              (eN.symm.trans hPGL.some)).some
        have hL := psl2_core_sup_eq_top S eS t ht hC F hF L eL
        apply top_unique
        rw [← hL]
        exact sup_le_sup_left (Subgroup.map_subtype_le _) _
    have hScard : Nat.card S = 8 :=
      (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
    have hind : N.index ∣ 8 := by
      rw [← hScard, ← Subgroup.relIndex_top_right N, ← hsup,
        Subgroup.relIndex_sup_right]
      exact Subgroup.relIndex_dvd_card N (S : Subgroup H)
    have hindex : N.index = 1 :=
      Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right 3)
        (dvd_refl _) (by simpa using hind)
    have htop : N = ⊤ := Subgroup.index_eq_one.mp hindex
    let eH : H ≃* N := ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm
    refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
    exact hmodels.imp (fun e => ⟨eH.trans (eN.symm.trans e.some)⟩)
      (fun e => ⟨eH.trans (eN.symm.trans e.some)⟩)

end Theory.GroupTheory.DihedralEightCentralizer
