module
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import Theory.SpecificGroups.Suzuki.SylowSquares
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.GroupAction.BinarySingerRegularity
public import Theory.SpecificGroups.Suzuki.OddTorusContainment
public import Theory.SpecificGroups.Suzuki.OmegaGeneration
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Odd Cartan actors in Suzuki automorphism groups

An odd subgroup permuting with a Suzuki Sylow lies in its Borel: otherwise
root-omega generation gives the whole group, contradicting the orders of
odd tori. In an automorphism overgroup the inner intersection of that product
therefore has a normal Sylow. Its characteristicness forces the whole odd
actor to normalize the Sylow. Pointwise Sylow rigidity and coprime Frattini
action then embed a cyclic actor in its binary Frattini quotient; a regular
orbit bounds its order by q - 1.

The argument includes every intermediate automorphism group containing the
inner automorphisms. The consumer is the Suzuki Cartan column of
Aschbacher--Smith 7.3.4, printed p.699. The concrete subgroup inputs are
Huppert--Blackburn III, XI.3.12(e), XI.11.15 and GLS4, Lemma 3.2(h).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.SuzukiCartan

theorem root_frattini_quotient_card_le (m : ℕ) (hm : 0 < m) :
    Nat.card (SuzukiRootSubgroup m ⧸ frattini (SuzukiRootSubgroup m)) ≤ 2^(2*m+1) := by
  let R := SuzukiRootSubgroup m
  let : Fact (IsPGroup 2 R) := ⟨suzukiRootSubgroup_isPGroup m hm⟩
  have hz : center R ≤ frattini R := by
    intro z hz
    obtain ⟨x,hx⟩ := suzukiRootSubgroup_square_surjective m hm ⟨z,hz⟩
    have hx' : x^2=z := hx
    rw [←hx']
    exact pth_power_mem_frattini_of_isPGroup (p := 2) x
  have hc := Nat.card_le_card_of_injective (inclusion hz) (inclusion_injective hz)
  rw [suzukiRootSubgroup_center_card m hm] at hc
  have hp := (frattini R).card_mul_index
  rw [index_eq_card, suzukiRootSubgroup_card m hm] at hp
  have hq : 0 < 2^(2*m+1) := by positivity
  nlinarith

theorem odd_cyclic_root_stabilizer_card_le
    {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (m : ℕ) (hm : 0 < m) (φ : A →* MulAut (SuzukiMatrixGroup m))
    (hφ : Function.Injective φ) (ho : Odd (Nat.card A))
    (hN : ∀ a, (SuzukiRootSubgroup m).map (φ a).toMonoidHom = SuzukiRootSubgroup m) :
    Nat.card A ≤ 2^(2*m+1)-1 := by
  classical
  let R := SuzukiRootSubgroup m
  let ψ : A →* MulAut R :=
    { toFun a := ((φ a).subgroupMap R).trans (MulEquiv.subgroupCongr (hN a))
      map_one' := by apply MulEquiv.ext; intro x; apply Subtype.ext; exact DFunLike.congr_fun φ.map_one (x : SuzukiMatrixGroup m)
      map_mul' a b := by apply MulEquiv.ext; intro x; apply Subtype.ext; exact DFunLike.congr_fun (φ.map_mul a b) (x : SuzukiMatrixGroup m) }
  have hψ : Function.Injective ψ := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    have hfix : ∀ x ∈ R, φ a x = x := by
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun ha (⟨x,hx⟩ : R))
    obtain ⟨P,hP⟩ := suzukiRootSubgroup_isSylow m hm
    obtain ⟨g,hg,he⟩ := suzuki_aut_fixing_sylow_inner hm (MulEquiv.refl _) P (φ a)
      (fun x hx => hfix x (by change x ∈ SuzukiRootSubgroup m; rwa [←hP]))
    have hd : orderOf (φ a) ∣ Nat.card R := by
      rw [he]
      apply (orderOf_map_dvd MulAut.conj g).trans
      simpa only [← Subgroup.orderOf_coe] using
        orderOf_dvd_natCard (⟨g,by change g ∈ SuzukiRootSubgroup m; rwa [←hP]⟩ : R)
    have hc : Nat.Coprime (Nat.card A) (Nat.card R) := by
      rw [suzukiRootSubgroup_card m hm]
      exact (ho.coprime_two_right.pow_right _).pow_right _
    have he1 : orderOf (φ a) = 1 := Nat.eq_one_of_dvd_coprimes hc
      ((orderOf_map_dvd φ a).trans (orderOf_dvd_natCard a)) hd
    exact hφ (by rw [orderOf_eq_one_iff.mp he1, map_one])
  let : Fact (IsPGroup 2 R) := ⟨suzukiRootSubgroup_isPGroup m hm⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let η := (Subgroup.quotientAut (frattini R)).comp ψ
  have hη : Function.Injective η :=
    MonoidHom.injective_frattini_action_of_coprime (suzukiRootSubgroup_isPGroup m hm)
      ψ hψ ho.coprime_two_right
  by_cases hA : Nat.card A = 1
  · rw [hA]
    have hq : 2 ≤ 2^(2*m+1) := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ 2*m+1)
      simpa using this
    omega
  obtain ⟨v,hv⟩ := Theory.GroupAction.faithful_cyclic_odd_binary_exists_free_orbit η hη ho
  have hv1 : v ≠ 1 := by
    intro he
    have hsub : Subsingleton A := ⟨fun a b => hv (by simp [he])⟩
    exact hA (Nat.card_eq_one_iff_unique.mpr ⟨hsub,inferInstance⟩)
  let f : A → {v : R ⧸ frattini R // v ≠ 1} := fun a =>
    ⟨η a v, fun h => hv1 ((η a).injective (h.trans (map_one (η a)).symm))⟩
  have hf : Function.Injective f := fun a b h => hv (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  let : Fintype (R ⧸ frattini R) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := {v : R ⧸ frattini R // v ≠ 1}),
    Fintype.card_subtype_compl,
    show Fintype.card {v : R ⧸ frattini R // v = 1} = 1 from Fintype.card_unique,
    ← Nat.card_eq_fintype_card] at hc
  exact hc.trans (Nat.sub_le_sub_right (root_frattini_quotient_card_le m hm) 1)
theorem odd_subgroup_card_lt_square (m : ℕ) (hm : 0 < m)
    (B : Subgroup (SuzukiMatrixGroup m)) (ho : Odd (Nat.card B)) :
    Nat.card B < (2^(2*m+1))^2+1 := by
  obtain ⟨U,hBU,hU⟩ := suzukiOddSubgroup_exists_torus hm B ho
  have hb := Nat.card_le_card_of_injective (inclusion hBU) (inclusion_injective hBU)
  have hq : 2 < 2^(2*m+1) := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (by omega : 2 ≤ 2*m+1)
    norm_num at hh
    omega
  have ht : 2^(m+1) ≤ 2^(2*m+1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rcases hU.card_eq hm with h | h | h
  · rw [h] at hb
    have hd := Nat.sub_le (2^(2*m+1)) 1
    nlinarith
  · rw [h] at hb
    nlinarith
  · rw [h] at hb
    have hd := Nat.sub_le (2^(2*m+1)) (2^(m+1))
    nlinarith

open scoped Pointwise in
theorem odd_permuting_root_le_borel (m : ℕ) (hm : 0 < m)
    (B : Subgroup (SuzukiMatrixGroup m)) (ho : Odd (Nat.card B))
    (hperm : (B : Set (SuzukiMatrixGroup m)) * (SuzukiRootSubgroup m : Set _) =
      (SuzukiRootSubgroup m : Set _) * (B : Set _)) : B ≤ SuzukiBorelSubgroup m := by
  have hq : 2 ≤ 2^(2*m+1) := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (by omega : 1 ≤ 2*m+1)
    simpa using hh
  have hproper : B ⊔ SuzukiRootSubgroup m ≠ ⊤ := by
    intro ht
    have hdisj : Disjoint B (SuzukiRootSubgroup m) := by
      apply disjoint_of_coprime_natCard
      rw [suzukiRootSubgroup_card m hm]
      exact (ho.coprime_two_right.pow_right _).pow_right _
    have hc := card_set_mul_mul_card_inf B (SuzukiRootSubgroup m)
    rw [hdisj.eq_bot, card_bot, mul_one,
      ← coe_sup_of_set_mul_comm _ _ hperm, ht] at hc
    change Nat.card (⊤ : Subgroup (SuzukiMatrixGroup m)) = _ at hc
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv, suzukiMatrixGroup_card m hm,
      suzukiRootSubgroup_card m hm] at hc
    have hb := odd_subgroup_card_lt_square m hm B ho
    have hqm : 1 ≤ 2^(2*m+1)-1 := by omega
    have hpos : 0 < (2^(2*m+1))^2 := by positivity
    have he : ((2^(2*m+1))^2+1)*(2^(2*m+1)-1) = Nat.card B := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        _ = ((2^(2*m+1))^2+1)*(2^(2*m+1))^2*(2^(2*m+1)-1) := by ring
        _ = _ := hc
    have hle := Nat.mul_le_mul_left ((2^(2*m+1))^2+1) hqm
    rw [mul_one,he] at hle
    omega
  intro b hb
  by_contra hn
  apply hproper
  apply top_unique
  rw [← suzukiRootSubgroup_omega_sup_zpowers_eq_top m hm b hn]
  exact sup_le ((omegaOneAmbient_le _).trans le_sup_right)
    (zpowers_le.mpr (mem_sup_left hb))


open scoped Pointwise in
theorem odd_permuting_embedded_root_normalizes
    {X : Type*} [Group X] [Finite X] (m : ℕ) (hm : 0 < m)
    (j : SuzukiMatrixGroup m →* X) (hj : Function.Injective j)
    [j.range.Normal] (S : Sylow 2 X)
    (hS : (SuzukiRootSubgroup m).map j = (S : Subgroup X))
    (B : Subgroup X) (ho : Odd (Nat.card B))
    (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) :
    B ≤ normalizer (S : Set X) := by
  let R := SuzukiRootSubgroup m
  let H := B ⊔ (S : Subgroup X)
  let K := H.comap j
  let J := H ⊓ j.range
  have hmem (r : SuzukiMatrixGroup m) (hr : r ∈ R) : j r ∈ S := by
    change j r ∈ (S : Subgroup X)
    rw [←hS]
    exact mem_map_of_mem j hr
  have hR : R ≤ K := by
    intro r hr
    exact mem_sup_right (hmem r hr)
  have hK : K = B.comap j ⊔ R := by
    apply le_antisymm
    · intro x hx
      have hx' : j x ∈ (B : Set X) * (S : Set X) :=
        (coe_sup_of_set_mul_comm B _ hperm) ▸ hx
      obtain ⟨b,hb,t,ht,he⟩ := hx'
      obtain ⟨r,hr,hrt⟩ := show t ∈ R.map j from hS.symm ▸ ht
      have hxB : x*r⁻¹ ∈ B.comap j := by
        change j (x*r⁻¹) ∈ B
        rw [map_mul, map_inv, hrt, ←he, mul_inv_cancel_right]
        exact hb
      have hh := mul_mem (mem_sup_left hxB) (mem_sup_right hr)
      simpa using hh
    · exact sup_le (comap_mono le_sup_left) hR
  have hpermR : (B.comap j : Set (SuzukiMatrixGroup m)) * (R : Set _) =
      (R : Set _) * (B.comap j : Set _) := by
    apply Set.Subset.antisymm
    · rintro x ⟨b,hb,r,hr,rfl⟩
      have ht : j b*j r ∈ (S : Set X)*(B : Set X) :=
        hperm ▸ Set.mul_mem_mul hb (hmem r hr)
      obtain ⟨t,ht,c,hc,he⟩ := ht
      obtain ⟨a,ha,hat⟩ := show t ∈ R.map j from hS.symm ▸ ht
      refine ⟨a,ha,a⁻¹*(b*r),?_,by group⟩
      change j (a⁻¹*(b*r)) ∈ B
      rw [map_mul, map_inv, map_mul, hat, ←he, inv_mul_cancel_left]
      exact hc
    · rintro x ⟨r,hr,b,hb,rfl⟩
      have ht : j r*j b ∈ (B : Set X)*(S : Set X) :=
        hperm.symm ▸ Set.mul_mem_mul (hmem r hr) hb
      obtain ⟨c,hc,t,ht,he⟩ := ht
      obtain ⟨a,ha,hat⟩ := show t ∈ R.map j from hS.symm ▸ ht
      refine ⟨(r*b)*a⁻¹,?_,a,ha,by group⟩
      change j ((r*b)*a⁻¹) ∈ B
      rw [map_mul, map_inv, map_mul, hat, ←he, mul_inv_cancel_right]
      exact hc
  have ho' : Odd (Nat.card (B.comap j)) := by
    let f : B.comap j →* B := j.restrict (fun _ hx => hx)
    exact ho.of_dvd_nat (Subgroup.card_dvd_of_injective f
      (fun a b hab => Subtype.ext (hj (congrArg Subtype.val hab))))
  have hKN : K ≤ normalizer (R : Set _) := by
    rw [hK, suzukiRootSubgroup_normalizer m hm]
    exact sup_le (odd_permuting_root_le_borel m hm _ ho' hpermR)
      (suzukiRootSubgroup_normalizer m hm ▸ R.le_normalizer)
  have hJ : K.map j = J := (map_comap_eq j H).trans (inf_comm _ _)
  have hSJ : (S : Subgroup X) ≤ J := by
    rw [←hJ, ←hS]
    exact map_mono hR
  have hJN : J ≤ normalizer (S : Set X) := by
    change J ≤ normalizer ((S : Subgroup X) : Set X)
    rw [←hJ, ←hS]
    exact (map_mono hKN).trans (le_normalizer_map j)
  let P := S.subtype hSJ
  let : (S : Subgroup X).subgroupOf J |>.Normal :=
    normal_subgroupOf_of_le_normalizer hJN
  have hPN : (P : Subgroup J).Normal := by
    simpa only [P, Sylow.coe_subtype] using (inferInstance : ((S : Subgroup X).subgroupOf J).Normal)
  let : ((S : Subgroup X).subgroupOf J).Characteristic := by
    simpa only [P, Sylow.coe_subtype] using P.characteristic_of_normal hPN
  have hBJ : B ≤ normalizer (J : Set X) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact ⟨H.mul_mem (H.mul_mem (mem_sup_left hb) hx.1) (H.inv_mem (mem_sup_left hb)),
        (inferInstance : j.range.Normal).conj_mem x hx.2 b⟩
    · intro hx
      have hh := H.mul_mem (H.mul_mem (H.inv_mem (mem_sup_left hb)) hx.1) (mem_sup_left hb)
      have hh' := (inferInstance : j.range.Normal).conj_mem _ hx.2 b⁻¹
      simp only [inv_inv] at hh'
      exact ⟨by simpa [mul_assoc] using hh, by simpa [mul_assoc] using hh'⟩
  have hn := normalizer_le_normalizer_characteristic_image J ((S : Subgroup X).subgroupOf J)
  rw [map_subgroupOf_eq_of_le hSJ] at hn
  exact hBJ.trans hn


open scoped Pointwise in
theorem automorphism_odd_cyclic_cartan_card
    (m : ℕ) (hm : 0 < m) (A : Subgroup (MulAut (SuzukiMatrixGroup m)))
    (hA : (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range ≤ A)
    (S : Sylow 2 A) (B C : Subgroup A) (hCB : C ≤ B)
    (ho : Odd (Nat.card B)) [IsCyclic C]
    (hperm : (B : Set A) * (S : Set A) = (S : Set A) * (B : Set A)) :
    Nat.card C ≤ 2^(2*m+1)-1 := by
  classical
  let Q := SuzukiMatrixGroup m
  have hcenter : center Q = ⊥ := by
    have hmodel : BenderSuzuki.IsSimpleBenderGroup Q := .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
    let := hmodel.isSimple
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hmodel.not_commutative (fun x y => by
        have hx : x ∈ center Q := by rw [h]; trivial
        exact (mem_center_iff.mp hx y).symm))
  have hconj := MulAut.conj_injective_of_center_eq_bot hcenter
  let i : Q →* A := MulAut.conj.codRestrict A (fun x => hA ⟨x,rfl⟩)
  have hi : Function.Injective i := fun x y h => hconj (congrArg Subtype.val h)
  have hiN : i.range = ((MulAut.conj : Q →* MulAut Q).range).comap A.subtype := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨x,rfl⟩
    · rintro ⟨x,hx⟩; exact ⟨x,Subtype.ext hx⟩
  let : i.range.Normal := hiN ▸ inferInstance
  have hSinner : (S : Subgroup A) ≤ i.range := by
    intro a ha
    let I := (MulAut.conj : Q →* MulAut Q).range
    let q := (QuotientGroup.mk' I).comp A.subtype
    have hodd : Odd (Nat.card (MulAut Q ⧸ I)) := suzuki_odd_outer_index m hm
    obtain ⟨k,hk⟩ := S.isPGroup' ⟨a,ha⟩
    have hk' : a^(2^k)=1 := congrArg Subtype.val hk
    have he : orderOf (q a) = 1 := Nat.eq_one_of_dvd_coprimes
      (hodd.coprime_two_right.pow_right k)
      (orderOf_dvd_natCard (q a))
      (orderOf_dvd_of_pow_eq_one (by rw [←map_pow, hk',map_one]))
    rw [hiN]
    exact (QuotientGroup.eq_one_iff (N := I) a.val).mp
      (show QuotientGroup.mk' I a.val = 1 from orderOf_eq_one_iff.mp he)
  let P := S.comapOfInjective i hi hSinner
  obtain ⟨f,hf,_⟩ := suzukiSylow_aligned_equiv hm (MulEquiv.refl Q) P
  let j := i.comp f.toMonoidHom
  have hj : Function.Injective j := hi.comp f.injective
  have hjrange : j.range = i.range := by
    rw [show j = i.comp f.toMonoidHom from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr f.surjective, ←MonoidHom.range_eq_map]
  let : j.range.Normal := hjrange ▸ inferInstance
  have hS : (SuzukiRootSubgroup m).map j = (S : Subgroup A) := by
    rw [show j = i.comp f.toMonoidHom from rfl, ←map_map, hf]
    exact map_comap_eq_self hSinner
  have hBN := odd_permuting_embedded_root_normalizes m hm j hj S hS B ho hperm
  let φ : C →* MulAut Q := (MulAut.congr f.symm).toMonoidHom.comp (A.subtype.comp C.subtype)
  have hφ : Function.Injective φ :=
    (MulAut.congr f.symm).injective.comp (A.subtype_injective.comp C.subtype_injective)
  apply odd_cyclic_root_stabilizer_card_le m hm φ hφ
    (ho.of_dvd_nat (card_dvd_of_le hCB))
  intro c
  have hle : (SuzukiRootSubgroup m).map (φ c).toMonoidHom ≤ SuzukiRootSubgroup m := by
    rintro _ ⟨r,hr,rfl⟩
    have hjr : j r ∈ S := by
      change j r ∈ (S : Subgroup A)
      rw [←hS]
      exact mem_map_of_mem j hr
    have hmem := (mem_normalizer_iff.mp (hBN (hCB c.property)) (j r)).mp hjr
    have he : j (φ c r) = (c : A) * j r * (c : A)⁻¹ := by
      apply Subtype.ext
      change MulAut.conj (f (f.symm (c.val.val (f r)))) = _
      rw [f.apply_symm_apply]
      ext x
      simp [j, i, MulAut.conj_apply, MulAut.mul_apply]
    rw [←he] at hmem
    have hmem' : j (φ c r) ∈ (SuzukiRootSubgroup m).map j := hS.symm ▸ hmem
    exact (mem_map_iff_mem hj).mp hmem'
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (φ c).injective]
end BenderSuzuki.MatrixGroups.SuzukiCartan
