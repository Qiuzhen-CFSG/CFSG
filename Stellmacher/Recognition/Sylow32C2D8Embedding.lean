module
public import Stellmacher.Recognition.MaximalC2S4Centralizer
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylow
public import Theory.SpecificGroups.CyclicTwoDihedralFourAlignment
public import Theory.GroupTheory.SymmetricFourModelCoreData

/-!
# An aligned C₂ × D₈ embedding in the order-32 Sylow branch

For a supplied Sylow two-subgroup S0 of order 32 and a maximal two-local
subgroup P isomorphic to C₂ × S₄, there is an actual C₂ × D₈ embedding in
S0. Its first-factor involution has this image as its centralizer in S0.
The canonical reflection centralizer maps to an elementary eight whose
normalizer in S0 is the same image. In the ambient group its normalizer
is the full involution centralizer, still isomorphic to C₂ × S₄.

Choose the central involution of P, a local Sylow containing it, and an
ambient Sylow with exactly that local intersection. One Sylow conjugator
moves the entire configuration into S0. The existing C₂ × D₈ Sylow
identification is adjusted by `CyclicTwoDihedralFour.exists_alignment`,
which aligns both the central nonsquare and the actual two-core of P.
Maximal two-locality identifies the ambient normalizer of this core with
P. Restricting that identity to S0 gives the desired internal normalizer.
The final witness records the same conjugator on P and on its actual
two-core; no abstract replacement of the elementary eight is used.

Source: Kurzweil–Stellmacher, The Theory of Finite Groups, Chapter 12,
initial case-(c) analysis on printed p.367. No simplicity, N₂, additional
Z condition, or classification of groups of order 32 is required.
-/

namespace Stellmacher.Recognition
open scoped Pointwise
private abbrev Model := Multiplicative (ZMod 2) × DihedralGroup 4
private abbrev C2S4 := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)
private abbrev c : Model := (Multiplicative.ofAdd 1, 1)
private abbrev b : Model := (1, DihedralGroup.sr 0)

set_option maxRecDepth 100000 in
private theorem model_center_nonsquare :
    ∀ t : C2S4, t ∈ Subgroup.center C2S4 → t ≠ 1 → ∀ x : C2S4, x ^ 2 ≠ t := by
  decide

private theorem core_eight {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (hModel : Nonempty (P ≃* C2S4)) :
    IsElementaryAbelian 2 (pCore 2 P) ∧ Nat.card (pCore 2 P) = 8 := by
  obtain ⟨hE, hcard⟩ := symmetric_four_model_twoCore_data (Or.inr hModel)
  refine ⟨hE, ?_⟩
  have hPcard : Nat.card P = 48 := by
    obtain ⟨e⟩ := hModel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rcases hcard with h | h
  · omega
  · exact h.1

private theorem centralizer_map {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set G') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa only [map_mul, e.apply_symm_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using h

/-- An actual C₂ × D₈ embedding preserving the involution and two-core of the maximal local. -/
public theorem sylow32_c2s4_embedding
    {G : Type*} [Group G] [Finite G] (S0 : Sylow 2 G)
    (hOrder : Nat.card S0 = 2 ^ 5) (P : Subgroup G) (hP : IsMaximalTwoLocal P)
    (hModel : Nonempty (P ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) :
    ∃ i : (Multiplicative (ZMod 2) × DihedralGroup 4) →* S0, Function.Injective i ∧ i.range.index = 2 ∧
      i.range = Subgroup.centralizer ({i (Multiplicative.ofAdd 1, 1)} : Set S0) ∧
      Subgroup.normalizer ((Subgroup.centralizer ({(1, DihedralGroup.sr 0)} : Set (Multiplicative (ZMod 2) × DihedralGroup 4))).map i : Set S0) = i.range ∧
      Subgroup.centralizer ({(i (Multiplicative.ofAdd 1, 1) : G)} : Set G) =
        Subgroup.normalizer (((Subgroup.centralizer ({(1, DihedralGroup.sr 0)} : Set (Multiplicative (ZMod 2) × DihedralGroup 4))).map i).map
          (S0 : Subgroup G).subtype : Set G) ∧
      Nonempty (Subgroup.centralizer ({(i (Multiplicative.ofAdd 1, 1) : G)} : Set G) ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
      ∃ g : G,
        Subgroup.centralizer ({(i (Multiplicative.ofAdd 1, 1) : G)} : Set G) = P.map (MulAut.conj g).toMonoidHom ∧
        ((Subgroup.centralizer ({(1, DihedralGroup.sr 0)} : Set (Multiplicative (ZMod 2) × DihedralGroup 4))).map i).map (S0 : Subgroup G).subtype =
          (pCore 2 P).map ((MulAut.conj g).toMonoidHom.comp P.subtype) := by
  classical
  obtain ⟨a, ha, hC⟩ := exists_involution_centralizer_of_maximal_c2s4 P hP hModel
  obtain ⟨eP⟩ := hModel
  have haP : a ∈ P := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
  let aP : P := ⟨a, haP⟩
  have haPorder : orderOf aP = 2 := (Subgroup.orderOf_coe aP).symm.trans ha
  have haPC : aP ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Subgroup.mem_centralizer_singleton_iff.mp
    change (x : G) ∈ Subgroup.centralizer ({a} : Set G)
    rw [hC]
    exact x.property
  have haPns (x : P) : x ^ 2 ≠ aP := by
    apply fun h => model_center_nonsquare (eP aP)
      (Subgroup.centerCongr eP ⟨aP, haPC⟩).property ?_ (eP x) ?_
    · intro he
      have he' : aP = 1 := eP.injective (he.trans eP.map_one.symm)
      simp [he'] at haPorder
    · simpa only [map_pow] using congrArg eP h
  have haptwo : IsPGroup 2 (Subgroup.zpowers aP) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using haPorder)
  obtain ⟨T, hT⟩ := haptwo.exists_le_sylow
  have haT : aP ∈ (T : Subgroup P) := hT (Subgroup.mem_zpowers aP)
  let aT : (T : Subgroup P) := ⟨aP, haT⟩
  obtain ⟨S, hS⟩ := T.exists_comap_subtype_eq
  have haS : a ∈ (S : Subgroup G) := by
    have h := haT
    rw [← hS] at h
    exact h
  let s : S := ⟨a, haS⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S0
  let eg : G ≃* G := MulAut.conj g
  let eS : S ≃* S0 := (S.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))
  let t : S0 := eS s
  let jS : T →* S := (P.subtype.comp (T : Subgroup P).subtype).codRestrict _ (by
    intro x
    exact (SetLike.ext_iff.mp hS (x : P)).mpr x.property)
  let j : T →* S0 := eS.toMonoidHom.comp jS
  have hj : Function.Injective j := eS.injective.comp (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : G)) h)
  have hja : j aT = t := rfl
  have hjG : (S0 : Subgroup G).subtype.comp j =
      (eg.toMonoidHom.comp P.subtype).comp (T : Subgroup P).subtype := by
    ext x
    rfl
  have htG : (t : G) = eg a := rfl
  have hCt : Subgroup.centralizer ({(t : G)} : Set G) = P.map eg.toMonoidHom := by
    rw [htG, ← centralizer_map, hC]
  have hjrange : j.range = Subgroup.centralizer ({t} : Set S0) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change eg (y.val : G) * eg a = eg a * eg (y.val : G)
      rw [← map_mul, ← map_mul]
      apply congrArg eg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp haPC y.val)
    · intro hx
      have hcomm : eS.symm x * s = s * eS.symm x := by
        apply eS.injective
        simpa only [map_mul, eS.apply_symm_apply] using
          (Subgroup.mem_centralizer_singleton_iff.mp hx)
      have hxP : (eS.symm x : G) ∈ P := by
        rw [← hC, Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hcomm
      let yP : P := ⟨eS.symm x, hxP⟩
      have hyT : yP ∈ (T : Subgroup P) := by
        rw [← hS]
        exact (eS.symm x).property
      refine ⟨⟨yP, hyT⟩, ?_⟩
      change eS (eS.symm x) = x
      exact eS.apply_symm_apply x
  have hcoreT : pCore 2 P ≤ (T : Subgroup P) := pCore_isPGroup.le_sylow_of_normal T
  let D : Subgroup T := (pCore 2 P).subgroupOf (T : Subgroup P)
  obtain ⟨hcoreE, hcorecard⟩ := core_eight P ⟨eP⟩
  let : IsElementaryAbelian 2 (pCore 2 P) := hcoreE
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hcoreT
  have hDcard : Nat.card D = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcoreT).toEquiv).trans hcorecard
  obtain ⟨eT⟩ := CyclicTwoSymmetricFour.sylow_two_equiv ⟨eP⟩ T
  let E := D.map eT.toMonoidHom
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map eT.toMonoidHom
  have hEcard : Nat.card E = 8 :=
    (Subgroup.card_map_of_injective eT.injective).trans hDcard
  have haTC : aT ∈ Subgroup.center (T : Subgroup P) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_center_iff.mp haPC x.val)
  have htmod : eT aT ∈ Subgroup.center Model :=
    (Subgroup.centerCongr eT ⟨aT, haTC⟩).property
  have htns (x : Model) : x ^ 2 ≠ eT aT := by
    intro h
    apply haPns (eT.symm x).val
    have hh : (eT.symm x) ^ 2 = aT := by
      apply eT.injective
      simpa only [map_pow, eT.apply_symm_apply] using h
    exact congrArg (fun z : T => (z : P)) hh
  obtain ⟨u, huc, huE⟩ := CyclicTwoDihedralFour.exists_alignment E hE hEcard (eT aT) htmod htns
  let k : Model ≃* T := u.trans eT.symm
  have hkc : k c = aT := by
    change eT.symm (u c) = aT
    rw [huc, eT.symm_apply_apply]
  have hkD : (Subgroup.centralizer ({b} : Set Model)).map k.toMonoidHom = D := by
    change (Subgroup.centralizer ({b} : Set Model)).map
      (eT.symm.toMonoidHom.comp u.toMonoidHom) = D
    rw [← Subgroup.map_map, huE]
    change (D.map eT.toMonoidHom).map eT.symm.toMonoidHom = D
    rw [Subgroup.map_map]
    have hid : eT.symm.toMonoidHom.comp eT.toMonoidHom = MonoidHom.id T := by ext x; simp
    rw [hid, Subgroup.map_id]
  let i := j.comp k.toMonoidHom
  have hi : Function.Injective i := hj.comp k.injective
  have hirange : i.range = j.range := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact ⟨k y, rfl⟩
    · rintro x ⟨y, rfl⟩
      exact ⟨k.symm y, congrArg j (k.apply_symm_apply y)⟩
  have hic : i c = t := by change j (k c) = t; rw [hkc, hja]
  let A := (Subgroup.centralizer ({b} : Set Model)).map i
  have hA : A = D.map j := by
    change (Subgroup.centralizer ({b} : Set Model)).map (j.comp k.toMonoidHom) = _
    rw [← Subgroup.map_map, hkD]
  have hAG : A.map (S0 : Subgroup G).subtype =
      (pCore 2 P).map (eg.toMonoidHom.comp P.subtype) := by
    rw [hA, Subgroup.map_map, hjG, ← Subgroup.map_map]
    rw [Subgroup.map_subgroupOf_eq_of_le hcoreT]
  have hNA : Subgroup.normalizer (A.map (S0 : Subgroup G).subtype : Set G) =
      P.map eg.toMonoidHom := by
    rw [hAG, ← Subgroup.map_map,
      ← Subgroup.map_equiv_normalizer_eq (f := eg)]
    rw [normalizer_twoCore_eq_of_maximal_twoLocal P hP]
  have hCcomap : (Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf
      (S0 : Subgroup G) = Subgroup.centralizer ({t} : Set S0) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact (Subtype.ext h : x * t = t * x)
    · intro h
      exact congrArg (fun z : S0 => (z : G)) h
  have hNinternal : Subgroup.normalizer (A : Set S0) = i.range := by
    have hN := Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le A)
    have hback : (A.map (S0 : Subgroup G).subtype).subgroupOf (S0 : Subgroup G) = A :=
      Subgroup.comap_map_eq_self_of_injective (S0 : Subgroup G).subtype_injective A
    rw [hback, hNA, ← hCt, hCcomap] at hN
    exact hN.symm.trans (hjrange.symm.trans hirange.symm)
  have hcard : Nat.card i.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hindex : i.range.index = 2 := by
    have h := i.range.card_mul_index
    rw [hcard, hOrder] at h
    omega
  refine ⟨i, hi, hindex, ?_, hNinternal, ?_, ?_, g, ?_, hAG⟩
  · rw [hic, hirange, hjrange]
  · rw [hic, hCt, hNA]
  · rw [hic, hCt]
    exact ⟨(eg.subgroupMap P).symm.trans eP⟩
  · rw [hic, hCt]

end Stellmacher.Recognition
