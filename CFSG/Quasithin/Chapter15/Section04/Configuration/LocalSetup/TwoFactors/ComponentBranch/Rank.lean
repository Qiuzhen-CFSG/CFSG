module

public import Theory.SpecificGroups.SymmetricFourSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The final rank obstruction in the component branch

An elementary two-subgroup of `S₄` lies in a dihedral Sylow subgroup of order
eight and cannot equal it, so it has order at most four. Projection therefore
bounds elementary two-subgroups of `E₄ × S₄` by order sixteen.

The two normal Klein four subgroups in `A₄ × A₄` give an elementary subgroup
of order sixteen in its two-core. A commuting fixed subgroup of order two
has trivial intersection with this centerless product. Multiplication constructs
an elementary subgroup of order thirty-two, witnessing two-rank at least five.
The two actual model identifications are consequently incompatible.

These results start after model recognition; they do not assume that the raw
mixed-factor configuration has either identification. The component-branch
assembly still has to construct both identifications and the two-core inclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the last three sentences of the component case in
15.4.18, printed p.1163.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch

private theorem elementary_symmetric_four_card_le (A : Subgroup (Equiv.Perm (Fin 4)))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨e⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  have hPc : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [DihedralGroup.card]
  have hd := card_dvd_of_le hAP
  rw [hPc] at hd
  have hne : Nat.card A ≠ 8 := by
    intro he
    have heq : A = (P : Subgroup (Equiv.Perm (Fin 4))) :=
      eq_of_le_of_card_ge hAP (by rw [he, hPc])
    have hp (x : P) : x ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : Equiv.Perm (Fin 4))
        (heq.symm ▸ (show (x : Equiv.Perm (Fin 4)) ∈ (P : Subgroup _) from x.property))
    have hr := congrArg e (hp (e.symm (DihedralGroup.r 1)))
    have hh : (DihedralGroup.r (1 : ZMod 4)) ^ 2 = 1 := by simpa using hr
    have hn : (DihedralGroup.r (1 : ZMod 4)) ^ 2 ≠ 1 := by decide
    exact hn hh
  have hcases : Nat.card A ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have ht : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [ht] at hcases
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  omega

/-- Every elementary two-subgroup of a group isomorphic to `E₄ × S₄`
has order at most sixteen. -/
theorem elementary_card_le_sixteen_of_equiv
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* (Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)))
    (A : Subgroup H) [IsElementaryAbelian 2 A] : Nat.card A ≤ 16 := by
  let f : H →* Equiv.Perm (Fin 4) := (MonoidHom.snd _ _).comp e.toMonoidHom
  let B := A.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB := elementary_symmetric_four_card_le B
  let j : A → Multiplicative (ZMod 2 × ZMod 2) × B :=
    fun a => ((e a).1, ⟨f a, mem_map.mpr ⟨a, a.property, rfl⟩⟩)
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact congrArg (fun z : Multiplicative (ZMod 2 × ZMod 2) × B => z.1) h
    · exact congrArg (fun z => (z.2 : Equiv.Perm (Fin 4))) h
  have hc := Nat.card_le_card_of_injective j hj
  rw [Nat.card_prod] at hc
  have hc4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
    norm_num
  rw [hc4] at hc
  omega

/-- Disjoint commuting elementary subgroups of orders sixteen and two
construct the rank-five witness inside the specified subgroup. -/
theorem rank_five_of_sixteen_and_central_two
    {G : Type*} [Group G] [Finite G] {T V C : Subgroup G}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 C]
    (hVT : V ≤ T) (hCT : C ≤ T) (hV : Nat.card V = 16) (hC : Nat.card C = 2)
    (hc : V ≤ centralizer (C : Set G)) (hd : Disjoint V C) :
    ∃ A : Subgroup T, IsElementaryAbelian 2 A ∧ Nat.card A = 32 ∧
      5 ≤ primeRank 2 T := by
  let : CommGroup V := { (inferInstance : Group V) with mul_comm := mul_comm' }
  let : CommGroup C := { (inferInstance : Group C) with mul_comm := mul_comm' }
  have hcomm : ∀ v : V, ∀ c : C, Commute (v : G) (c : G) :=
    fun v c => (hc v.property c c.property).symm
  let f : V × C →* T := (V.subtype.noncommCoprod C.subtype hcomm).codRestrict T
    (fun a => T.mul_mem (hVT a.1.property) (hCT a.2.property))
  have hf : Function.Injective f := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hp (a : V × C) : a ^ 2 = 1 := by
    apply Prod.ext
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) a.1
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 C) a.2
  have hn : Nat.card (V × C) = 2 ^ 5 := by rw [Nat.card_prod, hV, hC]; norm_num
  have hE : IsElementaryAbelian 2 f.range := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      obtain ⟨x, hx⟩ := a.property
      apply Subtype.ext
      change (a : T) ^ 2 = 1
      rw [← hx, ← map_pow, hp, map_one]) }
  refine ⟨f.range, hE, ?_, primeRank_ge_of_elementary_embedding hp hn f hf⟩
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hn

/-- The two Klein factors in `A₄ × A₄` lie in its two-core and give a normal
sixteen-group. Transport uses the given group isomorphism. -/
theorem exists_sixteen_le_twoCore_of_a4_product
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) :
    ∃ V : Subgroup H, IsElementaryAbelian 2 V ∧ Nat.card V = 16 ∧ V ≤ pCore 2 H := by
  let K := alternatingGroup.kleinFour (Fin 4)
  let : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour (by simp)
  let : IsMulCommutative K := IsKleinFour.isMulCommutative
  let : K.Normal := alternatingGroup.normal_kleinFour (by simp)
  let Q := K.prod K
  let : IsElementaryAbelian 2 Q := {
    toIsMulCommutative := .of_setLike_mul_comm (by
      intro a ha b hb
      exact Prod.ext
        (congrArg Subtype.val (mul_comm' (⟨a.1, ha.1⟩ : K) (⟨b.1, hb.1⟩ : K)))
        (congrArg Subtype.val (mul_comm' (⟨a.2, ha.2⟩ : K) (⟨b.2, hb.2⟩ : K))))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val (show (⟨a.val.1, a.property.1⟩ : K) ^ 2 = 1 from
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (by rw [IsKleinFour.exponent_two]) _)
      · exact congrArg Subtype.val (show (⟨a.val.2, a.property.2⟩ : K) ^ 2 = 1 from
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (by rw [IsKleinFour.exponent_two]) _)) }
  have hQ : Nat.card Q = 16 := by
    rw [Nat.card_congr (prodEquiv K K).toEquiv, Nat.card_prod]
    have hk : Nat.card K = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
    rw [hk]
  let V := Q.map e.symm.toMonoidHom
  let : V.Normal := (inferInstance : Q.Normal).map e.symm.toMonoidHom e.symm.surjective
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.symm.toMonoidHom
  refine ⟨V, inferInstance, ?_, le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩⟩
  exact (card_map_of_injective e.symm.injective).trans hQ

/-- The recognized double factor and its central fixed involution construct
an elementary subgroup of order thirty-two in `Tᵢ`. -/
theorem rank_five_of_a4_product
    {G : Type*} [Group G] [Finite G] {Tᵢ X C : Subgroup G}
    [IsElementaryAbelian 2 C]
    (e : X ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)))
    (hcore : X.pCoreIn 2 ≤ Tᵢ) (hCT : C ≤ Tᵢ)
    (hCX : C ≤ centralizer (X : Set G)) (hC : Nat.card C = 2) :
    ∃ A : Subgroup Tᵢ, IsElementaryAbelian 2 A ∧ Nat.card A = 32 ∧
      5 ≤ primeRank 2 Tᵢ := by
  obtain ⟨V, hV, hvcard, hvcore⟩ := exists_sixteen_le_twoCore_of_a4_product e
  let : IsElementaryAbelian 2 V := hV
  let W := V.map X.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  have hWX : W ≤ X := map_subtype_le V
  have hWT : W ≤ Tᵢ := (map_mono hvcore).trans hcore
  have hWcard : Nat.card W = 16 := (card_map_of_injective X.subtype_injective).trans hvcard
  have hd : Disjoint W C := by
    apply disjoint_iff_inf_le.mpr
    intro w hw
    have hz : (⟨w, hWX hw.1⟩ : X) ∈ center X := by
      rw [mem_center_iff]
      intro x
      exact Subtype.ext (hCX hw.2 x x.property)
    have hez := (centerCongr e ⟨⟨w, hWX hw.1⟩, hz⟩).property
    change e ⟨w, hWX hw.1⟩ ∈ center (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)) at hez
    have hec : center (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)) = ⊥ := by
      rw [Subgroup.center_prod, alternatingGroup.center_eq_bot (by simp)]
      exact bot_prod_bot
    rw [hec, mem_bot] at hez
    have hwone : (⟨w, hWX hw.1⟩ : X) = 1 := e.injective (hez.trans e.map_one.symm)
    exact congrArg Subtype.val hwone
  exact rank_five_of_sixteen_and_central_two hWT hCT hWcard hC
    (hWX.trans (le_centralizer_iff.mp hCX)) hd

/-- The actual model identifications make the two elementary-rank bounds
incompatible. This is the last step of the component branch, after recognition. -/
theorem false_of_a4_product_and_e4_s4
    {G : Type*} [Group G] [Finite G] {Tᵢ X C G₁ : Subgroup G}
    [IsElementaryAbelian 2 C]
    (eX : X ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)))
    (eG : G₁ ≃* (Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)))
    (hcore : X.pCoreIn 2 ≤ Tᵢ) (hCT : C ≤ Tᵢ) (hTG : Tᵢ ≤ G₁)
    (hCX : C ≤ centralizer (X : Set G)) (hC : Nat.card C = 2) : False := by
  obtain ⟨A, hA, hAc, _⟩ := rank_five_of_a4_product eX hcore hCT hCX hC
  let : IsElementaryAbelian 2 A := hA
  let f := inclusion hTG
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hc := elementary_card_le_sixteen_of_equiv eG (A.map f)
  rw [card_map_of_injective (inclusion_injective hTG), hAc] at hc
  omega

/-- `O₂(X)` lies in the mixed Sylow normalizer: it is a `T`-invariant
two-subgroup, and all of `X` normalizes the chosen direct factor. -/
theorem twoCore_le_mixed_sylow
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    {X Y₂ Tᵢ : Subgroup G}
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hXY : X ≤ normalizer (Y₂ : Set G))
    (hTᵢ : Tᵢ = (T : Subgroup G) ⊓ normalizer (Y₂ : Set G)) :
    X.pCoreIn 2 ≤ Tᵢ := by
  have hn : (T : Subgroup G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hTX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hsup := T.is_maximal'
    ((isPGroup_pCoreIn 2 X).to_sup_of_normal_left' T.isPGroup' hn) le_sup_right
  rw [hTᵢ]
  exact le_inf (sup_eq_right.mp hsup) ((pCoreIn_le 2 X).trans hXY)

/-- Commuting conjugate `A₄` factors have trivial intersection and form the
actual direct product in `X`. -/
theorem a4_product_of_commuting_conjugates
    {G : Type*} [Group G] {X Y₂ : Subgroup G} (t : G)
    (e : Y₂ ≃* alternatingGroup (Fin 4))
    (hX : X = Y₂ ⊔ Y₂.map (MulAut.conj t).toMonoidHom)
    (hc : Y₂ ≤ centralizer (Y₂.map (MulAut.conj t).toMonoidHom : Set G)) :
    Nonempty (X ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  let Y₂t := Y₂.map (MulAut.conj t).toMonoidHom
  have hd : Disjoint Y₂ Y₂t := by
    apply disjoint_iff_inf_le.mpr
    intro y hy
    have hz : (⟨y, hy.1⟩ : Y₂) ∈ center Y₂ := by
      rw [mem_center_iff]
      intro a
      exact Subtype.ext (hc a.property y hy.2).symm
    have hez := (centerCongr e ⟨⟨y, hy.1⟩, hz⟩).property
    change e ⟨y, hy.1⟩ ∈ center (alternatingGroup (Fin 4)) at hez
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
    exact congrArg Subtype.val (e.injective (hez.trans e.map_one.symm))
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting Y₂ Y₂t hd hc
  let e' : Y₂t ≃* alternatingGroup (Fin 4) :=
    ((MulAut.conj t).subgroupMap Y₂).symm.trans e
  rw [hX]
  exact ⟨f.symm.trans (e.prodCongr e')⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
