module
public import Theory.GroupTheory.TwoOrbitOddPrime.BinaryResidual
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.LinearModels
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Alternatives
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.ThreeDivisibility.Classical

/-!
# Residuals and centralizers of the exchanged closure

The actual inverse-conjugate product restricts to a pair inside Mc. Its binary
or PSL₃(2) quotient marking gives O^{p′}(Mc), and its two commuting centerless
factors exhaust p-rank, making their centralizer p-prime. Every transport uses
the original Mc/O₂(Mc) and the original s⁻¹. ExchangedLayer applies these facts
to the source input; the strict model comparison is still a separate obligation.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem pair_join_of_product {A B K : Subgroup G}
    (h : (K : Set G) = (A : Set G) * (B : Set G)) : K = A ⊔ B := by
  apply le_antisymm
  · intro x hx
    change x ∈ (K : Set G) at hx
    rw [h] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx
    exact (A ⊔ B).mul_mem ((show A ≤ A ⊔ B from le_sup_left) ha) ((show B ≤ A ⊔ B from le_sup_right) hb)
  · apply sup_le
    · intro a ha
      rw [show a ∈ K ↔ a ∈ (K : Set G) from Iff.rfl,h]
      exact ⟨a,ha,1,B.one_mem,mul_one a⟩
    · intro b hb
      rw [show b ∈ K ↔ b ∈ (K : Set G) from Iff.rfl,h]
      exact ⟨1,A.one_mem,b,hb,one_mul b⟩

omit [Finite G] in
private theorem exchanged_pair_in_overgroup
    {T Mc K L : Subgroup G} (hTMc : T ≤ Mc) (hLMc : L ≤ Mc)
    (hex : ∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
      (K : Set G) = (L : Set G) * (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G)) :
    K ≤ Mc ∧ ∃ t : Mc, t ∉ normalizer (L.subgroupOf Mc : Set Mc) ∧
      K.subgroupOf Mc = L.subgroupOf Mc ⊔ (L.subgroupOf Mc).conjBy t := by
  obtain ⟨s,hs,hsn,hprod⟩ := hex
  let t : Mc := ⟨s⁻¹,Mc.inv_mem (hTMc hs)⟩
  have ht : t ∉ normalizer (L.subgroupOf Mc : Set Mc) := by
    rw [←subgroupOf_normalizer_eq hLMc]
    exact fun hh => hsn (by simpa [t] using (normalizer (L : Set G)).inv_mem hh)
  have hc : ((L.subgroupOf Mc).conjBy t).map Mc.subtype =
      L.map (MulAut.conj s⁻¹).toMonoidHom := by
    change ((L.subgroupOf Mc).map (MulAut.conj t).toMonoidHom).map Mc.subtype = _
    rw [map_map]
    have he : Mc.subtype.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj s⁻¹).toMonoidHom.comp Mc.subtype := by ext; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hLMc]
  have hm : (L.subgroupOf Mc ⊔ (L.subgroupOf Mc).conjBy t).map Mc.subtype = K := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLMc,hc,←pair_join_of_product hprod]
  have hKMc : K ≤ Mc := hm ▸ map_subtype_le _
  refine ⟨hKMc,t,ht,?_⟩
  apply map_injective Mc.subtype_injective
  rw [map_subgroupOf_eq_of_le hKMc,hm]

/-- The binary exchanged product has the literal prime-to-r residual and
prime-to-r centralizer in Mc/O₂(Mc). The conjugate is by the original s⁻¹. -/
theorem exchanged_binary_closure_residual_and_centralizer
    {T Mc K L : Subgroup G} (hTMc : T ≤ Mc) (hLMc : L ≤ Mc)
    (hL : (L.subgroupOf Mc).IsCComponent)
    (hr : ∀ r : ℕ, r.Prime → Odd r → primeRank r Mc ≤ 2)
    (hex : ∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
      (K : Set G) = (L : Set G) * (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G))
    (F : Type*) [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m)
    (e : ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (r : ℕ) [Fact r.Prime] (ho : Odd r)
    (hd : r ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    K = (primeToResidual r Mc).map Mc.subtype ∧
      Nat.Coprime r (Nat.card (centralizer
        (((K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) : Set (Mc ⧸ pCore 2 Mc)))) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ)^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let A := L.subgroupOf Mc
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let B := A.map q
  let ec := (cComponentTwoCoreQuotientEquiv hL).trans e
  let : IsSimpleGroup (A ⧸ pCore 2 A) := ec.isSimpleGroup
  let : Group.IsPerfect A := hL.perfect
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : ec x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr ec ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact ec.map_eq_one_iff.mp hh
  let : IsQuasisimple (A ⧸ pCore 2 A) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  obtain ⟨hKMc,t,ht,hpair⟩ := exchanged_pair_in_overgroup hTMc hLMc hex
  have hres := TwoOrbitOddPrime.binary_cComponent_pair_eq_primeToResidual r
    (by intro he; rw [he] at ho; exact (by decide : ¬ Odd (2:ℕ)) ho)
    hL hr t ht F ec (by rwa [Nat.card_congr ec.toEquiv])
  have hresK : K = (primeToResidual r Mc).map Mc.subtype := by
    rw [←hres,←hpair,map_subgroupOf_eq_of_le hKMc]
  refine ⟨hresK,?_⟩
  have hcomm := TwoOrbitThree.quotient_pair_commutes hL t ht
  have hzB : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let et := (MulAut.conj (q t)).subgroupMap B
  have hzBt : center (B.conjBy (q t)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : et.symm x ∈ center B := ((centerCongr et).symm ⟨x,hx⟩).property
    rw [hzB,mem_bot] at hh
    exact et.symm.map_eq_one_iff.mp hh
  have hdB : r ∣ Nat.card B := by rwa [Nat.card_congr e.toEquiv]
  rw [hpair,TwoOrbitThree.pair_map_quotient]
  exact TwoOrbitOddPrime.pair_centralizer_coprime r B (B.conjBy (q t))
    hcomm hzB hzBt hdB (by
      change r ∣ Nat.card (B.map (MulAut.conj (q t)).toMonoidHom)
      rwa [card_map_of_injective (MulAut.conj (q t)).injective])
    ((primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans (hr r Fact.out ho))

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer

namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The other exchanged source row, PSL₃(2), has the same cubic residual
and three-prime centralizer on the literal ambient quotient. -/
theorem exchanged_linear_three_closure_residual_and_centralizer
    {T Mc K L : Subgroup G} (hTMc : T ≤ Mc) (hLMc : L ≤ Mc)
    (hL : (L.subgroupOf Mc).IsCComponent)
    (hr : ∀ r : ℕ, r.Prime → Odd r → primeRank r Mc ≤ 2)
    (hex : ∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
      (K : Set G) = (L : Set G) * (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G))
    (hmodel : ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2) :
    K = (primeToResidual 3 Mc).map Mc.subtype ∧
      Nat.Coprime 3 (Nat.card (centralizer
        (((K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) : Set (Mc ⧸ pCore 2 Mc)))) := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let A := L.subgroupOf Mc
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let B := A.map q
  let e : B ≃* Matrix.PSL3Two.PSL := eF.trans (Atlas.fieldEquivPSL 3 ef)
  let ec := (cComponentTwoCoreQuotientEquiv hL).trans e
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (A ⧸ pCore 2 A) := ec.isSimpleGroup
  let : Group.IsPerfect A := hL.perfect
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : ec x ∈ center Matrix.PSL3Two.PSL := (centerCongr ec ⟨x,hx⟩).property
    rw [Matrix.PSL3Two.Automorphisms.center_psl_eq_bot,mem_bot] at hh
    exact ec.map_eq_one_iff.mp hh
  let : IsQuasisimple (A ⧸ pCore 2 A) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  obtain ⟨hKMc,t,ht,hpair⟩ := exchanged_pair_in_overgroup hTMc hLMc hex
  have hi := TwoOrbitOddPrime.quasisimple_cComponent_normalizer_index_two hL hr t ht
  have hd : 3 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr ec.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card (ZMod 2) 3 (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (A ⧸ pCore 2 A))) := by
    rw [Nat.card_congr (MulAut.outerCongr (ec.trans Matrix.PSL3Two.equiv.symm)).toEquiv,
      Matrix.PSL3Two.Automorphisms.card_outer_sl]
    decide
  have hspan := TwoOrbitOddPrime.nonnormal_component_primeToResidual 3 (by decide)
    hL hi hz hd (hr 3 (by decide) (by decide)) ho
  let : (A ⊔ A.conjBy t).Normal := TwoOrbitThree.pair_normal_of_index_two A hi t ht
  have hepair : A ⊔ A.conjBy t = conjugateSpanBy A ⊤ := by
    apply le_antisymm
    · refine sup_le (le_conjugateSpanBy A ⊤) ?_
      rintro x ⟨l,hl,rfl⟩
      exact subset_closure ⟨t,mem_top t,l,hl,rfl⟩
    · apply conjugateSpanBy_le le_sup_left
      rw [normalizer_eq_top]
  have hres : K = (primeToResidual 3 Mc).map Mc.subtype := by
    rw [hspan,←hepair,←hpair,map_subgroupOf_eq_of_le hKMc]
  refine ⟨hres,?_⟩
  have hcomm := TwoOrbitThree.quotient_pair_commutes hL t ht
  have hzB : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center Matrix.PSL3Two.PSL := (centerCongr e ⟨x,hx⟩).property
    rw [Matrix.PSL3Two.Automorphisms.center_psl_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let et := (MulAut.conj (q t)).subgroupMap B
  have hzBt : center (B.conjBy (q t)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : et.symm x ∈ center B := ((centerCongr et).symm ⟨x,hx⟩).property
    rw [hzB,mem_bot] at hh
    exact et.symm.map_eq_one_iff.mp hh
  have hdB : 3 ∣ Nat.card B := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card (ZMod 2) 3 (by decide)
  rw [hpair,TwoOrbitThree.pair_map_quotient]
  exact TwoOrbitOddPrime.pair_centralizer_coprime 3 B (B.conjBy (q t)) hcomm hzB hzBt hdB
    (by
      change 3 ∣ Nat.card (B.map (MulAut.conj (q t)).toMonoidHom)
      rwa [card_map_of_injective (MulAut.conj (q t)).injective])
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (hr 3 (by decide) (by decide)))
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
