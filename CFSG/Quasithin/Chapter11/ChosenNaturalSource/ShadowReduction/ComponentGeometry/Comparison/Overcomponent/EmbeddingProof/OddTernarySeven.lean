module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernaryCore
public import Theory.SpecificGroups.SU3.FiveSylow
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Alternating-seven point exclusions in signed ternary containers

Both signed ternary carriers at prime five have an order-eight Sylow
member. In the linear case a concrete determinant-one matrix supplies it;
the unitary case uses the actual hyperbolic Sylow generators. Coprime
central kernels preserve it in both special and projective carriers.

Aut(A₇) is S₇, which has no order-eight element. Automorphisms of a perfect
central cover act faithfully on its central quotient, so the same obstruction
applies to 3.A₇. The original point image has trivial two-core and a faithful
full-Sylow action by OddTernaryCore. Transporting this literal action to the
point quotient excludes both alternating-seven rows on the chosen flag.
No maximality of the point component or FF assumption is used.

Source: Aschbacher--Smith 11.4.2, printed p.776, using A.3.21, pp.55--56.
The full odd ternary comparison is assembled in OddTernaryComparison.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels

private def linearFiveEight : SL(3,ZMod 5) :=
  ⟨!![0,1,0;2,0,0;0,0,2],by decide +kernel⟩

private theorem linearFiveEight_order : orderOf linearFiveEight = 8 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 8)
  · decide +kernel
  · intro p hp hd
    have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
      ((hp.dvd_of_dvd_pow (n := 3)) hd)
    subst p
    decide +kernel

private theorem sylow_has_eight_of_exists {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 A) (h : ∃ a : A, orderOf a = 8) : ∃ a : P, orderOf a = 8 := by
  obtain ⟨a,ha⟩ := h
  have hg : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers,ha]; decide)
  obtain ⟨Q,hQ⟩ := hg.exists_le_sylow
  let b : Q := ⟨a,hQ (mem_zpowers a)⟩
  refine ⟨Q.equiv P b,?_⟩
  rw [(Q.equiv P).orderOf_eq, ←Subgroup.orderOf_coe]
  exact ha

private theorem linear_five_sylow_eight {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 A) (hm : ClassicalGroup.IsPSL A 3 5 ∨ IsSL A 3 5) :
    ∃ a : P, orderOf a = 8 := by
  have hex : ∀ Q : Sylow 2 SL(3,ZMod 5), ∃ a : Q, orderOf a = 8 :=
    fun Q => sylow_has_eight_of_exists Q ⟨linearFiveEight,linearFiveEight_order⟩
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : Fintype F := Fintype.ofFinite F
    let ef : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let a := e.trans (Atlas.fieldEquivPSL 3 ef)
    let Q : Sylow 2 SL(3,ZMod 5) := default
    let R := P.mapSurjective (f := a.toMonoidHom) a.surjective
    let b := Sylow.equivOfSurjectiveCoprime (Matrix.PSL3.projection (ZMod 5))
      (Matrix.PSL3.projection_surjective _) (by
        rw [Matrix.PSL3.projection_ker]
        exact Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center _)) Q R
    let c : P ≃* R := (P : Subgroup A).equivMapOfInjective a.toMonoidHom a.injective
    obtain ⟨x,hx⟩ := hex Q
    exact ⟨c.symm (b x),by rw [c.symm.orderOf_eq,b.orderOf_eq,hx]⟩
  · let : Fintype F := Fintype.ofFinite F
    let ef : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let a := e.trans (Atlas.fieldEquivSL 3 ef)
    let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
    let b : P ≃* Q := (P : Subgroup A).equivMapOfInjective a.toMonoidHom a.injective
    obtain ⟨x,hx⟩ := hex Q
    exact ⟨b.symm x,by rw [b.symm.orderOf_eq,hx]⟩

private theorem unitary_five_sylow_eight {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 A) (hm : ClassicalGroup.IsPSU A 3 5 ∨ IsSU A 3 5) :
    ∃ a : P, orderOf a = 8 := by
  rcases hm with ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ | ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  · let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let b : P ≃* Q := (P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective
    obtain ⟨x,y,hx,_⟩ := BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow.sylow_generators J hF hconj Q
    exact ⟨b.symm x,by rw [b.symm.orderOf_eq,hx]⟩
  · let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let R : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := default
    let b := Sylow.equivOfSurjectiveCoprime J.specialToProjective J.specialToProjective_surjective
      (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker) Q R
    let c : P ≃* Q := (P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective
    obtain ⟨x,y,hx,_⟩ := BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow.sylow_generators J hF hconj R
    exact ⟨c.symm (b.symm x),by rw [c.symm.orderOf_eq,b.symm.orderOf_eq,hx]⟩

/-- Both signed ternary carriers at prime five retain an order-eight
Sylow element, including their special central covers. -/
theorem odd_ternary_five_sylow_eight {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 A) (u : Bool) (hm : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5) :
    ∃ a : P, orderOf a = 8 := by
  cases u with
  | false => exact linear_five_sylow_eight P hm
  | true => exact unitary_five_sylow_eight P hm

private theorem symmetric_seven_order_ne_eight (s : Equiv.Perm (Fin 7)) : orderOf s ≠ 8 := by
  intro h
  have hd : orderOf s ∣ 4 := by
    rw [←s.lcm_cycleType, Multiset.lcm_dvd]
    intro n hn
    have hnd : n ∣ 8 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have hn7 : n ≤ 7 := (Multiset.le_sum_of_mem hn).trans s.sum_cycleType_le
    interval_cases n <;> norm_num at hnd <;> norm_num
  norm_num [h] at hd

private theorem alternating_seven_aut_order_ne_eight
    {C : Type*} [Group C] [Group.IsPerfect C]
    (hm : IsAlternating C 7 ∨ IsAlternatingCover C 7) (a : MulAut C) : orderOf a ≠ 8 := by
  let s : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      7 (by decide) (by decide))
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hh := symmetric_seven_order_ne_eight (s.symm (MulAut.congr e a))
    rwa [s.symm.orderOf_eq,(MulAut.congr e).orderOf_eq] at hh
  · obtain ⟨_,_,⟨e⟩⟩ := hm
    have hh := symmetric_seven_order_ne_eight (s.symm (MulAut.centralQuotientAction e a))
    rwa [s.symm.orderOf_eq, orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e)] at hh

/-- The odd ternary Sylow cannot act faithfully on A₇ or its perfect
central triple cover. The contradiction is in the literal Sylow action. -/
theorem odd_ternary_five_not_faithful_alternating_seven
    {A C : Type*} [Group A] [Finite A] [Group C] [Group.IsPerfect C]
    (P : Sylow 2 A) (u : Bool) (hm : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5)
    (a : P →* MulAut C) (ha : Function.Injective a)
    (hc : IsAlternating C 7 ∨ IsAlternatingCover C 7) : False := by
  obtain ⟨x,hx⟩ := odd_ternary_five_sylow_eight P u hm
  exact alternating_seven_aut_order_ne_eight hc (a x) ((orderOf_injective a ha x).trans hx)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The original point quotient is isomorphic to its literal containing
image once that image's intrinsic two-core has been shown trivial. -/
theorem point_core_equiv_image_of_image_core {B J : Subgroup G} (hle : B ≤ J)
    (hc : pCore 2 (pointQuotientImage B J) = ⊥) :
    Nonempty ((B ⧸ pCore 2 B) ≃* pointQuotientImage B J) := by
  let C := B.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := (subgroupOfEquivOfLe hle).symm
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let d := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  exact ⟨bq.trans (d.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot))⟩

/-- On the original chosen flag a signed ternary containing quotient
excludes both alternating-seven point quotients. The actual point image,
its core, and the faithful full-Sylow action are constructed upstream. -/
theorem ofFlag_not_alternating_seven_point_in_odd_ternary
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hle : (ofFlag S f X z H).Kz ≤ J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    ¬ (IsAlternating ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) 7 ∨
      IsAlternatingCover ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) 7) := by
  obtain ⟨hp5,hc,_,P,hC,hn,hi⟩ :=
    ofFlag_odd_ternary_faithful_point_quotient S f X z H h hne hlinear h1132 e hJ hle hp ho u hm
  subst p
  obtain ⟨b⟩ := point_core_equiv_image_of_image_core hle hc
  let C := pointQuotientImage (ofFlag S f X z H).Kz J
  let d := subgroupOfEquivOfLe (show C ≤ C ⊔ (P : Subgroup _) from le_sup_left)
  let := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  let : Group.IsPerfect ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) :=
    Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  let a := (MulAut.congr b.symm).toMonoidHom.comp (C.normalizerMonoidHom.comp (inclusion hn))
  exact odd_ternary_five_not_faithful_alternating_seven P u hm a
    ((MulAut.congr b.symm).injective.comp hi)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
