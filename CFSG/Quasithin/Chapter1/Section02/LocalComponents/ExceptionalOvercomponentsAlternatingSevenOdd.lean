module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenSection
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SevenOdd
public import GorensteinWalter.SL2UniversalCover
public import Theory.SpecificGroups.OddThreePerfectLifts
public import Theory.SpecificGroups.OddThreeRank
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution
/-!
# The actual A₇ section excludes odd containing models

An A₇ two-core quotient has three-rank at least two. Prime and quadratic
PSL₂ carriers have cyclic Sylow three-subgroups outside characteristic
three; the characteristic-three endpoints have no factor seven.
In odd prime ternary groups a nontrivial two-core yields an involution
centralizing the original perfect subgroup. Its cubic centralizer cover
embeds that subgroup faithfully in prime SL₂, contradicting three-rank.
With trivial two-core the proved intrinsic A₇ Sylow-normalizer exclusion
applies to the same subgroup. Both arguments retain the full original core.
Source: Aschbacher–Smith A.3.12(8–9), pp.47–48, and 1.2.8, pp.506–507.
-/
public noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenOdd
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings AlternatingSevenSection
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
omit [Finite K] [Group.IsPerfect K] in
private theorem five_dvd_card (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    5 ∣ Nat.card K := by
  have hc : Nat.card (K ⧸ pCore 2 K) = 2520 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact (show 5 ∣ 2520 by decide).trans (hc ▸ (pCore 2 K).card_quotient_dvd_card)

omit [Group.IsPerfect K] in
private theorem not_prime_sl2_embedding
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card F = p) (i : K →* SL(2,F)) (hi : Function.Injective i)
    (hr : 2 ≤ primeRank 3 K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hc,ZMod.card])
  let f := (GorensteinWalter.sl2RingEquiv a).toMonoidHom.comp i
  have hf : Function.Injective f := (GorensteinWalter.sl2RingEquiv a).injective.comp hi
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  have hlow : 2 ≤ primeRank 3 SL(2,ZMod p) := by
    rw [primeRank_equiv 3 e] at hr
    exact hr.trans (primeRank_subgroup_le 3 f.range)
  let P : Sylow 3 SL(2,ZMod p) := Sylow.nonempty.some
  have hcyc : IsCyclic P :=
    SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
      P.isPGroup' (by decide) (P : Subgroup SL(2,ZMod p)).subtype Subtype.val_injective
  have hb := P.primeRank_le_one_of_isCyclic hcyc
  omega

private theorem not_cubic_centralizer
    {V H F E : Type*} [Group V] [Group H] [Field F] [Field E] [Finite E]
    (ρ : V →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (f : V →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center V)
    (h3 : ∀ v ∈ f.ker, v ^ 3 = 1)
    (d : (GeneralLinearGroup.det.comp ρ).ker ≃* SL(2,E))
    (j : K →* H) (hj : Function.Injective j)
    {p : ℕ} (hp : p.Prime) (_ho : Odd p) (hE : Nat.card E = p)
    (hfive : 5 ∣ Nat.card K) (hthree : 2 ≤ primeRank 3 K) : False := by
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp
    ((by decide : 1 < 5).trans_le (Nat.le_of_dvd Nat.card_pos hfive))
  let e : K ≃* j.range := MonoidHom.ofInjective hj
  let : Group.IsPerfect j.range := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hn : ¬ IsMulCommutative V := by
    intro ha
    have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
      obtain ⟨x,rfl⟩ := hf x
      obtain ⟨y,rfl⟩ := hf y
      rw [←map_mul,←map_mul,ha.is_comm.comm x y])
    exact Group.IsPerfect.not_isMulCommutative K (IsMulCommutative.of_comm
      (fun x y => hj (by rw [map_mul,map_mul,hh.is_comm.comm])))
  let D := (GeneralLinearGroup.det.comp ρ).ker
  let a : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨Theory.SpecificGroups.OddThreeLevi.determinant_kernel_injective ρ hρ hn f hk h3,
      f.subgroupMap_surjective D⟩
  have hB : j.range ≤ D.map f :=
    Theory.SpecificGroups.OddThreeLevi.perfect_subgroup_le_det_kernel_image ρ f hf j.range
  let i := d.toMonoidHom.comp (a.symm.toMonoidHom.comp
    ((inclusion hB).comp e.toMonoidHom))
  have hi : Function.Injective i := d.injective.comp
    (a.symm.injective.comp ((inclusion_injective hB).comp e.injective))
  exact not_prime_sl2_embedding hp hE i hi hthree


private def centralizer_embedding {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G)
    (hz : B ≤ centralizer ({z} : Set G)) :
    B →* centralizer ({e z} : Set H) :=
  (e.toMonoidHom.comp B.subtype).codRestrict _ (by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      ← map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (hz b.property)))

private theorem centralizer_embedding_injective {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G) (hz : B ≤ centralizer ({z} : Set G)) :
    Function.Injective (centralizer_embedding e B z hz) := by
  intro a b h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

private theorem not_section_of_involution
    {G : Type*} [Group G] [Finite G] (B : Subgroup G) [Group.IsPerfect B]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p)
    (z : G) (hz : orderOf z = 2) (hBz : B ≤ centralizer ({z} : Set G)) :
    False := by
  have hthree : 2 ≤ primeRank 3 B := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_congr 3 eB]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have h2 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
      (k := 1) (by simpa using hF)
    obtain ⟨f,hf,hk,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection
      (e z) ((e.orderOf_eq z).trans hz) h2
    exact not_cubic_centralizer (MonoidHom.id _) Function.injective_id
      f hf hk h3 (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm
      (centralizer_embedding e B z hBz) (centralizer_embedding_injective e B z hBz)
      hp ho hF (five_dvd_card eB) hthree
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    obtain ⟨f,hf,hk,h3⟩ := SU3.OddCubicCentralizer.surjection p ho F J hF hc
      (e z) ((e.orderOf_eq z).trans hz)
    let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
    let d : J2.unitaryDet.ker ≃* SL(2,GaloisField p 1) :=
      J2.unitaryDetKernelEquiv.trans (ABG.specialUnitaryTwo_equiv_sl2 p 1 ho one_ne_zero)
    exact not_cubic_centralizer J2.unitarySubgroup.subtype Subtype.val_injective
      f hf hk h3 d (centralizer_embedding e B z hBz)
      (centralizer_embedding_injective e B z hBz) hp ho
      (by simpa using GaloisField.card p 1 one_ne_zero) (five_dvd_card eB) hthree

private theorem odd_three_rank {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) :
    primeRank 2 G ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hc


variable {G : Type*} [Group G] [Finite G]

private theorem section_threeRank {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    2 ≤ primeRank 3 B := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
    primeRank_congr 3 h.some]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

/-- Prime and quadratic PSL₂ containing fields cannot contain the actual
A₇ two-core section. No normalization hypothesis is needed for this row. -/
theorem not_odd_linear_two (B : Subgroup G)
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    {p e : ℕ} (hp : p.Prime) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL G 2 (p^e)) : False := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  by_cases he0 : e=0
  · have hc : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hF,he0,pow_zero] at hc
    omega
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  by_cases hp3 : p=3
  · have hc : Nat.card (B ⧸ pCore 2 B) = 2520 := by
      rw [Nat.card_congr h.some.toEquiv,nat_card_alternatingGroup]
      norm_num
    have hd : 7 ∣ Nat.card G := ((by decide : 7 ∣ 2520).trans
      (hc ▸ card_quotient_dvd_card (pCore 2 B))).trans B.card_subgroup_dvd_card
    rw [Nat.card_congr a.toEquiv] at hd
    have hd' : 7 ∣ Nat.card SL(2,F) := hd.trans
      (card_quotient_dvd_card (center SL(2,F)))
    rw [GorensteinWalter.sl2_card_formula,hF,hp3] at hd'
    have he' : e=1 ∨ e=2 := by omega
    rcases he' with rfl|rfl <;> norm_num at hd'
  · have hr := (section_threeRank h).trans (primeRank_subgroup_le 3 B)
    rw [primeRank_congr 3 a] at hr
    let P : Sylow 3 SL(2,F) := Sylow.nonempty.some
    have hc : IsCyclic P :=
      SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_of_ne_char
        P.isPGroup' (by decide) (Ne.symm hp3)
        (P : Subgroup SL(2,F)).subtype Subtype.val_injective
    have hb := P.primeRank_quotient_le_one hc (center SL(2,F))
    change primeRank 3 PSL(2,F) ≤ 1 at hb
    omega

/-- Full Sylow normalization excludes the A₇ section in odd prime ternary
carriers, including original subgroups with a nontrivial two-core. -/
theorem not_odd_three (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) : False := by
  let := Exceptional.local_perfect hl
  by_cases hc : pCore 2 B = ⊥
  · let a : B ≃* alternatingGroup (Fin 7) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans h.some
    rcases hm with hm|hm
    · exact (ChapterC.Section05.NormalizerControl.EmbeddingSelection.not_seven_local_odd_three
        S hn ⟨a⟩ hp ho false).1 hm
    · exact (ChapterC.Section05.NormalizerControl.EmbeddingSelection.not_seven_local_odd_three
        S hn ⟨a⟩ hp ho true).1 hm
  · obtain ⟨z,_,hz,hBz⟩ := exists_involution_centralized_by_perfect_sup_sylow
      S B (odd_three_rank hp ho hm) hn hc
    exact not_section_of_involution B h.some hp ho hm z hz (le_sup_left.trans hBz)

/-- The complete odd Theorem C row is excluded on the same original pair. -/
theorem not_odd_model (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hm : ChapterA.Section02.IsTheoremCOddModel G) : False := by
  cases hm with
  | linear_two p e hp ho he hm => exact not_odd_linear_two B h hp he hm
  | linear_three p hp ho hm => exact not_odd_three S B hl hn h hp ho (.inl hm)
  | unitary_three p hp ho hm => exact not_odd_three S B hl hn h hp ho (.inr hm)

/-- Exclude every odd containing model for the literal original local
quotient, using its transported full Sylow and local section. -/
theorem local_overcomponent_not_odd
    (T : Sylow 2 G) {X L : Subgroup G}
    (hX : X ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hL : L ∈ Chapter1.L G (T : Subgroup G)) (hXL : X ≤ L)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ ChapterA.Section02.IsTheoremCOddModel (L ⧸ pCore 2 L) := by
  obtain ⟨S,B,hl,hs,hm⟩ := local_overcomponent_pair T hX hn hL hXL h
  exact not_odd_model S B hl hs hm

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenOdd
