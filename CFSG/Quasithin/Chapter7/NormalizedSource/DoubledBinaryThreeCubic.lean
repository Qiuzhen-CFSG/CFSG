module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCore
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.PSL3Two.DoubledCubic
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.CubicLength
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds

/-!
# The original cubic count above the doubled binary-three core

A cubic in the escaping component has fixed index sixteen on its two
identically marked natural summands. Every cubic displacement of O₂(H)
lies in that commutator core, so coprime fixed-point lifting gives the same
index on the whole O₂(H), including its possible fixed part. The original
index-seven parabolic contributes exactly one more factor on its radical Q:
positivity follows from the self-centralizing four-core of S₄, and the
literal quotient of order four supplies the upper bound.

The original natural--dual orbit W has fixed index sixteen for the same
cubic. Additivity therefore gives length one and fixed index four on the
actual quotient Q/W, with relative normality and conjugation retained.
This obtains the numerical premise used in the source's final graph
argument without requiring an identification of the whole O₂(H) with its
commutator core. The Chapter12 companion constructs all these inputs from
the chosen module and selects an actual cubic in its original local residual.

Source: Aschbacher--Smith, proof after 7.7.10, printed p.709,
refs/quasithin.pdf. Here W denotes the book's V, the full source orbit,
and is kept separate from the original chosen irreducible module.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCubic
open ChapterC.BinaryMS NoncentralChiefRefinement.CubicComparison
variable {J : Type*} [Group J] [Finite J] {κ : GroupClass} {K R : Subgroup J}

/-- Every actual cubic of the component contributes twice on the recognized
commutator core and on the whole ambient two-core. -/
theorem core_cubic_length (h : ChapterC.BinaryMS.Input κ K R)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (f : commutatorCore K ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2))
    (hf : ∀ k x i, (f (h.coreConjugate k x)).toAdd i =
      Representation.specialLinearNatural 3 (e (QuotientGroup.mk' _ k)) ((f x).toAdd i))
    (A : Subgroup J) (hA : Nat.card A = 3) (hAK : A ≤ K) :
    conjugationCubicLength A (commutatorCore K) = 2 ∧
      conjugationCubicLength A (pCore 2 J) = 2 := by
  let := h.component_normal
  let q := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hAK))
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply le_bot_iff.mp
    intro a ha
    have he : QuotientGroup.mk' (pCore 2 K) (inclusion hAK a) = 1 :=
      e.map_eq_one_iff.mp ha
    have hk : (a : J) ∈ (pCore 2 K).map K.subtype :=
      mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff _).mp he)
    have hd := hAp.disjoint_of_coprime (pCore_isPGroup.map K.subtype) (by decide : Nat.Coprime 3 2)
    exact Subtype.ext (hd.eq_bot.le ⟨a.property,hk⟩)
  let f' := f.trans (LinearEquiv.finTwoArrow (ZMod 2) (Fin 3 → ZMod 2)).toAddEquiv.toMultiplicative
  have hD : conjugationCubicLength A (commutatorCore K) = 2 := by
    apply BinaryLinearThree.doubled_natural_cubic_length A (commutatorCore K) hA
      le_normalizer_of_normal q hqi f'
    intro a x
    have hx : a • x = h.coreConjugate (inclusion hAK a) x := by
      apply Subtype.ext
      exact (h.coreConjugate_val (inclusion hAK a) x).symm
    rw [hx]
    exact Prod.ext (hf (inclusion hAK a) x 0) (hf (inclusion hAK a) x 1)
  refine ⟨hD,?_⟩
  have he := length_eq_of_commutator_le A (pCore 2 J) (commutatorCore K)
    hAp pCore_isPGroup (commutator_le_left _ _) le_normalizer_of_normal
    le_normalizer_of_normal (commutator_mono le_rfl hAK)
  exact he.symm.trans hD

variable {G : Type*} [Group G] [Finite G] {C Q : Subgroup G}

/-- Transport both cubic counts along the original component--radical inclusion. -/
theorem ambient_core_cubic_length
    (h : DoubledBinaryThreeCore.WholeCoreConclusion κ C Q)
    (A : Subgroup G) (hA : Nat.card A = 3) (hAC : A ≤ C) :
    conjugationCubicLength A (⁅(C ⊔ Q).pCoreIn 2,C⁆ : Subgroup G) = 2 ∧
      conjugationCubicLength A ((C ⊔ Q).pCoreIn 2) = 2 := by
  obtain ⟨b,_,_,_,e,f,hf⟩ := h
  let J := C ⊔ Q
  let A0 := A.subgroupOf J
  have hAJ : A ≤ J := hAC.trans le_sup_left
  have hA0 : Nat.card A0 = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have hh := core_cubic_length b e f hf A0 hA0 (subgroupOf_mono J hAC)
  have hmap : (commutatorCore (C.subgroupOf J)).map J.subtype =
      (⁅J.pCoreIn 2,C⁆ : Subgroup G) := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left)]
    rfl
  rw [←length_map_injective J.subtype J.subtype_injective A0
    (commutatorCore (C.subgroupOf J)),map_subgroupOf_eq_of_le hAJ,hmap] at hh
  rw [←length_map_injective J.subtype J.subtype_injective A0 (pCore 2 J),
    map_subgroupOf_eq_of_le hAJ] at hh
  exact hh

/-- The original index-seven base adds exactly one contribution above O₂(H). -/
theorem radical_cubic_length
    (q : G →* Matrix.PSL3Two.SL) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (P : Sylow 2 G) (B Q : Subgroup G)
    (hPB : (P : Subgroup G) ≤ B) (hB : B.index = 7)
    (hQ : B.pCoreIn 2 = Q) (hQcard : Nat.card (Q.map q) = 4)
    (A : Subgroup G) (hA : Nat.card A = 3) (hAB : A ≤ B)
    (hcore : conjugationCubicLength A (pCore 2 G) = 2) :
    conjugationCubicLength A Q = 3 := by
  have hker : IsPGroup 2 q.ker := hk ▸ pCore_isPGroup
  have hlow := Matrix.PSL3Two.index_seven_core_section_pos q hq hker P B hPB hB A hA hAB
  rw [hk,hQ] at hlow
  have hNQ : pCore 2 G ≤ Q := by
    rw [←hQ]
    exact pCore_le_map_pCore_of_prime_not_dvd_index B
      (fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPB)))
  have hAQ : A ≤ normalizer (Q : Set G) := by
    rw [←hQ]
    exact hAB.trans (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hQp : IsPGroup 2 Q := hQ ▸ isPGroup_pCoreIn 2 B
  have hc : Nat.card (Q ⧸ (pCore 2 G).subgroupOf Q) = 4 := by
    let f := q.subgroupMap Q
    have hf : f.ker = (pCore 2 G).subgroupOf Q := by rw [ker_subgroupMap,hk]
    rw [←hf,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (q.subgroupMap_surjective Q)).toEquiv]
    exact hQcard
  have hu := section_length_le_log_card A Q (pCore 2 G)
    (IsPGroup.of_card (n := 1) (by simpa using hA)) hQp hNQ hAQ le_normalizer_of_normal
  rw [hc] at hu
  simp only [sectionCubicLength,hcore,show Nat.log 4 4 = 1 from rfl] at hlow hu
  have hm := conjugationCubicLength_mono A hNQ
  omega

open Representation BinaryLinearThree

/-- The original natural--dual orbit contributes two for each cubic of L.
The full kernel is only required to be a two-group. -/
theorem orbit_cubic_length (W₀ L A : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (q : L →* BinaryLinearThree.Group)
    (hk : IsPGroup 2 q.ker) (hA : Nat.card A = 3) (hAL : A ≤ L)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (ChapterE.automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
      NaturalDual.action (q l) (E w)) : conjugationCubicLength A W₀ = 2 := by
  let : Finite (Module.Dual (ZMod 2) BinaryLinearThree.Vector) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) BinaryLinearThree.Vector =>
      (f : BinaryLinearThree.Vector → ZMod 2)) DFunLike.coe_injective
  let r := q.comp (inclusion hAL)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hri : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply le_bot_iff.mp
    intro a ha
    have hd := hAp.disjoint_of_coprime (hk.map L.subtype) (by decide : Nat.Coprime 3 2)
    exact Subtype.ext (hd.eq_bot.le ⟨a.property,mem_map_of_mem L.subtype (show inclusion hAL a ∈ q.ker from ha)⟩)
  let ρ : Representation (ZMod 2) A BinaryLinearThree.Vector := BinaryLinearThree.W.comp r
  let σ : Representation (ZMod 2) A NaturalDual.Space := ρ.prod ρ.dual
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).mp hcyc
  have hn := natural_cubic_fixedIndex hA r hri
  have hd := BinaryFixedPoints.fixedIndex_dual ρ a (fun x => ha ▸ mem_top x)
  let e : W₀ ≃* Multiplicative NaturalDual.Space := E.toAddEquiv.toMultiplicative
  let hAW := hAL.trans hLN
  let := conjMulDistribMulActionOfLeNormalizer A W₀ hAW
  have hσ (b : A) (z : NaturalDual.Space) :
      σ b z = NaturalDual.action (r b) z := by
    apply Prod.ext
    · rfl
    · change Module.Dual.transpose (ρ b⁻¹) z.2 =
        Module.Dual.transpose (BinaryLinearThree.W (r b)⁻¹) z.2
      simp only [ρ,MonoidHom.comp_apply,map_inv]
  have he := BinaryFixedPoints.cubicLength_eq_of_equivariant σ (MonoidHom.id A)
    Function.surjective_id e (by
      intro b w
      apply Multiplicative.toAdd.injective
      change E (Additive.ofMul (b • w)) = σ b (E (Additive.ofMul w))
      rw [hσ]
      exact hE (inclusion hAL b) (Additive.ofMul w))
  rw [BinaryFixedPoints.fixedIndex_prod,hd,hn] at he
  exact (conjugationCubicLength_eq A W₀ hAW).trans (he.trans (by decide))

/-- With the original orbit removed, precisely one cubic factor remains.
The last assertion is the invariant of the literal relative quotient. -/
theorem quotient_cubic_length (A W₀ Q : Subgroup G)
    (hA : Nat.card A = 3) (hQ : IsPGroup 2 Q) (hWQ : W₀ ≤ Q)
    (hAQ : A ≤ normalizer (Q : Set G)) (hAW : A ≤ normalizer (W₀ : Set G))
    [(W₀.subgroupOf Q).Normal]
    (hwhole : conjugationCubicLength A Q = 3)
    (horbit : conjugationCubicLength A W₀ = 2) :
    sectionCubicLength A W₀ Q = 1 ∧
      letI := quotientConjugationAction A Q W₀ hAQ hAW
      FixedPoints.cubicLength A (Q ⧸ W₀.subgroupOf Q) = 1 ∧
        (FixedPoints.subgroup A (Q ⧸ W₀.subgroupOf Q)).index = 4 := by
  have hs : sectionCubicLength A W₀ Q = 1 := by
    simp only [sectionCubicLength,hwhole,horbit]
  refine ⟨hs,?_⟩
  let := quotientConjugationAction A Q W₀ hAQ hAW
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hq := (sectionCubicLength_eq_quotient_of_twoGroup A Q W₀ hAp hQ hWQ hAQ hAW).symm.trans hs
  refine ⟨hq,?_⟩
  rw [FixedPoints.index_eq_four_pow_cubicLength hAp (hQ.to_quotient _),hq,pow_one]

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCubic
