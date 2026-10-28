module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointContaining
public import Theory.GroupTheory.InvertingComplementNormalizerRank
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# Cubic rank in the natural seven-core containing component

The actual smaller binary-three component complements the natural seven-core:
its kernel on the SL₂(7) quotient is both a two-group and a seven-group.
The unique involution of this complement inverts the seven-core. The
normalizer of the smaller component therefore has index dividing 49 in
any ambient group in which the containing component is normal and the
smaller component is normalized by a full Sylow two-subgroup. Its cubic
rank equals the ambient cubic rank.

Source: Aschbacher--Smith A.3.6 and the original setting of 15.3.23,
printed pp.43--45 and 1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.Section02.LocalModels

private theorem sl2_involution_unique {F : Type*} [Field F] (hF : (2 : F) ≠ 0) :
    ∃! z : SL(2,F), orderOf z = 2 := by
  refine ⟨-1,Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF,?_⟩
  intro z hz
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hd : (Matrix.SpecialLinearGroup.toGL z).det = 1 := Units.ext z.property
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
    (Matrix.SpecialLinearGroup.toGL z) (by rw [←map_pow,hz2,map_one]) hd with he | he
  · have h1 : z = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [h1] at hz
  · exact Subtype.ext (congrArg Units.val he)


/-- The normalizer of the original smaller component retains all cubic rank
in the natural E₄₉-by-SL₂(7) containing-component alternative. -/
theorem binary_three_seven_normalizer_rank
    {E : Type*} [Group E] [Finite E]
    (K B : Subgroup E) [K.Normal]
    (hBK : B ≤ K) (hgen : K.pCoreIn 7 ⊔ B = K)
    (hact : NaturalSL2Action K (pCore 7 K) 7)
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (S : Sylow 2 E) (hSB : (S : Subgroup E) ≤ normalizer (B : Set E)) :
    primeRank 3 (normalizer (B : Set E)) = primeRank 3 E := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := K.pCoreIn 7
  let : X.Normal := inferInstanceAs ((pCore 7 K).map K.subtype).Normal
  have hXK : X ≤ K := K.pCoreIn_le 7
  have hcore : X.subgroupOf K = pCore 7 K := by
    change ((pCore 7 K).map K.subtype).comap K.subtype = _
    exact comap_map_eq_self_of_injective K.subtype_injective _
  let N := pCore 7 K
  obtain ⟨F,_,_,hF,v,ρ,hρ⟩ := hact
  let q : K →* SL(2,F) := ρ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hq : q.ker = X.subgroupOf K := by
    rw [MonoidHom.ker_comp_of_injective _ _ ρ.injective,QuotientGroup.ker_mk',hcore]
  let f := q.comp (inclusion hBK)
  have hker7 : IsPGroup 7 f.ker := by
    rw [←MonoidHom.comap_ker,hq,hcore]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBK)
  let : Group.IsNilpotent f.ker := hker7.isNilpotent
  have hker2 := PerfectCoreTwoExtension.ker_isTwoGroup f
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    (disjoint_self.mp (hker2.disjoint_of_coprime hker7 (by decide)))
  have hqsurj := ρ.surjective.comp (QuotientGroup.mk'_surjective N)
  have hftop : f.range = ⊤ := by
    have htop : N ⊔ B.subgroupOf K = ⊤ := by
      rw [show N = pCore 7 K from rfl,←hcore,←subgroupOf_sup hXK hBK,hgen,subgroupOf_self]
    have hh := congrArg (map q) htop
    have hnq : N.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff,hq,hcore]
    rw [Subgroup.map_sup,hnq,bot_sup_eq,map_top_of_surjective q hqsurj] at hh
    have hr : f.range = (B.subgroupOf K).map q := by
      rw [MonoidHom.range_comp]
      congr 1
      ext c
      constructor
      · rintro ⟨b,rfl⟩; exact b.property
      · intro hc; exact ⟨⟨c,hc⟩,rfl⟩
    exact hr.trans hh
  let e : B ≃* SL(2,F) := MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp hftop⟩
  have hX7 : IsPGroup 7 X := by
    have hp : IsPGroup 7 (X.subgroupOf K) := hcore.symm ▸ pCore_isPGroup
    exact hp.of_equiv (subgroupOfEquivOfLe hXK)
  have hodd : Odd (Nat.card X) := by
    obtain ⟨n,hn⟩ := hX7.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide : Odd 7)
  have htwo : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (hF ▸ (by decide : Odd 7))
  have hthree : ¬ 3 ∣ Nat.card X := by
    obtain ⟨n,hn⟩ := hX7.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 7) (Nat.prime_three.dvd_of_dvd_pow hd)
  apply normalizer_primeRank_eq_of_unique_inverting_complement K X B hXK hBK hgen
    hodd q hq e (sl2_involution_unique htwo) ?_ S hSB 3 hthree
  intro z hz x hx
  have hez : f z = -1 := (sl2_involution_unique htwo).unique
    ((e.orderOf_eq z).trans hz) (Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two htwo)
  let xN : N := ⟨⟨x,hXK hx⟩,by
    change (⟨x,hXK hx⟩ : K) ∈ pCore 7 K
    rw [←hcore]
    exact hx⟩
  have hi := hρ (inclusion hBK z) xN
  change v _ = Multiplicative.ofAdd (Matrix.mulVec (f z).val (Multiplicative.toAdd (v xN))) at hi
  rw [hez] at hi
  have heq : (⟨_,(inferInstance : N.Normal).conj_mem xN xN.property (inclusion hBK z)⟩ : N) = xN⁻¹ := by
    apply v.injective
    rw [hi,map_inv]
    change Multiplicative.ofAdd (Matrix.mulVec (-1 : Matrix (Fin 2) (Fin 2) F) _) = _
    rw [Matrix.neg_mulVec,Matrix.one_mulVec]
    rfl
  exact congrArg (fun a : N => ((a : K) : E)) heq

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
