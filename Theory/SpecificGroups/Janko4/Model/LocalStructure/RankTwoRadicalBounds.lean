module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.GroupTheory.SolvableRadical.Transport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The local solvable-radical bounds required for the J₄ sieve

The Mathieu quotient of max1 kills every normal solvable image. In the full
first involution centralizer, the genuine series Q < R < H < C has factors
C₃, M₂₂ and C₂. A normal solvable subgroup therefore has order dividing
2|R|, whose three-part is three. For max4, an actual identification of its
quotient by O₂ with S₅ × SL₃(2) kills the projection to the simple second
factor; the remaining image has order dividing 120.

Only the max4 quotient identification is left as an explicit input. These
bounds concern the actual matrix-word subgroups and the full first
centralizer, not the second centralizer or an unconnected family tag.
Source: GLS3 Table 5.3i; Aschbacher--Smith, 15.3.41--42, printed p.1138.
-/

public section
open Subgroup
namespace Janko4.LocalStructure.RankTwoRadicalBounds

private theorem nonsolvable_of_simple_composite {A : Type*} [Group A]
    [IsSimpleGroup A] (hc : ¬ (Nat.card A).Prime) : ¬ Group.IsSolvable A := by
  intro hs
  let : IsMulCommutative A := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩
  let : CommGroup A := { ‹Group A› with mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr hs }
  exact hc IsSimpleGroup.prime_card

private theorem normal_solvable_eq_bot {A : Type*} [Group A] [IsSimpleGroup A]
    (ha : ¬ Group.IsSolvable A) (N : Subgroup A) [N.Normal] [Group.IsSolvable N] :
    N = ⊥ := by
  rcases (inferInstance : N.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (ha (Group.isSolvable_of_surjective
      (f := ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv).surjective)).elim

private theorem solvable_normal_le_ker {A B : Type*} [Group A] [Group B]
    [IsSimpleGroup B] (hb : ¬ Group.IsSolvable B)
    (f : A →* B) (hf : Function.Surjective f)
    (N : Subgroup A) [N.Normal] [Group.IsSolvable N] : N ≤ f.ker := by
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  let : Group.IsSolvable (N.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  exact (Subgroup.map_eq_bot_iff N).mp (normal_solvable_eq_bot hb (N.map f))

private theorem nine_dvd_image_of_two_kernel {A B : Type*} [Group A] [Group B]
    [Finite A] (f : A →* B) (hk : IsPGroup 2 f.ker) (h9 : 9 ∣ Nat.card A) :
    9 ∣ Nat.card f.range := by
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker, hk] at hc
  rw [← hc] at h9
  exact ((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_left h9

private theorem radical_card_congr {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (a : A ≃* B) :
    Nat.card (solvableRadical A) = Nat.card (solvableRadical B) := by
  rw [← map_solvableRadical_equiv a, card_map_of_injective a.injective]

/-- The actual max1 radical has no factor of nine in its order. -/
theorem max1_radical_not_nine :
    ¬ 9 ∣ Nat.card (solvableRadical
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) := by
  let A := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let K := Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let e := Janko4.LocalStructure.localQuotientEquivM24 Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let f : A →* Sporadic.Mathieu.M24 := e.toMonoidHom.comp (QuotientGroup.mk' K)
  let := Sporadic.Mathieu.m24_isSimpleGroup
  have hn : ¬ Group.IsSolvable Sporadic.Mathieu.M24 :=
    nonsolvable_of_simple_composite (by rw [Sporadic.Mathieu.m24_order]; norm_num)
  have hle := solvable_normal_le_ker hn f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (solvableRadical A)
  have hk : f.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  intro h9
  have hd := h9.trans (card_dvd_of_le (hk ▸ hle))
  rw [Janko4.Cardinality.localKernel_card] at hd
  norm_num at hd

/-- The full first involution centralizer, using its actual covering series,
has solvable radical of three-part at most three. -/
theorem firstCentralizer_radical_not_nine :
    ¬ 9 ∣ Nat.card (solvableRadical Janko4.InvolutionCentralizers.First.centralizer) := by
  let C := Janko4.InvolutionCentralizers.First.centralizer
  let N := solvableRadical C
  let H := Janko4.InvolutionCentralizers.First.QuotientExtension.H
  let R := Janko4.InvolutionCentralizers.First.QuotientExtension.R
  let Q := Janko4.InvolutionCentralizers.First.QuotientExtension.Q
  let f := Janko4.InvolutionCentralizers.First.QuotientExtension.mathieuProjection
  let := Sporadic.Mathieu.m22_isSimpleGroup
  have hn : ¬ Group.IsSolvable Sporadic.Mathieu.M22 :=
    nonsolvable_of_simple_composite (by rw [Sporadic.Mathieu.m22_order]; norm_num)
  let : Group.IsSolvable (N.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := H.subtype.subgroupComap N)
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : C)) h)))
  have hle : N.subgroupOf H ≤ R.subgroupOf H := by
    have ht := solvable_normal_le_ker hn f
      Janko4.InvolutionCentralizers.First.QuotientExtension.mathieuProjection_surjective
      (N.subgroupOf H)
    rwa [Janko4.InvolutionCentralizers.First.QuotientExtension.mathieuProjection_ker] at ht
  let g := Janko4.InvolutionCentralizers.First.QuotientExtension.centralizerOuterCharacter.comp N.subtype
  have hg : g.ker ≤ R.subgroupOf N := by
    intro x hx
    have hxH : (x : C) ∈ H := by
      change (x : C) ∈ Janko4.InvolutionCentralizers.First.QuotientExtension.H
      rw [← Janko4.InvolutionCentralizers.First.QuotientExtension.centralizerOuterCharacter_ker]
      exact hx
    exact hle (show (⟨x, hxH⟩ : H) ∈ N.subgroupOf H from x.property)
  have hker' : Nat.card g.ker ∣ Nat.card R := by
    let j : g.ker →* R :=
      (N.subtype.comp g.ker.subtype).codRestrict R (fun x => hg x.property)
    exact card_dvd_of_injective j (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : C)) h)))
  have hrange : Nat.card g.range ∣ 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using g.range.card_subgroup_dvd_card
  have hcardR : Nat.card R = 2 ^ 13 * 3 := by
    have hcount := (Q.subgroupOf R).card_mul_index
    have hcQ : Nat.card (Q.subgroupOf R) = 2 ^ 13 :=
      (Nat.card_congr (subgroupOfEquivOfLe
        Janko4.InvolutionCentralizers.First.QuotientExtension.Q_le_R).toEquiv).trans
        Janko4.InvolutionCentralizers.First.centralizer_twoCore_card
    have hi : (Q.subgroupOf R).index = 3 := by
      rw [index_eq_card, Nat.card_congr
        Janko4.InvolutionCentralizers.First.QuotientExtension.RQuotientEquivC3.toEquiv]
      simp
    rw [hcQ, hi] at hcount
    exact hcount.symm
  intro h9
  have hd : 9 ∣ Nat.card R * 2 := by
    apply h9.trans
    rw [← g.ker.card_mul_index, index_ker]
    exact Nat.mul_dvd_mul hker' hrange
  rw [hcardR] at hd
  norm_num at hd

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData in
/-- The literal ATLAS max2 subgroup has the same radical bound, through
its certified conjugation and the full centralizer-generation theorem. -/
theorem max2_radical_not_nine :
    ¬ 9 ∣ Nat.card (solvableRadical sourceSubgroup) := by
  let a : sourceSubgroup ≃* Janko4.InvolutionCentralizers.First.centralizer :=
    sourceSubgroupEquivLocal.trans
      (((MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv).trans
        Janko4.InvolutionCentralizers.First.centralizerEquiv.symm)
  have he : Nat.card (solvableRadical sourceSubgroup) =
      Nat.card (solvableRadical Janko4.InvolutionCentralizers.First.centralizer) :=
    radical_card_congr a
  rw [he]
  exact firstCentralizer_radical_not_nine

/-- Only the genuine max4 quotient isomorphism remains in this local bound. -/
theorem max4_radical_not_nine_of_quotient
    (e : (Janko4.LocalStructure.SymmetricLinear.max4Subgroup ⧸
      pCore 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup) ≃*
        Janko4.LocalStructure.SymmetricLinear.QuotientModel) :
    ¬ 9 ∣ Nat.card (solvableRadical Janko4.LocalStructure.SymmetricLinear.max4Subgroup) := by
  let A := Janko4.LocalStructure.SymmetricLinear.max4Subgroup
  let B := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let N := (solvableRadical A).map f
  let : N.Normal := (inferInstance : (solvableRadical A).Normal).map f hf
  let : Group.IsSolvable N := Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : ¬ Group.IsSolvable B :=
    nonsolvable_of_simple_composite (by rw [Atlas.Comparisons.Exceptional.sl3Two_card]; norm_num)
  have hle := solvable_normal_le_ker hn (MonoidHom.snd (Equiv.Perm (Fin 5)) B)
    (fun b => ⟨(1, b), rfl⟩) N
  let g := (MonoidHom.fst (Equiv.Perm (Fin 5)) B).comp N.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext hxy ((hle x.property).trans (hle y.property).symm)
  intro h9
  have hk : IsPGroup 2 (f.comp (solvableRadical A).subtype).ker := by
    have hker : f.ker = pCore 2 A := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    have ht : IsPGroup 2 f.ker := hker.symm ▸ pCore_isPGroup
    exact ht.comap_subtype
  have h9N : 9 ∣ Nat.card N := by
    simpa only [MonoidHom.range_comp, range_subtype] using
      nine_dvd_image_of_two_kernel (f.comp (solvableRadical A).subtype) hk h9
  have hd := h9N.trans (card_dvd_of_injective g hg)
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hd

end Janko4.LocalStructure.RankTwoRadicalBounds
