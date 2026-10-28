module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.ActorProducts
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.Representation.BinaryOffender.Basic

/-!
# Elementary ranks in the explicit cover actor products

Elementary abelian subgroups of SL₃(2) have order at most four: the standard
upper triangular Sylow subgroup has order eight and contains a matrix whose
square is nonidentity. Sylow conjugacy therefore prevents an elementary
subgroup from filling a Sylow subgroup. Projection images then bound the
orders of elementary subgroups of SL₃(2) × C₂ and SL₃(2) × SL₂(2) by eight.

An order-eight elementary subgroup of SL₃(2) × C₂ contains the nonidentity
scalar kernel element, since otherwise its first projection would be injective.
The actual actor product equivalences transport these conclusions, retaining
the identification of the scalar element with the mixed projection shear.

These are structural inputs to the offender exclusions supporting
Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),(5), printed
pp.136–137, and the covering-module discussion I.1.5–6, printed p.408.
-/

public section
open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
open Matrix.PSL3Two


private lemma matrix_card_le_four (A : Subgroup MatrixGroup)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  let _ := hA
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let T : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  have hScard : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity, card_SL]
    decide +kernel
  let u : SL := ⟨!![1,1,0;0,1,1;0,0,1], by decide⟩
  have hu : u ∈ borelSL := (mem_borelSL_iff u).mpr (by decide)
  have hu2 : u ^ 2 ≠ 1 := by decide
  have hne : A ≠ (S : Subgroup SL) := by
    intro he
    let v : S := T.equiv S ⟨u, hu⟩
    have hv : (v : SL) ∈ A := he ▸ v.property
    have hv2 : v ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (v : SL) hv)
    apply hu2
    have ht : (⟨u, hu⟩ : T) ^ 2 = 1 := by
      apply (T.equiv S).injective
      simpa only [map_pow, map_one] using hv2
    exact congrArg Subtype.val ht
  have hd : Nat.card A ∣ 8 := hScard ▸ Subgroup.card_dvd_of_le hAS
  have hn : Nat.card A ≠ 8 := by
    intro he
    exact hne (Subgroup.eq_of_le_of_card_ge hAS (by omega))
  have hh := Nat.mem_divisors.mpr ⟨hd, (by decide : (8 : ℕ) ≠ 0)⟩
  have hdiv : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
  rw [hdiv] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  omega

private lemma mixing_card_le_two (A : Subgroup MixingGroup)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 2 := by
  let _ := hA
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hScard : Nat.card S = 2 := by
    rw [S.card_eq_multiplicity, mixingGroup_card]
    decide +kernel
  exact (Subgroup.card_le_of_le hAS).trans_eq hScard

private lemma product_card_le {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (A : Subgroup (G × H)) :
    Nat.card A ≤ Nat.card (A.map (MonoidHom.fst G H)) *
      Nat.card (A.map (MonoidHom.snd G H)) := by
  let B := A.map (MonoidHom.fst G H)
  let C := A.map (MonoidHom.snd G H)
  have hle : A ≤ B.prod C := fun a ha =>
    ⟨Subgroup.mem_map_of_mem _ ha, Subgroup.mem_map_of_mem _ ha⟩
  calc
    Nat.card A ≤ Nat.card (B.prod C) := Subgroup.card_le_of_le hle
    _ = Nat.card B * Nat.card C := by
      rw [Nat.card_congr (B.prodEquiv C).toEquiv, Nat.card_prod]

private lemma mixed_product_card_le (A : Subgroup (MatrixGroup × Multiplicative (ZMod 2)))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 8 := by
  let _ := hA
  have hB := matrix_card_le_four (A.map (MonoidHom.fst _ _))
    (IsElementaryAbelian.map _)
  have hC : Nat.card (A.map (MonoidHom.snd _ _)) ≤ 2 := by
    calc
      _ ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := Nat.card_zmod 2
  exact (product_card_le A).trans (Nat.mul_le_mul hB hC)

private lemma doubled_product_card_le (A : Subgroup (MatrixGroup × MixingGroup))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 8 := by
  let _ := hA
  have hB := matrix_card_le_four (A.map (MonoidHom.fst _ _))
    (IsElementaryAbelian.map _)
  have hC := mixing_card_le_two (A.map (MonoidHom.snd _ _))
    (IsElementaryAbelian.map _)
  exact (product_card_le A).trans (Nat.mul_le_mul hB hC)

private lemma mixed_product_shear (A : Subgroup (MatrixGroup × Multiplicative (ZMod 2)))
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 8) :
    (1, Multiplicative.ofAdd 1) ∈ A := by
  let _ := hA
  by_contra hs
  let f := MonoidHom.fst MatrixGroup (Multiplicative (ZMod 2))
  have hf : Function.Injective (f.subgroupMap A) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    have ha1 : a.val.1 = 1 := congrArg Subtype.val ha
    have ha2 : a.val.2 = 1 ∨ a.val.2 = Multiplicative.ofAdd 1 := by
      have h : ∀ c : Multiplicative (ZMod 2), c = 1 ∨ c = Multiplicative.ofAdd 1 := by decide
      exact h _
    rcases ha2 with ha2 | ha2
    · exact Subtype.ext (Prod.ext ha1 ha2)
    · have he : a.val = (1, Multiplicative.ofAdd 1) := Prod.ext ha1 ha2
      exact (hs (he ▸ a.property)).elim
  have hbound := matrix_card_le_four (A.map f) (IsElementaryAbelian.map f)
  have hcard := Nat.card_le_card_of_injective _ hf
  omega

/-- Every elementary abelian two-subgroup of the mixed actors has rank at most three. -/
lemma mixedActors_elementary_rank_le_three (A : Subgroup mixedActors)
    (hA : IsElementaryAbelian 2 A) : rank A ≤ 3 := by
  let _ := hA
  have hc := mixed_product_card_le (A.map mixedActorEquiv.symm.toMonoidHom)
    (IsElementaryAbelian.map _)
  rw [Subgroup.card_map_of_injective mixedActorEquiv.symm.injective] at hc
  exact Nat.log_mono_right hc

/-- Every elementary abelian two-subgroup of the doubled actors has rank at most three. -/
lemma doubledActors_elementary_rank_le_three (A : Subgroup doubledActors)
    (hA : IsElementaryAbelian 2 A) : rank A ≤ 3 := by
  let _ := hA
  have hc := doubled_product_card_le (A.map doubledActorEquiv.symm.toMonoidHom)
    (IsElementaryAbelian.map _)
  rw [Subgroup.card_map_of_injective doubledActorEquiv.symm.injective] at hc
  exact Nat.log_mono_right hc

/-- Every rank-three elementary abelian subgroup of the mixed actors contains the actual shear. -/
lemma mixedShearActor_mem_of_rank_three (A : Subgroup mixedActors)
    (hA : IsElementaryAbelian 2 A) (hr : rank A = 3) : mixedShearActor ∈ A := by
  let _ := hA
  have hcard : Nat.card A = 8 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hrn : rank A = n := by rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
    have hn3 : n = 3 := hrn.symm.trans hr
    rw [hn, hn3]
    rfl
  have hc : Nat.card (A.map mixedActorEquiv.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective mixedActorEquiv.symm.injective, hcard]
  have hs := mixed_product_shear (A.map mixedActorEquiv.symm.toMonoidHom)
    (IsElementaryAbelian.map _) hc
  obtain ⟨a, ha, he⟩ := hs
  change mixedActorEquiv.symm a = (1, Multiplicative.ofAdd 1) at he
  have he' : a = mixedShearActor := by
    simpa only [mixedActorEquiv.apply_symm_apply, mixedActorEquiv_shear] using
      congrArg mixedActorEquiv he
  exact he' ▸ ha

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
