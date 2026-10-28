module
public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Recognition
public import Theory.SpecificGroups.SL2.FieldCardinality
/-!
# Proper binary rank-one subgroups with large root intersections

A proper subgroup of SL₂(q) with trivial two-core has every Sylow
2-subgroup smaller than q/2 when q > 4. Dickson recognition identifies
any putative larger Sylow subgroup with the additive group of a subfield.
Its degree divides the ambient degree and is at least one less, forcing
the two fields to have the same size.

Two nontrivial intersections with distinct ambient root groups force the
intrinsic two-core to vanish. Thus a proper subgroup meeting each of two
distinct roots in at least half its elements can occur only for q ≤ 4.
This includes the binary field and retains the actual root subgroups.

Source: DGS, Groups and Graphs (1985), (10.8), printed p.161; the
rank-one subgroup calculation uses Huppert II.8.23 and II.8.26.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A proper two-core-free subgroup with a half-sized Sylow requires q ≤ 4. -/
theorem half_sylow_field_card_le_four (H : Subgroup SL(2,F)) (hc : pCore 2 H=⊥)
    (P : Sylow 2 H) (hhalf : Nat.card F≤2*Nat.card P) (hne : H≠⊤) :
    Nat.card F≤4 := by
  let : Fintype F := Fintype.ofFinite F
  by_contra hsmall
  have hP : 4≤Nat.card P := by
    obtain ⟨r,hr⟩ := P.isPGroup'.exists_card_eq
    change Nat.card P=2^r at hr
    by_cases hr2 : 2≤r
    · rw [hr]; exact (show 2^2≤2^r from Nat.pow_le_pow_right (by decide) hr2)
    · have hh : r=0 ∨ r=1 := by omega
      rcases hh with rfl|rfl <;> rw [hr] at hhalf <;> norm_num only [pow_zero, pow_one, Nat.mul_one, Nat.reduceMul] at hhalf <;> omega
  obtain ⟨n,_,hF'⟩ := FiniteField.card F 2
  have hF : Nat.card F=2^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hF'
  obtain ⟨k,hk,hkn,⟨e⟩⟩ := TwoConjugateWitness.sl_subgroup_recognition hF H hc P hP
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hPc : Nat.card P=2^k := by
    calc
      Nat.card P=Nat.card R := Nat.card_congr
        ((P:Subgroup H).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _=Nat.card (GaloisField 2 k) :=
        (Nat.card_congr (sylowEquivAdditive (GaloisField 2 k) 2 R).toEquiv).symm
      _=2^k := GaloisField.card 2 k (by omega)
  have hnk : (n:ℕ)≤k+1 := by
    rw [hF,hPc,←Nat.pow_succ'] at hhalf
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hhalf
  have hke : k=(n:ℕ) := by
    have hle := Nat.le_of_dvd n.pos hkn
    obtain ⟨j,hj⟩ := hkn
    by_cases hj1 : j≤1
    · interval_cases j <;> simp_all
    · have : 2*k≤(n:ℕ) := by rw [hj]; nlinarith
      omega
  have hcard : Nat.card H=Nat.card SL(2,F) := by
    rw [Nat.card_congr e.toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 k (by omega),hke,hF]
  exact hne (eq_top_of_card_eq H hcard)

private theorem sl_sylow_eq_of_inf_ne_bot (P Q : Sylow 2 SL(2,F))
    (hi : (P:Subgroup SL(2,F))⊓(Q:Subgroup SL(2,F))≠⊥) : P=Q := by
  let e := TwoConjugateWitness.slEquivPSL F
  let P' := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let Q' := Q.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hh : P'=Q' := Theory.PSL2.sylow_eq_of_inf_ne_bot P' Q' (by
    change (P:Subgroup SL(2,F)).map e.toMonoidHom⊓
      (Q:Subgroup SL(2,F)).map e.toMonoidHom≠⊥
    rw [←map_inf (P:Subgroup SL(2,F)) (Q:Subgroup SL(2,F)) e.toMonoidHom e.injective]
    exact fun hz => hi ((map_eq_bot_iff_of_injective _ e.injective).mp hz))
  apply Sylow.ext
  apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
  have hh' := congrArg Sylow.toSubgroup hh
  change (P:Subgroup SL(2,F)).map e.toMonoidHom=(Q:Subgroup SL(2,F)).map e.toMonoidHom at hh'
  exact hh'

/-- Two distinct half-sized root intersections force q ≤ 4 in a proper subgroup. -/
theorem half_roots_field_card_le_four (R T : Sylow 2 SL(2,F)) (hne : R≠T)
    (A B H : Subgroup SL(2,F)) (hAR : A≤R) (hBT : B≤T)
    (hAH : A≤H) (hBH : B≤H)
    (hA : Nat.card F≤2*Nat.card A) (hB : Nat.card F≤2*Nat.card B)
    (hH : H≠⊤) : Nat.card F≤4 := by
  by_contra hsmall
  have hAn : A≠⊥ := by
    intro hz
    have : Nat.card A=1 := by rw [hz]; simp
    rw [this] at hA
    omega
  have hBn : B≠⊥ := by
    intro hz
    have : Nat.card B=1 := by rw [hz]; simp
    rw [this] at hB
    omega
  have hcore : pCore 2 H=⊥ := by
    by_contra hc
    let N := (pCore 2 H).map H.subtype
    obtain ⟨U,hU⟩ := (pCore_isPGroup (p:=2) (G:=H)).map H.subtype |>.exists_le_sylow
    have hAN : A≤N := by
      have hh := isPGroup_le_twoCore_of_ne_bot H hc (A.subgroupOf H)
        ((R.isPGroup'.to_le hAR).comap_subtype)
      simpa only [map_subgroupOf_eq_of_le hAH] using map_mono (f:=H.subtype) hh
    have hBN : B≤N := by
      have hh := isPGroup_le_twoCore_of_ne_bot H hc (B.subgroupOf H)
        ((T.isPGroup'.to_le hBT).comap_subtype)
      simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f:=H.subtype) hh
    have hRU : R=U := sl_sylow_eq_of_inf_ne_bot R U
      (fun hz => hAn (le_bot_iff.mp (hz ▸ le_inf hAR (hAN.trans hU))))
    have hTU : T=U := sl_sylow_eq_of_inf_ne_bot T U
      (fun hz => hBn (le_bot_iff.mp (hz ▸ le_inf hBT (hBN.trans hU))))
    exact hne (hRU.trans hTU.symm)
  have hAp : IsPGroup 2 (A.subgroupOf H) := (R.isPGroup'.to_le hAR).comap_subtype
  obtain ⟨P,hP⟩ := hAp.exists_le_sylow
  have hcard : Nat.card A≤Nat.card P := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective _)
  exact hsmall (half_sylow_field_card_le_four H hcore P (hA.trans (Nat.mul_le_mul_left 2 hcard)) hH)
end Matrix.SpecialLinearGroup
