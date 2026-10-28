module
public import GorensteinWalter.PGammaL2Subgroups
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Complement

/-!
# Pure field-automorphism complements in projective semilinear subgroups

Let A be an actual subgroup of PGammaL2(K) containing the canonical PSL2
layer, over a finite field of odd prime-power order. If its field projection
has odd-order image D, then the actual pure coefficient subgroup D.inr lies
in A. Its internal copy E is a cyclic odd-order complement to the linear
kernel. The theorem retains the equality of its ambient image with D.inr,
so the complement has the prescribed coefficient action.

Adjoin PGL2 to A. The resulting relative index over A divides the PSL2/PGL2
index two, hence A is normal of index one or two in that join. Removing the
linear coordinate of each element of A puts D.inr in the join. Its odd order
then forces it into A. The coefficient projection is injective on this pure
subgroup and identifies it with D; disjointness from the kernel and the
kernel index formula give the complement. Cyclicity comes from the actual
finite-field automorphism group. No lower bound excluding field order three
is used.

This proves the pure field complement step in ABG II.3 Proposition 3,
article page 25, before lifting the decomposition through the central kernel.
-/

namespace GorensteinWalter
universe u

public theorem pGammaL2_exists_pure_field_complement
    (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K)) [Finite A]
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hodd : Odd (Nat.card (pGammaL2FieldProjection K A).range)) :
    ∃ E : Subgroup A, (pGammaL2LinearKernel K A).IsComplement' E ∧
      IsCyclic E ∧ Odd (Nat.card E) ∧
      E.map A.subtype = (pGammaL2FieldProjection K A).range.map
        (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K) := by
  let : Finite (PGL2 K) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) := Finite.of_injective
    (fun e : K ≃+* K => (e : K → K)) DFunLike.coe_injective
  let : Finite (PGammaL2 K) := Finite.of_injective
    (fun x : PGammaL2 K => (x.left, x.right)) (by
      intro x y h
      exact SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let P := pGammaL2PGLRange K
  let B := A ⊔ P
  let D := (pGammaL2FieldProjection K A).range
  let C := D.map (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K)
  let eC : D ≃* C := Subgroup.equivMapOfInjective D _ SemidirectProduct.inr_injective
  have hCodd : Odd (Nat.card C) := by
    rw [← Nat.card_congr eC.toEquiv]
    exact hodd
  have hCB : C ≤ B := by
    rintro _ ⟨σ, ⟨a, ha⟩, rfl⟩
    have hleft : (SemidirectProduct.inl (a : PGammaL2 K).left : PGammaL2 K) ∈ B :=
      (le_sup_right : P ≤ B) ⟨_, rfl⟩
    have hright := B.mul_mem (B.inv_mem hleft) ((le_sup_left : A ≤ B) a.property)
    have hdecomp := SemidirectProduct.inl_left_mul_inr_right (a : PGammaL2 K)
    have ha' : (a : PGammaL2 K).right = σ := ha
    have he : (SemidirectProduct.inl (a : PGammaL2 K).left)⁻¹ * (a : PGammaL2 K) =
        (SemidirectProduct.inr σ : PGammaL2 K) := by
      calc
        _ = (SemidirectProduct.inl (a : PGammaL2 K).left)⁻¹ *
            (SemidirectProduct.inl (a : PGammaL2 K).left *
              SemidirectProduct.inr (a : PGammaL2 K).right) :=
          congrArg (fun y : PGammaL2 K =>
            (SemidirectProduct.inl (a : PGammaL2 K).left)⁻¹ * y) hdecomp.symm
        _ = _ := by rw [inv_mul_cancel_left, ha']
    exact he ▸ hright
  have hidx : (A.subgroupOf B).index ∣ 2 := by
    have hcancel : A.relIndex B = (A ⊓ P).relIndex P := by
      have hn : P.relIndex B = (A ⊓ P).relIndex A := by
        rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_left]
      have hleft := Subgroup.relIndex_mul_relIndex (A ⊓ P) A B inf_le_left le_sup_left
      have hright := Subgroup.relIndex_mul_relIndex (A ⊓ P) P B inf_le_right le_sup_right
      rw [hn] at hright
      have hpos : 0 < (A ⊓ P).relIndex A := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      nlinarith
    change A.relIndex B ∣ 2
    rw [hcancel]
    have hle : pGammaL2PSLRange K ≤ A ⊓ P := by
      refine le_inf hPSL ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    have hd := Subgroup.relIndex_dvd_of_le_left P hle
    change (A ⊓ P).relIndex P ∣ (pGammaL2PSLRange K).relIndex (pGammaL2PGLRange K) at hd
    rwa [pGammaL2_psl_range_relIndex_pgl_eq_two K hK] at hd
  have hAN : (A.subgroupOf B).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · have htop := Subgroup.index_eq_one.mp h
      rw [htop]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  let : (A.subgroupOf B).Normal := hAN
  have hCA : C ≤ A := by
    let C' := C.subgroupOf B
    have hcard : Nat.card C' = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
    have hdivtwo : (A.subgroupOf B).relIndex C' ∣ 2 :=
      (Subgroup.relIndex_dvd_index_of_normal (H := A.subgroupOf B) (K := C')).trans hidx
    have hdivcard : (A.subgroupOf B).relIndex C' ∣ Nat.card C := by
      rw [← hcard]
      exact Subgroup.relIndex_dvd_card _ _
    have hone : (A.subgroupOf B).relIndex C' = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hCodd) hdivtwo hdivcard
    intro c hc
    exact (Subgroup.relIndex_eq_one.mp hone) (show (⟨c, hCB hc⟩ : B) ∈ C' from hc)
  let E := C.subgroupOf A
  let eE : E ≃* D := (Subgroup.subgroupOfEquivOfLe hCA).trans eC.symm
  have hEcard : Nat.card E = Nat.card D := Nat.card_congr eE.toEquiv
  let : IsCyclic (K ≃+* K) := finiteField_ringAut_isCyclic_of_oddPrimePower K hK
  have hEcyc : IsCyclic E := eE.isCyclic.mpr inferInstance
  have hdis : Disjoint (pGammaL2LinearKernel K A) E := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    rintro a ⟨haL, haE⟩
    obtain ⟨σ, _hσ, hσa⟩ := haE
    change (SemidirectProduct.inr σ : PGammaL2 K) = (a : PGammaL2 K) at hσa
    have hs : σ = 1 := by
      have h := (mem_pGammaL2LinearKernel_iff K A a).mp haL
      change SemidirectProduct.rightHom (a : PGammaL2 K) = 1 at h
      rw [← hσa, SemidirectProduct.rightHom_inr] at h
      exact h
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    rw [← hσa, hs, map_one]
    rfl
  have hcomp : (pGammaL2LinearKernel K A).IsComplement' E := by
    apply Subgroup.isComplement'_of_card_mul_and_disjoint _ hdis
    rw [hEcard, ← pGammaL2LinearKernel_index_eq_card_range K A]
    exact Subgroup.card_mul_index _
  exact ⟨E, hcomp, hEcyc, hEcard ▸ hodd, Subgroup.map_subgroupOf_eq_of_le hCA⟩

end GorensteinWalter
