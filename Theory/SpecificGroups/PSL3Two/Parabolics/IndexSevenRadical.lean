module

public import Theory.SpecificGroups.PSL3Two.Parabolics.OddIndex
public import Theory.SpecificGroups.SymmetricFourResidualCore
public import Theory.GroupTheory.PCoreImage

/-!
# The radical of a covered binary parabolic

Let a finite group map onto SL₃(2) with two-group kernel. An index-seven
subgroup containing a specified Sylow two-subgroup maps to a parabolic S₄.
Suppose its index-two subgroup contains the kernel, and its intersection
with the specified Sylow has index two in that Sylow. Then this intersection
is exactly the embedded two-core of the index-seven subgroup.

The four-core of S₄ lies in its two-residual, hence in the index-two
subgroup. Lift this containment and compare the two indices, both 42,
in the covering group. The source consumer constructs the index-seven
subgroup as the normalizer of the original four-plane.

Source: Aschbacher–Smith, C.1.31(MS2)(a), printed p.135, and the MS-pair
step in the proof of 12.4.6, printed p.814. The parabolic identification
uses the concrete binary parabolic lattice, independently of C.1.34.
-/

public section
open Subgroup
namespace Matrix.PSL3Two

/-- The actual two-core in a two-group cover of an index-seven parabolic. -/
theorem core_of_index_seven_cover
    {H : Type*} [Group H] [Finite H]
    (q : H →* Matrix.PSL3Two.SL) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (S : Sylow 2 H) (A C R : Subgroup H)
    (hkC : q.ker ≤ C) (hCA : C ≤ A) (hSA : (S : Subgroup H) ≤ A)
    (hA : A.index = 7) (hC : C.index = 14)
    (hR : R = (S : Subgroup H) ⊓ C) (hRi : R.relIndex (S : Subgroup H) = 2) :
    A.pCoreIn 2 = R := by
  let B := A.map q
  let K := C.map q
  have hkA : q.ker ≤ A := hkC.trans hCA
  have hBi : B.index = 7 := (A.index_map_eq hq hkA).trans hA
  have hKi : K.index = 14 := (C.index_map_eq hq hkC).trans hC
  have hBcard : Nat.card B = 24 := by
    have hh := B.index_mul_card
    rw [hBi,Matrix.PSL3Two.card_SL] at hh
    omega
  have hKB : K ≤ B := map_mono hCA
  have hKBi : K.relIndex B = 2 := by
    have hh := relIndex_mul_index hKB
    rw [hBi,hKi] at hh
    omega
  let Sbar := S.mapSurjective hq
  have hSB : (Sbar : Subgroup Matrix.PSL3Two.SL) ≤ B := map_mono hSA
  have hBne : B ≠ ⊤ := by intro he; simp only [he,index_top] at hBi; omega
  have hBtwo : ¬ IsPGroup 2 B := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hBcard] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 24)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨e,_,he⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    Matrix.PSL3Two.equiv Sbar B hSB hBne hBtwo
  let eB : B ≃* Equiv.Perm (Fin 4) :=
    ((e.subgroupMap B).trans (MulEquiv.subgroupCongr he)).trans
      Matrix.PSL3Two.MarkedAutomorphisms.lineEquivSymmetric
  have hcorecard : Nat.card (B.pCoreIn 2) = 4 := by
    rw [pCoreIn,card_map_of_injective B.subtype_injective]
    exact (Matrix.PSL3Two.ParabolicCoreModel.core_data eB).2
  have hcoreK : B.pCoreIn 2 ≤ K := by
    let : (K.subgroupOf B).Normal := normal_of_index_eq_two hKBi
    have hp : IsPGroup 2 (B ⧸ K.subgroupOf B) :=
      IsPGroup.of_card (n := 1) hKBi
    have hres : pResidual 2 B ≤ K.subgroupOf B := sInf_le ⟨inferInstance,hp⟩
    have hh := (Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv eB).trans hres
    rintro x ⟨x,hx,rfl⟩
    exact hh hx
  have hkcore : q.ker ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hk hkA (by rw [q.ker.normalizer_eq_top]; exact le_top)
  have hmapcore : (A.pCoreIn 2).map q = B.pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup q hk A
  have hcoreC : A.pCoreIn 2 ≤ C := by
    have hpre := map_le_iff_le_comap.mp (show (A.pCoreIn 2).map q ≤ C.map q by
      rw [hmapcore]
      exact hcoreK)
    simpa only [K,comap_map_eq,sup_eq_left.mpr hkC] using hpre
  have hcoreS : A.pCoreIn 2 ≤ (S : Subgroup H) := by
    have hh := pCoreIn_le_sylow A (S.subtype hSA)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSA] using hh
  have hle : A.pCoreIn 2 ≤ R := by rw [hR]; exact le_inf hcoreS hcoreC
  have hcoreindex : (A.pCoreIn 2).index = 42 := by
    have hh := (B.pCoreIn 2).index_mul_card
    rw [hcorecard,Matrix.PSL3Two.card_SL] at hh
    have hi := (A.pCoreIn 2).index_map_eq hq hkcore
    rw [hmapcore] at hi
    omega
  have hSindex : (S : Subgroup H).index = 21 := by
    have hc := Sbar.card_eq_multiplicity
    have hfac : (Nat.factorization 168) 2 = 3 := by decide +kernel
    rw [Matrix.PSL3Two.card_SL,hfac] at hc
    norm_num at hc
    have hi := (Sbar : Subgroup Matrix.PSL3Two.SL).index_mul_card
    rw [hc,Matrix.PSL3Two.card_SL] at hi
    have he := (S : Subgroup H).index_map_eq hq (hk.le_sylow_of_normal S)
    change (Sbar : Subgroup Matrix.PSL3Two.SL).index = _ at he
    omega
  have hRindex : R.index = 42 := by
    have hh := relIndex_mul_index (show R ≤ (S : Subgroup H) by rw [hR]; exact inf_le_left)
    rw [hRi,hSindex] at hh
    omega
  apply eq_of_le_of_card_ge hle
  have hc := (A.pCoreIn 2).index_mul_card
  have hr := R.index_mul_card
  rw [hcoreindex] at hc
  rw [hRindex] at hr
  omega

end Matrix.PSL3Two
