module

public import Stellmacher.SectionThree.LemmaThreeFour

/-!
# Odd cyclic rotations and an elementary `2`-actor

The first result identifies the `2`-residual of a semidirect product of a
normal odd `p`-group by a `2`-group. The second turns an elementary abelian
actor together with one reflected odd cyclic generator into the equality
`A ⊔ A^z = ⟨z⟩ ⊔ A`. These are the quotient-to-generated-subgroup
identifications used in Stellmacher (3.6), pp. 22--23.
-/

open scoped Pointwise

namespace Stellmacher.SectionThree

universe u

@[expose] public section

theorem twoResidualAmbient_sup_eq_odd_normal_subgroup
    {Q : Type u} [Group Q] [Finite Q]
    (C A : Subgroup Q)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hCp : IsPGroup p C) (hA2 : IsPGroup 2 A)
    (hAnormC : A ≤ Subgroup.normalizer (C : Set Q)) :
    twoResidualAmbient (C ⊔ A) = C := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup Q := C ⊔ A
  have hCL : C ≤ L := le_sup_left
  have hAL : A ≤ L := le_sup_right
  let CL : Subgroup L := C.subgroupOf L
  let AL : Subgroup L := A.subgroupOf L
  have hLnormC : L ≤ Subgroup.normalizer (C : Set Q) := by
    rw [show L = C ⊔ A by rfl]
    exact sup_le (Subgroup.le_normalizer (H := C)) hAnormC
  have hCLnormal : CL.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCL).2 hLnormC
  let _ : CL.Normal := hCLnormal
  have hCLp : IsPGroup p CL := hCp.comap_subtype
  have hAL2 : IsPGroup 2 AL := hA2.comap_subtype
  let qC : L →* L ⧸ CL := QuotientGroup.mk' CL
  have hmapAL : AL.map qC = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective CL x
    have hlL : (l : Q) ∈ C ⊔ A := l.property
    have hcoe : (↑(C ⊔ A) : Set Q) = (C : Set Q) * (A : Set Q) :=
      Subgroup.coe_mul_of_right_le_normalizer_left C A hAnormC
    change (l : Q) ∈ (↑(C ⊔ A) : Set Q) at hlL
    rw [hcoe] at hlL
    obtain ⟨c, hc, a, ha, hca⟩ := hlL
    let aL : L := ⟨a, hAL ha⟩
    have hcaL : l = ⟨c, hCL hc⟩ * aL := by
      apply Subtype.ext
      exact hca.symm
    have hqeq : qC l = qC aL := by
      rw [hcaL, map_mul]
      have hc1 : qC ⟨c, hCL hc⟩ = 1 :=
        (QuotientGroup.eq_one_iff (N := CL) _).2 hc
      rw [hc1, one_mul]
    rw [hqeq]
    exact Subgroup.mem_map_of_mem qC (show aL ∈ AL from ha)
  have hquot2 : IsPGroup 2 (L ⧸ CL) := by
    have himage : IsPGroup 2 (AL.map qC) := IsPGroup.map hAL2 qC
    rw [hmapAL] at himage
    exact himage.of_equiv Subgroup.topEquiv
  have hpne : p ≠ 2 := by
    rintro rfl
    obtain ⟨n, hn⟩ := hpodd
    omega
  have hres_le : twoResidualSubgroup L ≤ CL := by
    rw [twoResidualSubgroup]
    apply sInf_le
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hquot2
    refine ⟨hCLnormal, n, ?_⟩
    simpa [Subgroup.index_eq_card] using hn
  have hCL_res : CL ≤ twoResidualSubgroup L := by
    intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let _ : N.Normal := hN.1
    let qN : L →* L ⧸ N := QuotientGroup.mk' N
    have hquotN2 : IsPGroup 2 (L ⧸ N) := by
      rw [IsPGroup.iff_card]
      obtain ⟨n, hn⟩ := hN.2
      exact ⟨n, by simpa [← Subgroup.index_eq_card N] using hn⟩
    have himgp : IsPGroup p (CL.map qN) := IsPGroup.map hCLp qN
    have himg2 : IsPGroup 2 (CL.map qN) :=
      hquotN2.to_subgroup (CL.map qN)
    have hdisj : Disjoint (CL.map qN) (CL.map qN) :=
      IsPGroup.disjoint_of_ne p 2 hpne (CL.map qN) (CL.map qN) himgp himg2
    have himgbot : CL.map qN = ⊥ := disjoint_self.mp hdisj
    have hCLker : CL ≤ qN.ker :=
      (Subgroup.map_eq_bot_iff CL).mp himgbot
    have hxker : x ∈ qN.ker := hCLker hx
    simpa [qN, QuotientGroup.ker_mk'] using hxker
  have hres : twoResidualSubgroup L = CL :=
    le_antisymm hres_le hCL_res
  calc
    twoResidualAmbient L = (twoResidualSubgroup L).map L.subtype := rfl
    _ = CL.map L.subtype := by rw [hres]
    _ = C := Subgroup.map_subgroupOf_eq_of_le hCL

theorem sup_conjBy_eq_zpowers_sup_of_reflection
    {Q : Type u} [Group Q] [Finite Q]
    (A : Subgroup Q) (z a : Q)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (hzp : IsPGroup p (Subgroup.zpowers z))
    (hAelem : IsElementaryAbelian 2 A) (haA : a ∈ A)
    (hza : a * z * a⁻¹ = z⁻¹) :
    A ⊔ A.conjBy z = Subgroup.zpowers z ⊔ A := by
  classical
  let J : Subgroup Q := A ⊔ A.conjBy z
  let L : Subgroup Q := Subgroup.zpowers z ⊔ A
  have hJleL : J ≤ L := by
    apply sup_le le_sup_right
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
    change z * b * z⁻¹ ∈ L
    exact L.mul_mem
      (L.mul_mem
        ((le_sup_left : Subgroup.zpowers z ≤ L) (Subgroup.mem_zpowers z))
        ((le_sup_right : A ≤ L) hb))
      (L.inv_mem
        ((le_sup_left : Subgroup.zpowers z ≤ L) (Subgroup.mem_zpowers z)))
  have ha2 : a ^ 2 = 1 := by
    let _ : IsElementaryAbelian 2 A := hAelem
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let _ : Fact (IsPGroup 2 A) :=
      ⟨IsElementaryAbelian.isPGroup 2 A⟩
    let aA : A := ⟨a, haA⟩
    have : aA ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) aA
    exact congrArg Subtype.val this
  have hconjA : z * a * z⁻¹ ∈ A.conjBy z := by
    exact Subgroup.mem_map.mpr ⟨a, haA, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hprodJ : (z * a * z⁻¹) * a⁻¹ ∈ J :=
    J.mul_mem ((le_sup_right : A.conjBy z ≤ J) hconjA)
      (J.inv_mem ((le_sup_left : A ≤ J) haA))
  have hzinv : a * z⁻¹ * a⁻¹ = z := by
    have h := congrArg Inv.inv hza
    simpa [mul_assoc] using h
  have hzsqJ : z ^ 2 ∈ J := by
    have heq : (z * a * z⁻¹) * a⁻¹ = z ^ 2 := by
      calc
        (z * a * z⁻¹) * a⁻¹ = z * (a * z⁻¹ * a⁻¹) := by group
        _ = z * z := by rw [hzinv]
        _ = z ^ 2 := by simp [pow_two]
    rw [← heq]
    exact hprodJ
  have hzmemPow : z ∈ Subgroup.zpowers (z ^ 2) := by
    rw [mem_zpowers_pow_iff]
    obtain ⟨n, hn⟩ := hzp.exists_card_eq
    have horddiv : orderOf z ∣ p ^ n := by
      have hordSub : orderOf (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∣
          Nat.card (Subgroup.zpowers z) := orderOf_dvd_natCard _
      simpa [hn, Subgroup.orderOf_mk] using hordSub
    exact (Nat.Coprime.of_dvd_right horddiv hpodd.pow.coprime_two_left).gcd_eq_one
  have hzJ : z ∈ J :=
    (Subgroup.zpowers_le.2 hzsqJ) hzmemPow
  have hLleJ : L ≤ J := sup_le (Subgroup.zpowers_le.2 hzJ) le_sup_left
  exact le_antisymm hJleL hLleJ

end

end Stellmacher.SectionThree
