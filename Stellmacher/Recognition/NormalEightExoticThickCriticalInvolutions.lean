module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalFourThickCriticalBase
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.PGroup.RelativeNormalAbelian

/-!
# Critical involutions over a thick homocyclic candidate

The critical subgroup with prescribed center is enlarged by the square fibers
of its elements.  The enlargement is normal and its maximal normal abelian
subgroup collapses back to the candidate: an involution differs from its
abelian witness by an involution in the normal four.  Commutators of a
critical subgroup are involutions modulo its elementary central quotient, and
the homocyclic candidate supplies their square roots.

Source: Janko--Thompson, Math. Z. 113 (1970), 1.4, pp.386,395, citing
MacWilliams.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition.NormalEightExoticThickCriticalInvolutions

private theorem normal_map_of_characteristic_of_injective
    {H P : Type*} [Group H] [Group P]
    (f : H →* P) (hf : Function.Injective f) [f.range.Normal]
    (K : Subgroup H) [K.Characteristic] : (K.map f).Normal := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  refine ⟨?_⟩
  rintro _ ⟨k, hk, rfl⟩ g
  let α : MulAut H := (e.trans (MulAut.conjNormal g)).trans e.symm
  refine ⟨α k, characteristic_iff_le_comap.mp inferInstance α hk, ?_⟩
  have h := e.apply_symm_apply ((MulAut.conjNormal g) (e k))
  exact congrArg Subtype.val h

private theorem root_zmod (n : ℕ) (hn : 2 ≤ n)
    (x : Multiplicative (ZMod (2 ^ n))) (hx : x ^ 2 = 1) :
    ∃ y : Multiplicative (ZMod (2 ^ n)), y ^ 2 = x := by
  have hxx : x.toAdd + x.toAdd = 0 := by
    simpa [pow_two] using congrArg Multiplicative.toAdd hx
  have hxneg : -x.toAdd = x.toAdd := neg_eq_iff_add_eq_zero.mpr hxx
  rcases (ZMod.neg_eq_self_iff x.toAdd).mp hxneg with hz | hv
  · exact ⟨1, by simpa using congrArg Multiplicative.ofAdd hz.symm⟩
  have hn4 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = 2 + (n - 2) from by omega, pow_add]
    congr 2
    omega
  have hv' : x.toAdd.val = 2 * 2 ^ (n - 2) := by omega
  refine ⟨Multiplicative.ofAdd (2 ^ (n - 2) : ZMod (2 ^ n)), ?_⟩
  rw [pow_two]
  change (2 ^ (n - 2) : ZMod (2 ^ n)) + 2 ^ (n - 2) = x.toAdd
  rw [← two_mul, ← ZMod.natCast_zmod_val x.toAdd, hv']
  simp

private theorem square_one_mem_of_normal_thick_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (A K : Subgroup P) [A.Normal] [K.Normal] [IsMulCommutative A]
    (hWA : W ≤ A) (hAK : A ≤ K) (hAc : A ≤ centralizer (K : Set P))
    (hroots : ∀ x ∈ K, ∀ y ∈ K, ∃ a ∈ A, a ^ 2 = ⁅x,y⁆)
    (x : P) (hxK : x ∈ K) (hx : x ^ 2 = 1) : x ∈ A := by
  let H : Subgroup P :=
    { carrier := {x | x ∈ K ∧ ∃ a ∈ A, x ^ 2 = a ^ 2}
      one_mem' := ⟨K.one_mem, 1, A.one_mem, rfl⟩
      mul_mem' := by
        rintro x y ⟨hx, a, ha, hxa⟩ ⟨hy, b, hb, hyb⟩
        obtain ⟨c, hc, hcc⟩ := hroots x hx y hy
        refine ⟨K.mul_mem hx hy, a * b * c, A.mul_mem (A.mul_mem ha hb) hc, ?_⟩
        have hxy : y⁻¹ * x ^ 2 = x ^ 2 * y⁻¹ := by
          rw [hxa]
          exact hAc (A.pow_mem ha 2) _ (K.inv_mem hy)
        have hcomm : x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := by
          rw [← hcc]
          exact hAc (A.pow_mem hc 2) _ (K.mul_mem (K.pow_mem hx 2) (K.pow_mem hy 2))
        have hs : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
          symm
          calc
            x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := hcomm
            _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
              simp only [commutatorElement_def, mul_assoc]
            _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [hxy]
            _ = (x * y) ^ 2 := by simp only [pow_two]; group
        rw [hs, hxa, hyb, ← hcc]
        have hab : Commute a b := (hAc ha _ (hAK hb)).symm
        have habc : Commute (a * b) c := hAc hc _ (hAK (A.mul_mem ha hb))
        rw [habc.mul_pow, hab.mul_pow]
      inv_mem' := by
        rintro x ⟨hx, a, ha, he⟩
        exact ⟨K.inv_mem hx, a⁻¹, A.inv_mem ha, by rw [inv_pow, he, inv_pow]⟩ }
  let : H.Normal := ⟨by
    rintro x ⟨hx, a, ha, he⟩ g
    refine ⟨(inferInstance : K.Normal).conj_mem x hx g,
      g * a * g⁻¹, (inferInstance : A.Normal).conj_mem a ha g, ?_⟩
    simpa only [map_pow, MulAut.conj_apply] using congrArg (MulAut.conj g) he⟩
  have hAH : A ≤ H := fun a ha => ⟨hAK ha, a, ha, rfl⟩
  have hHK : H ≤ K := fun _ h => h.1
  obtain ⟨D, hAD, hDH, hDn, hDa, -, hself⟩ :=
    exists_ambient_normal_abelian_selfCentralizing_containing hP H A hAH
      inferInstance inferInstance
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW (hWA.trans hAD)
  have hDA : D ≤ A := by
    intro d hd
    obtain ⟨a, ha, he⟩ := (hDH hd).2
    have hcomm : Commute d a := hAc ha d (hHK (hDH hd))
    have hp : (d * a⁻¹) ^ 2 = 1 := by
      rw [hcomm.inv_right.mul_pow, inv_pow, he, mul_inv_cancel]
    have hw : d * a⁻¹ ∈ W := by
      apply hO.le
      refine ⟨⟨d * a⁻¹, D.mul_mem hd (D.inv_mem (hAD ha))⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      simpa using hp
    simpa using A.mul_mem (hWA hw) ha
  apply hDA
  apply hself
  refine ⟨⟨hxK, 1, A.one_mem, by simpa using hx⟩, ?_⟩
  intro d hd
  exact (hAc (hDA hd) x hxK).symm

/-- Every involution in a critical subgroup whose center is the candidate lies
in that candidate. -/
public theorem critical_involution_mem_candidate
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (A : Subgroup (centralizer (W : Set S))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set S)).subtype)
    (_hmax : ∀ A' : Subgroup (centralizer (W : Set S)), A'.Characteristic →
      IsMulCommutative A' → A ≤ A' → A' = A)
    (n : ℕ) (hn : 2 ≤ n)
    (e : A.map (centralizer (W : Set S)).subtype ≃*
      (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n))))
    (K : Subgroup (centralizer (W : Set S))) (hK : IsCriticalPSubgroup 2 K)
    (hKA : (center K).map K.subtype = A) :
    ∀ x : K, x ^ 2 = 1 → (x : centralizer (W : Set S)) ∈ A := by
  let C := centralizer (W : Set S)
  let D := A.map C.subtype
  let K' := K.map C.subtype
  let : C.Normal := inferInstance
  let : C.subtype.range.Normal := by simpa only [range_subtype] using (inferInstance : C.Normal)
  let : K.Characteristic := hK.characteristic
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative D := Subgroup.map_isMulCommutative (H := A) C.subtype
  let : K'.Normal := normal_map_of_characteristic_of_injective C.subtype C.subtype_injective K
  have hDA : D ≤ K' := by
    change A.map C.subtype ≤ K.map C.subtype
    rw [← hKA]
    exact map_mono (map_subtype_le (center K))
  have hcomm (x y : K') : ∃ a : D, (a : S) ^ 2 = ⁅(x : S),(y : S)⁆ := by
    obtain ⟨x0, hx0, hxeq⟩ := x.property
    obtain ⟨y0, hy0, hyeq⟩ := y.property
    have hxambient : (x : S) = (x0 : S) := hxeq.symm
    have hyambient : (y : S) = (y0 : S) := hyeq.symm
    obtain ⟨z, hz, heq⟩ := hK.commutator_le
      (commutator_mem_commutator (mem_top (x0 : C)) hy0)
    have hsqC : (⁅(x0 : C), (y0 : C)⁆ : C) ^ 2 = 1 := by
      have hh := IsElementaryAbelian.commutatorElement_sq_eq_one_of_central_quotient
        hK.quotient_elementary ⟨x0, hx0⟩ ⟨y0, hy0⟩
      change ((⁅(⟨x0, hx0⟩ : K), (⟨y0, hy0⟩ : K)⁆ : K) : C) ^ 2 = 1
      exact congrArg Subtype.val hh
    have hsq : ((⁅(x0 : C), (y0 : C)⁆ : C) : S) ^ 2 = 1 :=
      congrArg (fun q : C => (q : S)) hsqC
    have hm : ((⁅(x0 : C), (y0 : C)⁆ : C) : S) ∈ D := by
      refine ⟨K.subtype z, ?_, ?_⟩
      · have hzA : K.subtype z ∈ A := hKA ▸
          (show K.subtype z ∈ (center K).map K.subtype from ⟨z, hz, rfl⟩)
        exact hzA
      · exact congrArg Subtype.val heq
    have hroot : ∃ a : D, (a : S) ^ 2 = ((⁅(x0 : C), (y0 : C)⁆ : C) : S) := by
      have hsqD : (⟨(⁅(x0 : C), (y0 : C)⁆ : C), hm⟩ : D) ^ 2 = 1 := by
        apply Subtype.ext
        exact hsq
      have he : (e ⟨(⁅(x0 : C), (y0 : C)⁆ : C), hm⟩) ^ 2 = 1 := by
        rw [← map_pow, hsqD, e.map_one]
      obtain ⟨u, hu⟩ := root_zmod n hn
        (e ⟨(⁅(x0 : C), (y0 : C)⁆ : C), hm⟩).1 (congrArg Prod.fst he)
      obtain ⟨v, hv⟩ := root_zmod n hn
        (e ⟨(⁅(x0 : C), (y0 : C)⁆ : C), hm⟩).2 (congrArg Prod.snd he)
      refine ⟨e.symm (u, v), ?_⟩
      have hD : (e.symm (u, v) : D) ^ 2 =
          ⟨(⁅(x0 : C), (y0 : C)⁆ : C), hm⟩ := by
        apply e.injective
        rw [map_pow, e.apply_symm_apply]
        exact Prod.ext hu hv
      convert congrArg (fun q : D => (q : S)) hD using 1
      all_goals rfl
    obtain ⟨a, ha⟩ := hroot
    have hxy : ⁅(x : S), (y : S)⁆ = ⁅(x0 : S), (y0 : S)⁆ := by
      rw [hxambient, hyambient]
    exact ⟨a, ha.trans hxy.symm⟩
  have hAc : D ≤ centralizer (K' : Set S) := by
    intro d hd k hk
    obtain ⟨a, ha, hae⟩ := hd
    have haZ : a ∈ (center K).map K.subtype := hKA.symm ▸ ha
    obtain ⟨z, hz, hza⟩ := haZ
    obtain ⟨k, hk, hke⟩ := hk
    have hc := mem_center_iff.mp hz ⟨k, hk⟩
    have hcC := congrArg (fun q : K => (q : C)) hc
    have hcS := congrArg Subtype.val hcC
    rw [← hke, ← hae, ← hza]
    change C.subtype k * C.subtype (K.subtype z) =
      C.subtype (K.subtype z) * C.subtype k at hcS
    exact hcS
  intro x hx
  have hxK' : (x : S) ∈ K' := ⟨(x : C), x.property, rfl⟩
  have hxD : (x : S) ∈ D := square_one_mem_of_normal_thick_center S.isPGroup'
    hno W hW D K' hWA hDA hAc (by
      intro u hu v hv
      obtain ⟨a, ha⟩ := hcomm ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨a, a.property, by simpa only [Subtype.coe_mk] using ha⟩) (x : S) hxK' (by
        change (x : S) ^ 2 = 1
        have hh := congrArg (fun q : C => (q : S)) (congrArg Subtype.val hx)
        simpa using hh)
  obtain ⟨a, ha, heq⟩ := hxD
  have haC : (a : S) ∈ C := (a : C).property
  let aC : C := ⟨(a : S), haC⟩
  let xC : C := ⟨(x : S), (x : C).property⟩
  have hxeq : xC = (a : C) := by
    apply Subtype.ext
    exact heq.symm
  have hmem : xC ∈ A := hxeq ▸ ha
  simpa [xC] using hmem

end Stellmacher.Recognition.NormalEightExoticThickCriticalInvolutions
