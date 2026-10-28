module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Mathlib.GroupTheory.Complement

/-!
# A prime subgroup normalizer retains the seed orbit

Let B be a p-subgroup in a subgroup C normalized by T. If p does not
divide |T| and B permutes with T, then T = (T ∩ C) N_T(B). Work in
TB: B is Sylow there, and the Frattini argument in its normal subgroup
C ∩ TB supplies the factorization. If C normalizes a seed L, removal
of T ∩ C preserves the full conjugate span of L.

This gives the prime-primary orbit consequence needed in
Aschbacher–Smith, 4.4.4–6, combined manuscript of 1 March 2004,
printed pp.619–620. No solvability or commutativity of B is needed.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

private theorem coe_sup_of_permutable (A B : Subgroup G)
    (hperm : (A : Set G) * (B : Set G) = (B : Set G) * (A : Set G)) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  rw [sup_eq_closure_mul]
  apply Set.Subset.antisymm _ subset_closure
  intro x hx
  induction hx using closure_induction'' with
  | one => exact ⟨1,A.one_mem,1,B.one_mem,mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨a,ha,b,hb,rfl⟩ := hx
    rw [mul_inv_rev, hperm]
    exact ⟨b⁻¹,B.inv_mem hb,a⁻¹,A.inv_mem ha,rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a,ha,b,hb,rfl⟩ := hx
    obtain ⟨c,hc,d,hd,rfl⟩ := hy
    obtain ⟨e,he,f,hf,hef⟩ := (show b*c ∈ (A : Set G)*(B : Set G) from
      hperm.symm ▸ Set.mul_mem_mul hb hc)
    change e*f=b*c at hef
    refine ⟨a*e,A.mul_mem ha he,f*d,B.mul_mem hf hd,?_⟩
    calc
      _ = a*(e*f)*d := by simp only [mul_assoc]
      _ = _ := by rw [hef]; simp only [mul_assoc]

variable [Finite G] {p : ℕ} [Fact p.Prime]
private theorem frattini_of_coprime_factorization (B T C : Subgroup G) [C.Normal]
    (hB : IsPGroup p B) (hT : ¬ p ∣ Nat.card T)
    (hprod : (T : Set G) * (B : Set G) = Set.univ) (hBC : B ≤ C) :
    (T : Set G) = (T ⊓ C : Subgroup G) * (T ⊓ normalizer (B : Set G) : Subgroup G) := by
  have hcop : Nat.Coprime (Nat.card T) (Nat.card B) := by
    obtain ⟨n,hn⟩ := hB.exists_card_eq
    rw [hn]
    exact (Fact.out : p.Prime).coprime_pow_of_not_dvd hT
  have hcomp := isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_of_coprime_natCard hcop) hprod
  have hp : ¬ p ∣ B.index := by rwa [hcomp.index_eq_card]
  have hgen : C ⊔ normalizer (B : Set G) = ⊤ := by
    rw [sup_comm]
    exact (hB.toSylow hp).normalizer_sup_eq_top' hBC
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨c,hc,n,hn,hcn⟩ := mem_sup_of_normal_left.mp
      (show t ∈ C ⊔ normalizer (B : Set G) from hgen.symm ▸ mem_top t)
    obtain ⟨s,hs,b,hb,hsb⟩ := (show c ∈ (T : Set G)*(B : Set G) from hprod.symm ▸ Set.mem_univ c)
    change s*b=c at hsb
    have hsC : s ∈ C := by
      have he : s = c*b⁻¹ := by rw [← hsb]; simp
      rw [he]
      exact C.mul_mem hc (C.inv_mem (hBC hb))
    have hbnT : b*n ∈ T := by
      have he : b*n = s⁻¹*t := by rw [← hcn, ← hsb]; simp only [mul_assoc,inv_mul_cancel_left]
      rw [he]
      exact T.mul_mem (T.inv_mem hs) ht
    exact ⟨s,⟨hs,hsC⟩,b*n,⟨hbnT,(normalizer (B:Set G)).mul_mem
      (B.le_normalizer hb) hn⟩,by change s*(b*n)=t; rw [← mul_assoc,hsb,hcn]⟩
  · rintro _ ⟨s,hs,n,hn,rfl⟩
    exact T.mul_mem hs.1 hn.1

omit [Finite G] in
private theorem span_of_kernel_factorization (L T S C : Subgroup G)
    (hTC : T ≤ normalizer (C : Set G)) (hCL : C ≤ normalizer (L : Set G))
    (hTS : (T : Set G) = (T ⊓ C : Subgroup G) * (S : Set G))
    (hST : S ≤ T) : conjugateSpanBy L T = conjugateSpanBy L S := by
  apply le_antisymm _ (conjugateSpanBy_mono le_rfl hST)
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro t
  obtain ⟨c,hc,s,hs,hcs⟩ := hTS.subset t.property
  have hd : s⁻¹*c*s ∈ C := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp (hTC (T.inv_mem (hST hs))) c).mp hc.2
  have he : L.map (MulAut.conj (t : G)).toMonoidHom =
      L.map (MulAut.conj s).toMonoidHom := by
    calc
      _ = (L.map (MulAut.conj (s⁻¹*c*s)).toMonoidHom).map
          (MulAut.conj s).toMonoidHom := by
        rw [map_map]
        congr 1
        ext x
        simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
        rw [← hcs]
        group
      _ = _ := by
        have hf : L.map (MulAut.conj (s⁻¹*c*s)).toMonoidHom = L :=
          mem_normalizer_iff_map_conj_eq.mp (hCL hd)
        rw [hf]
  rw [he]
  rw [conjugateSpanBy_eq_iSup_conj]
  exact le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨s,hs⟩

/-- A prime subgroup in an invariant kernel has a normalizer supplement
inside any coprime subgroup with which it permutes. -/
theorem pSubgroup_normalizer_supplement_of_permutable (B T C : Subgroup G)
    (hB : IsPGroup p B) (hT : ¬ p ∣ Nat.card T)
    (hperm : (T : Set G)*(B : Set G) = (B : Set G)*(T : Set G))
    (hBC : B ≤ C) (hTC : T ≤ normalizer (C : Set G)) :
    (T : Set G) = (T ⊓ C : Subgroup G) * (T ⊓ normalizer (B : Set G) : Subgroup G) := by
  let J := T ⊔ B
  have hTJ : T ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  let T' := T.subgroupOf J
  let B' := B.subgroupOf J
  let C' := C.subgroupOf J
  let : C'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le hTC (hBC.trans C.le_normalizer))
  have hB' : IsPGroup p B' := hB.comap_subtype
  have hT' : ¬ p ∣ Nat.card T' := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv]
  have hprod : (T' : Set J)*(B' : Set J) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro j
    obtain ⟨t,ht,b,hb,he⟩ := (coe_sup_of_permutable T B hperm).subset j.property
    exact ⟨⟨t,hTJ ht⟩,ht,⟨b,hBJ hb⟩,hb,Subtype.ext he⟩
  have hfactor := frattini_of_coprime_factorization B' T' C' hB' hT' hprod (comap_mono hBC)
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨c,hc,n,hn,he⟩ := hfactor.subset (show (⟨t,hTJ ht⟩ : J) ∈ T' from ht)
    have hnB : (n : G) ∈ normalizer (B : Set G) := by
      have hh := hn.2
      change n ∈ normalizer (B.subgroupOf J : Set J) at hh
      rw [← subgroupOf_normalizer_eq hBJ] at hh
      exact hh
    exact ⟨c,⟨hc.1,hc.2⟩,n,⟨hn.1,hnB⟩,congrArg Subtype.val he⟩
  · rintro _ ⟨c,hc,n,hn,rfl⟩
    exact T.mul_mem hc.1 hn.1

/-- Removing the invariant kernel preserves the actual seed orbit. -/
theorem conjugateSpanBy_inf_normalizer_eq_of_permutable (L B T C : Subgroup G)
    (hB : IsPGroup p B) (hT : ¬ p ∣ Nat.card T)
    (hperm : (T : Set G)*(B : Set G) = (B : Set G)*(T : Set G))
    (hBC : B ≤ C) (hTC : T ≤ normalizer (C : Set G))
    (hCL : C ≤ normalizer (L : Set G)) :
    conjugateSpanBy L (T ⊓ normalizer (B : Set G)) = conjugateSpanBy L T :=
  (span_of_kernel_factorization L T (T ⊓ normalizer (B : Set G)) C hTC hCL
    (pSubgroup_normalizer_supplement_of_permutable B T C hB hT hperm hBC hTC)
    inf_le_left).symm
end Subgroup
