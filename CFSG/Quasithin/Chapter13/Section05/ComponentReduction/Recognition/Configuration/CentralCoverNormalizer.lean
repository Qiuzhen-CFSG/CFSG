module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SimpleImage
public import CFSG.Quasithin.ChapterF.Section09.SeedNormalizer
public import Theory.GroupAction.CoprimeCentralizerLift
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The original component centralizer after the central-cover quotient

An element of Khat centralizing Vhat has a representative whose V* coset
modulo Z(K*) is fixed. The center has odd order, since the actual K/O₂(K)
quotient has trivial two-core. Coprime fixed-coset lifting puts that
representative in C_K*(V*) Z(K*). The central factor is killed in
X/C_X(K*), while genuine F.9.5(3) and N_H(V)≤N_G(L) make the first factor
normalize the same marked L₁ image.

The argument retains starHom, componentStarMap and the original quotient
map throughout. It assumes neither a new centralizer equality in the
central quotient nor the desired normalization conclusion.
Source: Aschbacher–Smith13.5.21(ii), printed p.923.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis)
  [(componentCentralizer s h).Normal]

theorem Khat_actor_centralizer_normalizes_local
    (hi : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hm : D.H ⊓ normalizer (D.V : Set G) ≤ normalizer (D.L : Set G)) :
    Khat s h ⊓ centralizer (Vhat s h : Set (Xhat s h)) ≤
      normalizer (L1hat s h : Set (Xhat s h)) := by
  let f := starHom s h
  let q := QuotientGroup.mk' (componentCentralizer s h)
  let P := starImage D.H K
  let A := starImage D.H D.V
  let Z := (center P).map P.subtype
  let R := (normalizer (L1hat s h : Set (Xhat s h))).comap q
  have hn : ¬ D.V ≤ D.QH := fun hc => hU (h.UH_elementary_of_V_le_QH hc).toIsMulCommutative
  have hVK := (selected_actor_normalization s h hi hU).1
  have hVX : D.V ≤ X D K :=
    (le_inf h.V_le_T hVK).trans (le_sup_right.trans le_sup_right)
  have hLX : D.L₁ ≤ X D K := le_sup_left.trans le_sup_right
  have hker : f.ker ≤ R := by
    intro x hx
    have hxC : x ∈ componentCentralizer s h := by
      change f x ∈ centralizer (P : Set (Hstar D.H))
      rw [show f x=1 from hx]
      exact one_mem _
    change q x ∈ normalizer (L1hat s h : Set (Xhat s h))
    rw [show q x=1 from (QuotientGroup.eq_one_iff x).mpr hxC]
    exact one_mem _
  have hC : P ⊓ centralizer (A : Set (Hstar D.H)) ≤ R.map f := by
    have he := h.star_relative_centralizer_eq_normalizer_image hi hn K
    change P ⊓ centralizer (A : Set (Hstar D.H)) =
      starImage D.H (K ⊓ normalizer (D.V : Set G)) at he
    rw [he]
    rintro _ ⟨k,hk,rfl⟩
    let kX : X D K := ⟨k.val,mem_sup_left hk.1⟩
    refine ⟨kX,?_,rfl⟩
    have hkn : k.val ∈ normalizer (D.L₁ : Set G) :=
      h.module_normalizer_normalizes_local hm ⟨k.property,hk.2⟩
    have hknX : kX ∈ normalizer (D.L₁.subgroupOf (X D K) : Set (X D K)) := by
      rw [←subgroupOf_normalizer_eq hLX]
      exact hkn
    exact (D.L₁.subgroupOf (X D K)).le_normalizer_map q (mem_map_of_mem q hknX)
  have hZ : Z ≤ R.map f := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨k,hk⟩ := componentStarMap_surjective s h z
    have he : f k.val = z.val := congrArg Subtype.val hk
    refine ⟨k.val,?_,he⟩
    have hkC : k.val ∈ componentCentralizer s h := by
      change f k.val ∈ centralizer (P : Set (Hstar D.H))
      rw [he]
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
    change q k.val ∈ normalizer (L1hat s h : Set (Xhat s h))
    rw [show q k.val=1 from (QuotientGroup.eq_one_iff k.val).mpr hkC]
    exact one_mem _
  have hAP : A ≤ normalizer (P : Set (Hstar D.H)) := by
    have hh : D.V.subgroupOf D.H ≤ normalizer (K.subgroupOf D.H : Set D.H) := by
      rw [←subgroupOf_normalizer_eq s.le_H]
      exact comap_mono hVK
    exact (map_mono hh).trans ((K.subgroupOf D.H).le_normalizer_map _)
  have hAZ : A ≤ normalizer (Z : Set (Hstar D.H)) :=
    hAP.trans (normalizer_le_normalizer_characteristic_image P (center P))
  have hZsub : Z.subgroupOf P = center P := comap_map_eq_self_of_injective P.subtype_injective _
  let : (Z.subgroupOf P).Normal := by rw [hZsub]; infer_instance
  let : IsMulCommutative (Z.subgroupOf P) := by rw [hZsub]; infer_instance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Z) := by
    have hcard : Nat.card A=2 := h.star_module_card_two hi hn
    rw [hcard,show Nat.card Z=Nat.card (center P) from card_map_of_injective P.subtype_injective]
    obtain ⟨e⟩ := s.quotient
    have hp : pCore 2 P=⊥ := by
      have he := pCore_map_iso 2 e
      rw [pCore_quotient_pCore_eq_bot,Subgroup.map_bot] at he
      exact he.symm
    exact Nat.prime_two.coprime_iff_not_dvd.mpr
      (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hp (center P) le_rfl)
  rintro _ ⟨⟨k,hk,rfl⟩,hfix⟩
  have hP : f k∈P := by
    change f k ∈ starImage D.H K
    rw [←starHom_map s h K le_sup_left]
    exact mem_map_of_mem f hk
  have hf : ∀ a∈A, MulAut.conj a (f k) / f k ∈ Z := by
    rintro _ ⟨v,hv,rfl⟩
    let vX : X D K := ⟨v.val,hVX hv⟩
    have hvA : f vX∈A := mem_map_of_mem _ hv
    have hqcomm : q ⁅vX,k⁆=1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact hfix (q vX) (mem_map_of_mem q hv)
    have hc : f ⁅vX,k⁆ ∈ centralizer (P : Set (Hstar D.H)) :=
      (QuotientGroup.eq_one_iff ⁅vX,k⁆).mp hqcomm
    have he : MulAut.conj (f vX) (f k) / f k = f ⁅vX,k⁆ := by
      simp only [commutatorElement_def,MulAut.conj_apply,div_eq_mul_inv,map_mul,map_inv]
    have hdelta : MulAut.conj (f vX) (f k) / f k ∈ P :=
      P.div_mem ((mem_normalizer_iff.mp (hAP hvA) (f k)).mp hP) hP
    change MulAut.conj (f vX) (f k) / f k ∈ Z
    refine ⟨⟨_,hdelta⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    change b.val * (MulAut.conj (f vX) (f k) / f k) =
      (MulAut.conj (f vX) (f k) / f k) * b.val
    rw [he]
    exact hc b b.property
  have hh := mem_centralizer_sup_of_coprime_fixed_coset P Z A (map_subtype_le _)
    hAP hAZ hcop (f k) hP hf
  have hhR : k ∈ (R.map f).comap f := (sup_le hC hZ) hh
  rw [comap_map_eq,sup_eq_left.mpr hker] at hhR
  exact hhR
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
