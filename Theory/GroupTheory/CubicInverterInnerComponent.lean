module
public import Theory.GroupTheory.SylowInnerAction
public import Theory.GroupTheory.NormalQuotientOuterAction
public import Theory.GroupTheory.TwoPerfectCubicNormalizer
public import Theory.GroupTheory.PResidual.NormalizerLift
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PPerfectHom

/-!
# Centralizing inverters outside a normal component

Let A be two-perfect with cubic A/O₂(A), normalized by a Sylow two-subgroup S,
and let C be normal with A outside C and centerless C/O₂(C). If an element
of S inverts A/O₂(A) and acts inner on C/O₂(C), its inner conjugator lifts
inside S∩C. This intersection acts trivially on A/O₂(A): the kernel of
A → G/C is a normal two-group. Removing the conjugator therefore gives
an inverter in the literal component-action kernel. Two-perfectness then
forces the entire A-action on C/O₂(C) to be trivial.

Finally C normalizes A. Quotient by the embedded O₂(C), which normalizes A
because it lies in S, and lift the image normalizer using two-perfectness.
No splitting of either two-core extension is used.

Source application: Aschbacher–Smith 14.7.41, printed p.1061,
refs/quasithin.pdf, the outside-component inner-action branch.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An inner actor in the prescribed Sylow has a conjugator in its component intersection. -/
theorem normalQuotient_inner_sylow_lift (C : Subgroup G) [C.Normal]
    (S : Sylow 2 G) (hz : center (C ⧸ pCore 2 C) = ⊥)
    (t : G) (ht : t ∈ S)
    (hi : normalQuotientAction C (pCore 2 C) t ∈ MulAut.innerSubgroup (C ⧸ pCore 2 C)) :
    ∃ c : C, (c : G) ∈ S ∧
      normalQuotientAction C (pCore 2 C) (c : G) =
        normalQuotientAction C (pCore 2 C) t := by
  let a := normalQuotientAction C (pCore 2 C)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  obtain ⟨b,hb⟩ := hi
  have hQ : (Q : Subgroup (C ⧸ pCore 2 C)).map MulAut.conj ≤ (S : Subgroup G).map a := by
    rintro _ ⟨_,⟨c,hc,rfl⟩,rfl⟩
    refine ⟨c,?_,normalQuotientAction_inner C (pCore 2 C) c⟩
    rw [hP] at hc
    exact hc
  have hbQ : b ∈ Q := MulAut.inner_mem_image_sylow hz Q ((S : Subgroup G).map a)
    (S.isPGroup'.map a) hQ (hb.symm ▸ mem_map_of_mem a ht)
  obtain ⟨c,hc,he⟩ := hbQ
  refine ⟨c,?_,?_⟩
  · rw [hP] at hc
    exact hc
  · rw [normalQuotientAction_inner,he]
    exact hb

private theorem eq_one_of_twoPerfect_inverted {A D : Type*} [Group A] [Group D]
    (f : A →* D) (hp : IsPPerfect 2 A)
    (b : MulAut A) (hi : ∀ x : A, b x * x ∈ pCore 2 A)
    (hf : ∀ x : A, f (b x) = f x) : f = 1 := by
  have hr : IsPGroup 2 f.range := by
    rintro ⟨_,x,rfl⟩
    obtain ⟨n,hn⟩ := pCore_isPGroup (p := 2) (⟨b x * x,hi x⟩ : pCore 2 A)
    have hh : (f x ^ 2) ^ (2^n) = 1 := by
      have hh := congrArg f (congrArg Subtype.val hn)
      change f ((b x * x) ^ (2^n)) = f 1 at hh
      simpa only [map_pow,map_mul,hf,pow_two,map_one] using hh
    refine ⟨n+1,Subtype.ext ?_⟩
    change f x ^ (2^(n+1)) = 1
    rw [pow_succ,Nat.mul_comm,pow_mul]
    exact hh
  have he := hp.hom_eq_one_of_isPGroup hr f.rangeRestrict
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun he x)

/-- Correct the original inverter within the actual Sylow, and kill the entire cubic action. -/
theorem outside_cubic_centralizing_inverter
    (A C : Subgroup G) [C.Normal] (S : Sylow 2 G)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) (hout : ¬ A ≤ C)
    (hz : center (C ⧸ pCore 2 C) = ⊥)
    (t : G) (ht : t ∈ S)
    (hti : ∀ a ∈ A, t*a*t⁻¹*a ∈ A.pCoreIn 2)
    (htinner : normalQuotientAction C (pCore 2 C) t ∈
      MulAut.innerSubgroup (C ⧸ pCore 2 C)) :
    ∃ s : G, s ∈ S ∧ normalQuotientAction C (pCore 2 C) s = 1 ∧
      (∀ a ∈ A, s*a*s⁻¹*a ∈ A.pCoreIn 2) ∧
      A ≤ (normalQuotientAction C (pCore 2 C)).ker := by
  let f := (QuotientGroup.mk' C).comp A.subtype
  have hf : f ≠ 1 := by
    intro he
    apply hout
    intro a ha
    have hh := DFunLike.congr_fun he (⟨a,ha⟩ : A)
    exact (QuotientGroup.eq_one_iff _).mp hh
  have hk : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,f.kernel_isTwoGroup_of_twoPerfect_cubic hp hc hf⟩
  have hAC : A ⊓ C ≤ A.pCoreIn 2 := by
    intro a ha
    exact mem_map_of_mem A.subtype (hk (show (⟨a,ha.1⟩ : A) ∈ f.ker from
      (QuotientGroup.eq_one_iff _).mpr ha.2))
  obtain ⟨c,hcS,hce⟩ := normalQuotient_inner_sylow_lift C S hz t ht htinner
  let s := (c : G)⁻¹ * t
  have hs : s ∈ S := S.mul_mem (S.inv_mem hcS) ht
  have hsk : normalQuotientAction C (pCore 2 C) s = 1 := by
    change normalQuotientAction C (pCore 2 C) ((c : G)⁻¹*t) = 1
    rw [map_mul,map_inv,hce,inv_mul_cancel]
  have hci (a : G) (ha : a ∈ A) : (c : G)⁻¹*a*(c : G)*a⁻¹ ∈ A.pCoreIn 2 := by
    apply hAC
    constructor
    · change (c : G)⁻¹*a*(c : G)*a⁻¹ ∈ A
      simpa only [inv_inv] using A.mul_mem
        ((mem_normalizer_iff.mp (hn (S.inv_mem hcS)) a).mp ha) (A.inv_mem ha)
    · change (c : G)⁻¹*a*(c : G)*a⁻¹ ∈ C
      have hh := C.mul_mem (C.inv_mem c.property)
        ((inferInstance : C.Normal).conj_mem (c : G) c.property a)
      simpa only [mul_assoc] using hh
  have hsi (a : G) (ha : a ∈ A) : s*a*s⁻¹*a ∈ A.pCoreIn 2 := by
    have hta : t*a*t⁻¹ ∈ A := (mem_normalizer_iff.mp (hn ht) a).mp ha
    have hh := (A.pCoreIn 2).mul_mem (hci _ hta) (hti a ha)
    convert hh using 1
    dsimp only [s]
    group
  refine ⟨s,hs,hsk,hsi,?_⟩
  let b := A.normalizerMonoidHom ⟨s,hn hs⟩
  let r := (normalQuotientAction C (pCore 2 C)).comp A.subtype
  have he : r = 1 := eq_one_of_twoPerfect_inverted r hp b (fun a => by
    exact (mem_map_iff_mem A.subtype_injective).mp (hsi a a.property)) (fun a => by
      change normalQuotientAction C (pCore 2 C) (s*(a:G)*s⁻¹) = _
      rw [map_mul,map_mul,map_inv,hsk,one_mul,inv_one,mul_one]
      rfl)
  intro a ha
  exact DFunLike.congr_fun he (⟨a,ha⟩ : A)

omit [Finite G] in
/-- Trivial action on the component quotient lifts to normalization of the two-perfect actor. -/
theorem normalizes_of_trivial_core_action
    (A C : Subgroup G) [C.Normal] (S : Sylow 2 G)
    (hp : IsPPerfect 2 A) (hn : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hfix : A ≤ (normalQuotientAction C (pCore 2 C)).ker) :
    C ≤ normalizer (A : Set G) := by
  let N := C.pCoreIn 2
  let : N.Normal := inferInstanceAs ((pCore 2 C).map C.subtype).Normal
  let q := QuotientGroup.mk' N
  have hNS : N ≤ (S : Subgroup G) := (isPGroup_pCoreIn 2 C).le_sylow_of_normal S
  have hker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact isPGroup_pCoreIn 2 C
  have hkerN : q.ker ≤ normalizer (A : Set G) := by
    rw [QuotientGroup.ker_mk']
    exact hNS.trans hn
  have hcom : ⁅A,C⁆ ≤ N := by
    apply commutator_le.mpr
    intro a ha c hc
    have he := MulEquiv.congr_fun (show normalQuotientAction C (pCore 2 C) a = 1 from hfix ha)
      (QuotientGroup.mk' (pCore 2 C) (⟨c,hc⟩ : C))
    rw [normalQuotientAction_apply_mk] at he
    have hh : MulAut.conjNormal a (⟨c,hc⟩ : C) * (⟨c,hc⟩ : C)⁻¹ ∈ pCore 2 C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 C) (_ * _) = 1
      rw [map_mul,map_inv,he]
      exact mul_inv_cancel _
    exact mem_map_of_mem C.subtype hh
  have hnorm : C.map q ≤ normalizer (A.map q : Set (G ⧸ N)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [←map_commutator,commutator_comm]
    have hh := map_mono (f := q) hcom
    have hzero : N.map q = ⊥ := by
      apply (map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    rw [hzero] at hh
    exact hh.trans bot_le
  exact ((le_comap_map q C).trans (comap_mono hnorm)).trans
    (normalizer_comap_map_le_of_pGroup_kernel q A hp hker hkerN)

end Subgroup
