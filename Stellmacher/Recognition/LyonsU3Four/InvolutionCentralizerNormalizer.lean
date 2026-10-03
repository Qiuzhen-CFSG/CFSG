module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerQuotients
public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import BenderSuzuki.External.Huppert.IV.ComplementTransfer

/-!
# The reduced Sylow normalizer when the automizer has order three

Let C = C_G(z), where z is a nonidentity element of Z(S). Assuming that
Z(S) has central image in C/O₂′(C), the Sylow subgroup of
C/(O₂′(C) Z(S)) lies in the center of its normalizer.

Fusion moves z inside the Sylow normalizer. Since S C_G(S) has prime
index three there and fixes z, it is exactly the stabilizer of z.
Normalizers lift first through the odd core, then through the image of
Z(S), which lies in the Sylow image. Finally S′ = Z(S) makes the image
of S abelian, and C_G(S) already centralizes it.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
pp. 372–373, the paragraph beginning “Suppose |K| = 3”.
-/

namespace Stellmacher.Recognition.LyonsU3Four

private theorem involution_stabilizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (hthree : automizerIndex S = 3)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer ({z} : Set G) =
      (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G) := by
  let D := (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G)
  let N := Subgroup.normalizer (S : Set G)
  let C := Subgroup.centralizer ({z} : Set G)
  have hDC : D ≤ C := sup_le (sylow_le_involutionCentralizer S hz) (by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx z (centerImage_le S hz)).symm)
  have hDN : D ≤ N := sup_le Subgroup.le_normalizer
    (Subgroup.centralizer_le_normalizer _)
  have hDH : D ≤ N ⊓ C := le_inf hDN hDC
  have hprod : D.relIndex (N ⊓ C) * (N ⊓ C).relIndex N = 3 :=
    (Subgroup.relIndex_mul_relIndex D (N ⊓ C) N hDH inf_le_left).trans hthree
  have hnot : ¬ N ≤ C := by
    intro hn
    obtain ⟨y, hy, hyz, hzy⟩ := exists_distinct_conjugate_in_centerImage S h hz hz1
    have hy1 : y ≠ 1 := fun he => hz1 (isConj_one_left.mp (he ▸ hzy))
    obtain ⟨n, hnN, he⟩ := centerImage_nonidentity_normalizer_conjugate S h hz hy hz1 hy1
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hn hnN)
    have he' : n⁻¹ * z * n = z := by rw [mul_assoc, ← hc]; simp
    exact hyz (he.symm.trans he')
  have hdiv : D.relIndex (N ⊓ C) ∣ 3 := ⟨_, hprod.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with he | he
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp he) hDH
  · have hi : (N ⊓ C).relIndex N = 1 := by
      rw [he] at hprod
      omega
    exact (hnot ((Subgroup.relIndex_eq_one.mp hi).trans inf_le_right)).elim

open scoped commutatorElement

/-- The normalizer-centrality step of the index-three case, with the local
Z-star conclusion supplied explicitly. -/
public theorem centralizerReducedSylow_le_center_normalizer_of_automizerIndex_eq_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (hthree : automizerIndex S = 3)
    (z : G) (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (hcentral : centralizerCenterModOddCore S z ≤ Subgroup.center
      (Subgroup.centralizer ({z} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)))) :
    let Q := (Subgroup.centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) ⧸ centralizerCenterClosure S z
    let T : Sylow 2 Q := centralizerReducedSylow S hz
    (T : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (T : Set Q)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({z} : Set G)
  let P := centralizerSylow S hz
  let O := pPrimeCore 2 C
  let q : C →* C ⧸ O := QuotientGroup.mk' O
  let Z := centralizerCenterClosure S z
  let r : C ⧸ O →* (C ⧸ O) ⧸ Z := QuotientGroup.mk' Z
  let f := centralizerReductionMap S z
  have hP : (P : Subgroup C) = (S : Subgroup G).subgroupOf C := rfl
  have hZ : Z = centralizerCenterModOddCore S z :=
    centralizerCenterClosure_eq_of_le_center S z hcentral
  have hZP : Z ≤ (P : Subgroup C).map q := by
    rw [hZ]
    exact Subgroup.map_mono (fun x hx => centerImage_le S hx)
  have hnorm : Subgroup.normalizer (((P : Subgroup C).map f) : Set ((C ⧸ O) ⧸ Z)) =
      (Subgroup.normalizer (P : Set C)).map f := by
    have : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
    change Subgroup.normalizer (((P : Subgroup C).map (r.comp q)) : Set ((C ⧸ O) ⧸ Z)) = _
    rw [← Subgroup.map_map,
      BenderSuzuki.External.hkt_normalizer_map_quotient_eq_map_normalizer_of_le Z
        ((P : Subgroup C).map q) hZP,
      normalizer_map_quotient_eq_map_normalizer 2 (P : Subgroup C) O
        (inferInstance : O.Normal) (pPrimeCore_coprime_card (p := 2) (G := C)),
      Subgroup.map_map]
    rfl
  have hkill : ∀ x : C, (x : G) ∈ centerImage S → f x = 1 := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (q x)).mpr
    change q x ∈ Z
    rw [hZ]
    exact Subgroup.mem_map_of_mem q hx
  have hScomm : ∀ a b : C, a ∈ (P : Subgroup C) → b ∈ (P : Subgroup C) →
      f a * f b = f b * f a := by
    intro a b ha hb
    have hc : ⁅(a : G), (b : G)⁆ ∈ centerImage S := by
      refine ⟨⁅(⟨a, ha⟩ : S), (⟨b, hb⟩ : S)⁆, ?_, rfl⟩
      rw [h.center_eq_commutator]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have he := hkill ⁅a,b⁆ hc
    rw [map_commutatorElement] at he
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  have hSC : (S : Subgroup G) ≤ C := sylow_le_involutionCentralizer S hz
  have hCC : Subgroup.centralizer (S : Set G) ≤ C := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx z (centerImage_le S hz)).symm
  have hDC : ((S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G)).subgroupOf C ≤
      (Subgroup.centralizer (((P : Subgroup C).map f) : Set _)).comap f := by
    rw [Subgroup.subgroupOf_sup hSC hCC]
    apply sup_le
    · intro a ha
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨b, hb, rfl⟩
      exact hScomm b a hb ha
    · intro a ha
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨b, hb, rfl⟩
      have he : b * a = a * b := Subtype.ext
        (Subgroup.mem_centralizer_iff.mp ha b hb)
      simpa only [map_mul] using congrArg f he
  have hNC : Subgroup.normalizer (P : Set C) ≤
      (Subgroup.centralizer (((P : Subgroup C).map f) : Set _)).comap f := by
    apply le_trans ?_ hDC
    change Subgroup.normalizer ((P : Subgroup C) : Set C) ≤ _
    rw [hP, ← Subgroup.subgroupOf_normalizer_eq hSC]
    intro n hn
    exact (involution_stabilizer_eq S h hthree hz hz1).le ⟨hn, n.property⟩
  change (P : Subgroup C).map f ≤ centerIn
    (Subgroup.normalizer (((P : Subgroup C).map f) : Set ((C ⧸ O) ⧸ Z)))
  apply le_inf Subgroup.le_normalizer
  apply Subgroup.le_centralizer_iff.mpr
  rw [hnorm]
  exact Subgroup.map_le_iff_le_comap.mpr hNC

end Stellmacher.Recognition.LyonsU3Four
