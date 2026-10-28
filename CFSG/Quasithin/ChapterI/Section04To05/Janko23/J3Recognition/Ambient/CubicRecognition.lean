module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneNatural
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Eight

/-!
# The actual cubic centralizer quotient is A₆

Choose a central cubic in an actual complement of the marked plane
normalizer. The complement has order 180 and embeds into the cubic
centralizer, so its quotient by the central cubic has order divisible by 60.
The H-type calculation supplies D₈ as every involution centralizer of this
quotient. Unique central involutions and Sylow conjugacy supply fusion.
The proved dihedral recognition theorem gives L₃(2) or A₆; divisibility by
five excludes the order-168 group, leaving an actual A₆ isomorphism.

This reuses the checked Bender/BSW source route behind I.4.1(2). It proves
the centralizer-quotient step of Baumeister Lemma 2.4, not the subsequent
normalizer identification, central-extension splitting or ambient recognition.

Sources: Baumeister, *A geometry for groups of J₃-type* (2007), Lemma 2.4,
p.495; Bender, *Finite groups with large subgroups* (1974), §3, pp.224–225;
Aschbacher–Smith I.4.1(2), p.415.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient
open LocalSixteen
variable {G : Type*} [Group G] [Finite G]

/-- An actual central cubic and all the hypotheses needed for the dihedral quotient recognition. -/
theorem plane_cubic_bender_input {D : Seed G} (P : ReturningPair D)
    (hc : OneInvolutionClass G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (C : Subgroup (normalizer (A : Set G))) (s : C),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
      Nat.card C = 180 ∧ s ∈ center C ∧ orderOf s = 3 ∧
      60 ∣ Nat.card (centralizer ({((s : normalizer (A : Set G)) : G)} : Set G) ⧸
        cubicKernel ((s : normalizer (A : Set G)) : G)) ∧
      ∀ v : centralizer ({((s : normalizer (A : Set G)) : G)} : Set G) ⧸
          cubicKernel ((s : normalizer (A : Set G)) : G),
        orderOf v = 2 → Nonempty (centralizer ({v} : Set _) ≃* DihedralGroup 4) := by
  obtain ⟨C,f,hC,hcard,_⟩ := P.plane_normalizer_marked_complement hc A hA hAR
  obtain ⟨hZ,hZc⟩ := P.plane_automizer_central_cubic hc A hA hAR
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := _)
    3 (by rw [hZ])
  let s : C := f.symm a.val
  have hs : orderOf s = 3 := (f.symm.orderOf_eq a.val).trans ((orderOf_coe a).trans ha)
  have hsc : s ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    apply f.injective
    simpa only [map_mul, s, f.apply_symm_apply] using mem_center_iff.mp (hZc a.property) (f c)
  let j : C →* G := (normalizer (A : Set G)).subtype.comp C.subtype
  have hj : Function.Injective j := (normalizer (A : Set G)).subtype_injective.comp C.subtype_injective
  have hsG : orderOf (j s) = 3 := (orderOf_injective j hj s).trans hs
  let CS := centralizer ({j s} : Set G)
  have hCC : j.range ≤ CS := by
    rintro _ ⟨c,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul, mem_center_iff.mp hsc c]
  have hd : 180 ∣ Nat.card CS := by
    have hh := card_dvd_of_le hCC
    rwa [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, hcard] at hh
  have hq : Nat.card (CS ⧸ cubicKernel (j s)) * 3 = Nat.card CS := by
    have hh := (cubicKernel (j s)).index_mul_card
    rwa [cubicKernel_card (j s) hsG] at hh
  have h60 : 60 ∣ Nat.card (CS ⧸ cubicKernel (j s)) := by
    obtain ⟨n,hn⟩ := hd
    refine ⟨n,?_⟩
    omega
  exact ⟨C,s,hC,hcard,hsc,hs,h60,
    cubic_quotient_involution_centralizers D.localType hc (j s) hsG⟩


/-- The dihedral recognition alternative of order 168 is excluded by the actual divisor 60. -/
theorem alternatingSix_of_dihedral_centralizers {B : Type*} [Group B] [Finite B]
    (h60 : 60 ∣ Nat.card B)
    (h : ∀ t : B, orderOf t = 2 → Nonempty (centralizer ({t} : Set B) ≃* DihedralGroup 4)) :
    Nonempty (B ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    ((by decide : 2 ∣ 60).trans h60)
  let D : DihedralInvolutionCentralizerHypotheses B 3 := {
    two_le := by decide
    z := t
    involution := ⟨by intro h1; simp [h1] at ht, ht ▸ pow_orderOf_eq_one t⟩
    involutions_conjugate := fun u hu => isConj_iff.mp
      (Sporadic.Janko3.SourceRecognition.CentralCubicQuotient.dihedral_centralizers_fusion h u t
        (orderOf_eq_prime hu.2 hu.1) ht)
    centralizer_equiv := h t ht }
  rcases D.recognize_eight with he | he
  · obtain ⟨e⟩ := he
    have hcard : Nat.card B = 168 := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm.toEquiv).trans
        Atlas.Comparisons.Exceptional.sl3Two_card
    rw [hcard] at h60
    norm_num at h60
  · exact he


/-- The actual plane complement supplies a cubic whose full ambient centralizer quotient is A₆. -/
theorem plane_cubic_quotient_alternatingSix {D : Seed G} (P : ReturningPair D)
    (hc : OneInvolutionClass G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (C : Subgroup (normalizer (A : Set G))) (s : C),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
      Nat.card C = 180 ∧ s ∈ center C ∧ orderOf s = 3 ∧
      Nonempty ((centralizer ({((s : normalizer (A : Set G)) : G)} : Set G) ⧸
        cubicKernel ((s : normalizer (A : Set G)) : G)) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨C,s,hC,hcard,hsc,hs,h60,hD⟩ := plane_cubic_bender_input P hc A hA hAR
  exact ⟨C,s,hC,hcard,hsc,hs,alternatingSix_of_dihedral_centralizers h60 hD⟩

end CFSG.Quasithin.Janko23.J3Recognition.Ambient
