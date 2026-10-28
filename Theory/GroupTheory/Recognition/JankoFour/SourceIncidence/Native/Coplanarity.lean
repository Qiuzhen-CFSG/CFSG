module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
/-!
# Coplanar native trios and the first three line labels

Seven explicit sextets through the standard trio supply a common plane for
any trio sharing one of its octads. Coverage is checked against the existing
3795-entry trio catalogue and its already proved surjectivity; no new trio
catalogue or transporter forest is constructed. Every sextet is verified
against the original Golay encoder. Native M24 transitivity transports the
shared-octad result to arbitrary trios, giving the exact coplanarity test
for the unchanged labels zero, one and two.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (3.9), pp.595–596,
applied in (5.4)(2), p.600, DOI 10.1007/BF01232280.
-/

public section
-- The full Scratch check took 127 seconds and 2.04 GiB peak RSS. Checking
-- the small finite certificates sequentially keeps this memory bound.
set_option Elab.async false
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeCoplanarity
open SourceCycleBase.Native SourceCycleBase.Native.FarOrbit
private def planeMasks : Fin 7 → Fin 6 → BitVec 24 :=
  ![![15, 133168, 541248, 1085568, 2367744, 12649472], ![10528, 20672, 66566, 1606144, 2490384, 12582921], ![33472, 403456, 1593344, 2097456, 4195331, 8454156], ![53760, 393504, 1573056, 2107408, 4259845, 8389642], ![66569, 139536, 529024, 1097792, 2361376, 12582918], ![264464, 561216, 1065600, 2236448, 4259850, 8389637], ![270384, 573568, 1053248, 2230528, 4195340, 8454147]]
private def planeMessage : Fin 7 → Fin 6 → Fin 6 → Fin 4096 :=
  ![![![0, 1087, 591, 143, 2319, 15], ![1087, 0, 1648, 1200, 3376, 1072], ![591, 1648, 0, 704, 2880, 576], ![143, 1200, 704, 0, 2432, 128], ![2319, 3376, 2880, 2432, 0, 2304], ![15, 1072, 576, 128, 2304, 0]], ![![0, 3552, 3366, 3872, 3376, 3369], ![3552, 0, 198, 704, 208, 201], ![3366, 198, 0, 518, 22, 15], ![3872, 704, 518, 0, 528, 521], ![3376, 208, 22, 528, 0, 25], ![3369, 201, 15, 521, 25, 0]], ![![0, 3776, 704, 1008, 707, 716], ![3776, 0, 3072, 3376, 3075, 3084], ![704, 3072, 0, 304, 3, 12], ![1008, 3376, 304, 0, 307, 316], ![707, 3075, 3, 307, 0, 15], ![716, 3084, 12, 316, 15, 0]], ![![0, 800, 704, 3600, 517, 522], ![800, 0, 480, 3376, 293, 298], ![704, 480, 0, 3280, 197, 202], ![3600, 3376, 3280, 0, 3093, 3098], ![517, 293, 197, 3093, 0, 15], ![522, 298, 202, 3098, 15, 0]], ![![0, 2329, 649, 73, 1065, 15], ![2329, 0, 2960, 2384, 3376, 2326], ![649, 2960, 0, 704, 1696, 646], ![73, 2384, 704, 0, 1120, 70], ![1065, 3376, 1696, 1120, 0, 1062], ![15, 2326, 646, 70, 1062, 0]], ![![0, 1360, 1936, 3376, 1306, 1301], ![1360, 0, 704, 2144, 74, 69], ![1936, 704, 0, 2720, 650, 645], ![3376, 2144, 2720, 0, 2090, 2085], ![1306, 74, 650, 2090, 0, 15], ![1301, 69, 645, 2085, 15, 0]], ![![0, 2224, 2672, 3376, 2108, 2099], ![2224, 0, 704, 1408, 140, 131], ![2672, 704, 0, 1856, 588, 579], ![3376, 1408, 1856, 0, 1292, 1283], ![2108, 140, 588, 1292, 0, 15], ![2099, 131, 579, 1283, 15, 0]]]
private def standardMasks : Fin 3 → BitVec 24 := ![12649487, 1626816, 2500912]

private def shares (i : Fin 3795) : Prop :=
  ∃ j k : Fin 3, (row i).masks j = standardMasks k
private instance (i : Fin 3795) : Decidable (shares i) := inferInstanceAs (Decidable (∃ j k : Fin 3, (row i).masks j = standardMasks k))
private def covered (i : Fin 3795) : Prop :=
  ∃ s : Fin 7, ∀ j : Fin 3, ∃ b c : Fin 6, b ≠ c ∧
    (row i).masks j = planeMasks s b ||| planeMasks s c
private instance (i : Fin 3795) : Decidable (covered i) :=
  inferInstanceAs (Decidable (∃ s : Fin 7, ∀ j : Fin 3, ∃ b c : Fin 6, b ≠ c ∧ (row i).masks j = planeMasks s b ||| planeMasks s c))

private theorem covered00 : ∀ j : Fin 64, shares (index 0 j) → covered (index 0 j) := by decide +kernel

private theorem covered01 : ∀ j : Fin 64, shares (index 1 j) → covered (index 1 j) := by decide +kernel

private theorem covered02 : ∀ j : Fin 64, shares (index 2 j) → covered (index 2 j) := by decide +kernel

private theorem covered03 : ∀ j : Fin 64, shares (index 3 j) → covered (index 3 j) := by decide +kernel

private theorem covered04 : ∀ j : Fin 64, shares (index 4 j) → covered (index 4 j) := by decide +kernel

private theorem covered05 : ∀ j : Fin 64, shares (index 5 j) → covered (index 5 j) := by decide +kernel

private theorem covered06 : ∀ j : Fin 64, shares (index 6 j) → covered (index 6 j) := by decide +kernel

private theorem covered07 : ∀ j : Fin 64, shares (index 7 j) → covered (index 7 j) := by decide +kernel

private theorem covered08 : ∀ j : Fin 64, shares (index 8 j) → covered (index 8 j) := by decide +kernel

private theorem covered09 : ∀ j : Fin 64, shares (index 9 j) → covered (index 9 j) := by decide +kernel

private theorem covered10 : ∀ j : Fin 64, shares (index 10 j) → covered (index 10 j) := by decide +kernel

private theorem covered11 : ∀ j : Fin 64, shares (index 11 j) → covered (index 11 j) := by decide +kernel

private theorem covered12 : ∀ j : Fin 64, shares (index 12 j) → covered (index 12 j) := by decide +kernel

private theorem covered13 : ∀ j : Fin 64, shares (index 13 j) → covered (index 13 j) := by decide +kernel

private theorem covered14 : ∀ j : Fin 64, shares (index 14 j) → covered (index 14 j) := by decide +kernel

private theorem covered15 : ∀ j : Fin 64, shares (index 15 j) → covered (index 15 j) := by decide +kernel

private theorem covered16 : ∀ j : Fin 64, shares (index 16 j) → covered (index 16 j) := by decide +kernel

private theorem covered17 : ∀ j : Fin 64, shares (index 17 j) → covered (index 17 j) := by decide +kernel

private theorem covered18 : ∀ j : Fin 64, shares (index 18 j) → covered (index 18 j) := by decide +kernel

private theorem covered19 : ∀ j : Fin 64, shares (index 19 j) → covered (index 19 j) := by decide +kernel

private theorem covered20 : ∀ j : Fin 64, shares (index 20 j) → covered (index 20 j) := by decide +kernel

private theorem covered21 : ∀ j : Fin 64, shares (index 21 j) → covered (index 21 j) := by decide +kernel

private theorem covered22 : ∀ j : Fin 64, shares (index 22 j) → covered (index 22 j) := by decide +kernel

private theorem covered23 : ∀ j : Fin 64, shares (index 23 j) → covered (index 23 j) := by decide +kernel

private theorem covered24 : ∀ j : Fin 64, shares (index 24 j) → covered (index 24 j) := by decide +kernel

private theorem covered25 : ∀ j : Fin 64, shares (index 25 j) → covered (index 25 j) := by decide +kernel

private theorem covered26 : ∀ j : Fin 64, shares (index 26 j) → covered (index 26 j) := by decide +kernel

private theorem covered27 : ∀ j : Fin 64, shares (index 27 j) → covered (index 27 j) := by decide +kernel

private theorem covered28 : ∀ j : Fin 64, shares (index 28 j) → covered (index 28 j) := by decide +kernel

private theorem covered29 : ∀ j : Fin 64, shares (index 29 j) → covered (index 29 j) := by decide +kernel

private theorem covered30 : ∀ j : Fin 64, shares (index 30 j) → covered (index 30 j) := by decide +kernel

private theorem covered31 : ∀ j : Fin 64, shares (index 31 j) → covered (index 31 j) := by decide +kernel

private theorem covered32 : ∀ j : Fin 64, shares (index 32 j) → covered (index 32 j) := by decide +kernel

private theorem covered33 : ∀ j : Fin 64, shares (index 33 j) → covered (index 33 j) := by decide +kernel

private theorem covered34 : ∀ j : Fin 64, shares (index 34 j) → covered (index 34 j) := by decide +kernel

private theorem covered35 : ∀ j : Fin 64, shares (index 35 j) → covered (index 35 j) := by decide +kernel

private theorem covered36 : ∀ j : Fin 64, shares (index 36 j) → covered (index 36 j) := by decide +kernel

private theorem covered37 : ∀ j : Fin 64, shares (index 37 j) → covered (index 37 j) := by decide +kernel

private theorem covered38 : ∀ j : Fin 64, shares (index 38 j) → covered (index 38 j) := by decide +kernel

private theorem covered39 : ∀ j : Fin 64, shares (index 39 j) → covered (index 39 j) := by decide +kernel

private theorem covered40 : ∀ j : Fin 64, shares (index 40 j) → covered (index 40 j) := by decide +kernel

private theorem covered41 : ∀ j : Fin 64, shares (index 41 j) → covered (index 41 j) := by decide +kernel

private theorem covered42 : ∀ j : Fin 64, shares (index 42 j) → covered (index 42 j) := by decide +kernel

private theorem covered43 : ∀ j : Fin 64, shares (index 43 j) → covered (index 43 j) := by decide +kernel

private theorem covered44 : ∀ j : Fin 64, shares (index 44 j) → covered (index 44 j) := by decide +kernel

private theorem covered45 : ∀ j : Fin 64, shares (index 45 j) → covered (index 45 j) := by decide +kernel

private theorem covered46 : ∀ j : Fin 64, shares (index 46 j) → covered (index 46 j) := by decide +kernel

private theorem covered47 : ∀ j : Fin 64, shares (index 47 j) → covered (index 47 j) := by decide +kernel

private theorem covered48 : ∀ j : Fin 64, shares (index 48 j) → covered (index 48 j) := by decide +kernel

private theorem covered49 : ∀ j : Fin 64, shares (index 49 j) → covered (index 49 j) := by decide +kernel

private theorem covered50 : ∀ j : Fin 64, shares (index 50 j) → covered (index 50 j) := by decide +kernel

private theorem covered51 : ∀ j : Fin 64, shares (index 51 j) → covered (index 51 j) := by decide +kernel

private theorem covered52 : ∀ j : Fin 64, shares (index 52 j) → covered (index 52 j) := by decide +kernel

private theorem covered53 : ∀ j : Fin 64, shares (index 53 j) → covered (index 53 j) := by decide +kernel

private theorem covered54 : ∀ j : Fin 64, shares (index 54 j) → covered (index 54 j) := by decide +kernel

private theorem covered55 : ∀ j : Fin 64, shares (index 55 j) → covered (index 55 j) := by decide +kernel

private theorem covered56 : ∀ j : Fin 64, shares (index 56 j) → covered (index 56 j) := by decide +kernel

private theorem covered57 : ∀ j : Fin 64, shares (index 57 j) → covered (index 57 j) := by decide +kernel

private theorem covered58 : ∀ j : Fin 64, shares (index 58 j) → covered (index 58 j) := by decide +kernel

private theorem covered59 : ∀ j : Fin 64, shares (index 59 j) → covered (index 59 j) := by decide +kernel

private theorem covered_chunks (k : Fin 60) (j : Fin 64) : shares (index k j) → covered (index k j) := by
  fin_cases k
  · exact covered00 j
  · exact covered01 j
  · exact covered02 j
  · exact covered03 j
  · exact covered04 j
  · exact covered05 j
  · exact covered06 j
  · exact covered07 j
  · exact covered08 j
  · exact covered09 j
  · exact covered10 j
  · exact covered11 j
  · exact covered12 j
  · exact covered13 j
  · exact covered14 j
  · exact covered15 j
  · exact covered16 j
  · exact covered17 j
  · exact covered18 j
  · exact covered19 j
  · exact covered20 j
  · exact covered21 j
  · exact covered22 j
  · exact covered23 j
  · exact covered24 j
  · exact covered25 j
  · exact covered26 j
  · exact covered27 j
  · exact covered28 j
  · exact covered29 j
  · exact covered30 j
  · exact covered31 j
  · exact covered32 j
  · exact covered33 j
  · exact covered34 j
  · exact covered35 j
  · exact covered36 j
  · exact covered37 j
  · exact covered38 j
  · exact covered39 j
  · exact covered40 j
  · exact covered41 j
  · exact covered42 j
  · exact covered43 j
  · exact covered44 j
  · exact covered45 j
  · exact covered46 j
  · exact covered47 j
  · exact covered48 j
  · exact covered49 j
  · exact covered50 j
  · exact covered51 j
  · exact covered52 j
  · exact covered53 j
  · exact covered54 j
  · exact covered55 j
  · exact covered56 j
  · exact covered57 j
  · exact covered58 j
  · exact covered59 j

private theorem all_covered (i : Fin 3795) : shares i → covered i := by
  have he : index ⟨i.val / 64,by omega⟩ ⟨i.val % 64,by omega⟩ = i := by
    apply Fin.ext
    simp only [index]
    omega
  rw [←he]
  exact covered_chunks _ _

private theorem support_or (a b : BitVec 24) : support (a ||| b) = support a ∪ support b := by
  ext i
  simp [support, BitVec.getLsb]

private theorem plane_word (s : Fin 7) (i j : Fin 6) (hij : i ≠ j) :
    support (planeMasks s i) ∪ support (planeMasks s j) =
      m24GolayWord (planeMessage s i j) := by
  revert s i j; decide +kernel

private def witnessPlane (s : Fin 7) : Plane where
  parts := Finset.univ.image (fun i => support (planeMasks s i))
  card := by revert s; decide +kernel
  tetrad := by
    intro A hA
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    revert s i; decide +kernel
  disjoint := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    revert s i j; decide +kernel
  cover := by revert s; decide +kernel
  octad := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    have hij : i ≠ j := fun he => hne (he ▸ rfl)
    rw [plane_word s i j hij]
    apply m24GolayWord_mem_blocks_of_card_eq_eight
    revert s i j; decide +kernel

private theorem standard_incident (s : Fin 7) : Incident standardTrio (witnessPlane s) := by
  have hh : ∀ (s : Fin 7) (j : Fin 3), ∃ b c : Fin 6,
      b ≠ c ∧ standardTrioOctad j = support (planeMasks s b) ∪ support (planeMasks s c) := by
    decide +kernel
  intro A hA
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b,c,hbc,he⟩ := hh s j
  refine ⟨support (planeMasks s b),Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩,
    support (planeMasks s c),Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,?_,he⟩
  have hinj : ∀ s : Fin 7, Function.Injective (fun b : Fin 6 => support (planeMasks s b)) := by
    decide +kernel
  exact (hinj s).ne hbc

private theorem shared_standard_coplanar (m : Line)
    (hm : (standardTrio.parts ∩ m.parts).Nonempty) : Coplanar standardTrio m := by
  obtain ⟨i,rfl⟩ := entry_surjective m
  have hshares : shares i := by
    obtain ⟨A,hA⟩ := hm
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hA).1
    have hi := (Finset.mem_inter.mp hA).2
    rw [entry_parts] at hi
    obtain ⟨b,hb,hbA⟩ := Finset.mem_image.mp hi
    have hb' : ∃ j : Fin 3, b = (row i).masks j := by
      simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with rfl|rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    obtain ⟨j,rfl⟩ := hb'
    refine ⟨j,k,support_injective ?_⟩
    have hs : ∀ k : Fin 3, support (standardMasks k) = standardTrioOctad k := by decide +kernel
    exact hbA.trans (hk.symm.trans (hs k).symm)
  obtain ⟨s,hs⟩ := all_covered i hshares
  refine ⟨witnessPlane s,standard_incident s,?_⟩
  intro A hA
  rw [entry_parts] at hA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
  have hb' : ∃ j : Fin 3, b = (row i).masks j := by
    simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨j,rfl⟩ := hb'
  obtain ⟨b,c,hbc,he⟩ := hs j
  refine ⟨support (planeMasks s b),Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩,
    support (planeMasks s c),Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,?_,?_⟩
  · have hinj : ∀ s : Fin 7, Function.Injective (fun b : Fin 6 => support (planeMasks s b)) := by
      decide +kernel
    exact (hinj s).ne hbc
  · rw [he,support_or]

theorem shared_octad_coplanar (l m : Line)
    (hm : (l.parts ∩ m.parts).Nonempty) : Coplanar l m := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 standardTrio l
  have hi : (standardTrio.parts ∩ (g⁻¹ • m).parts).Nonempty := by
    obtain ⟨A,hA⟩ := hm
    refine ⟨g⁻¹ • A,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · have hh := Finset.smul_mem_smul_finset (a := g⁻¹) (Finset.mem_inter.mp hA).1
      rw [←hg,smulLine_parts,inv_smul_smul] at hh
      exact hh
    · exact Finset.smul_mem_smul_finset (Finset.mem_inter.mp hA).2
  exact coplanar_transport g (congrArg Trio.parts hg).symm
    (by simp only [smulLine_parts,smul_inv_smul]) (shared_standard_coplanar _ hi)

/-- AS91 (3.9): the first three native labels are exactly coplanarity. -/
theorem coplanar_iff (l m : Line) :
    Coplanar l m ↔ ∃ i : Fin 5, i.val ≤ 2 ∧ Delta i l m := by
  classical
  constructor
  · intro hc
    by_cases he : l.parts = m.parts
    · exact ⟨0,by decide,he⟩
    by_cases hs : (l.parts ∩ m.parts).Nonempty
    · exact ⟨1,by decide,he,hs⟩
    exact ⟨2,by decide,Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hs),hc⟩
  · rintro ⟨i,hi,ht⟩
    fin_cases i
    · have he := line_parts_injective ht
      subst m
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 standardTrio l
      exact coplanar_transport g (congrArg Trio.parts hg).symm
        (congrArg Trio.parts hg).symm ⟨witnessPlane 0,standard_incident 0,standard_incident 0⟩
    · exact shared_octad_coplanar l m ht.2
    · exact ht.2
    · norm_num at hi
    · norm_num at hi

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeCoplanarity
