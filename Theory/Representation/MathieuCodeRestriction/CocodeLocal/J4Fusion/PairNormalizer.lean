module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.PairSpaces
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.SourceInvolutions

/-!
# Marked pair-plane normalizers in the Todd module

The three nonzero vectors of a pure pair plane lift to the three edges of
a coordinate triangle. An actor fixing the distinguished edge and preserving
the plane fixes the third coordinate. Thus its actual stabilizer embeds in
an M23 point stabilizer and has two-rank at most four; every involution there
fixes seven Todd dimensions. The two native M24 involution classes also give
the fixed ranks seven and six without reclassifying involutions.

The pair-word calculation uses the existing Golay minimum-distance proof.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(a),(b), p.602.
-/

public section
open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace MathieuCode.J4Fusion

private theorem pair_add_support (A B C : PointPair)
    (he : pairVector A + pairVector B = pairVector C) :
    C.val = (A.val \ B.val) ∪ (B.val \ A.val) := by
  have hw := pair_add_lifts A B C he
  ext i
  have hi := congrFun hw i
  simp only [Pi.add_apply, wordOfSet] at hi
  by_cases ha : i ∈ A.val <;> by_cases hb : i ∈ B.val <;>
    by_cases hc : i ∈ C.val <;> simp_all

private theorem pair_external_singleton (A B C : PointPair)
    (he : pairVector A + pairVector B = pairVector C) :
    ∃ i : Fin 24, B.val \ A.val = {i} ∧ C.val \ A.val = {i} := by
  classical
  have hs := pair_add_support A B C he
  have hd : Disjoint (A.val \ B.val) (B.val \ A.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hc := C.property
  rw [hs,Finset.card_union_of_disjoint hd] at hc
  have hA := Finset.card_sdiff_add_card_inter A.val B.val
  have hB := Finset.card_sdiff_add_card_inter B.val A.val
  rw [A.property] at hA
  rw [Finset.inter_comm B.val A.val,B.property] at hB
  have hcard : (B.val \ A.val).card = 1 := by omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i,hi,?_⟩
  rw [hs]
  have hh : ((A.val \ B.val) ∪ (B.val \ A.val)) \ A.val = B.val \ A.val := by
    ext j
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hh,hi]

private theorem pair_space_elements (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B)
    (A B : PointPair) (ha : pairVector A ∈ U) (hb : pairVector B ∈ U)
    (hne : A ≠ B) :
    ∀ v ∈ U, v = 0 ∨ v = pairVector A ∨ v = pairVector B ∨
      v = pairVector A + pairVector B := by
  classical
  let va : U := ⟨pairVector A,ha⟩
  let vb : U := ⟨pairVector B,hb⟩
  have ha0 : va ≠ 0 := fun h => pairVector_ne_zero A (congrArg Subtype.val h)
  have hb0 : vb ≠ 0 := fun h => pairVector_ne_zero B (congrArg Subtype.val h)
  have hab : va ≠ vb := fun h => hne (pairVector_injective (congrArg Subtype.val h))
  have hsum : va + vb ≠ 0 := by
    intro he
    have hh := congrArg (fun x : U => x + vb) he
    have hbb : vb + vb = 0 := by
      rw [←two_smul (ZMod 2),show (2 : ZMod 2) = 0 from rfl,zero_smul]
    rw [add_assoc,hbb,add_zero,zero_add] at hh
    exact hab hh
  let s : Finset U := {0,va,vb,va+vb}
  have hsc : s.card = 4 := by
    have hsa : va+vb ≠ va := fun he => hb0 ((add_left_cancel (he.trans (add_zero va).symm)))
    have hsb : va+vb ≠ vb := fun he => ha0 ((add_right_cancel (he.trans (zero_add vb).symm)))
    simp [s,ha0.symm,hb0.symm,hsum.symm,hab,hsa.symm,hsb.symm]
  have hsurj : Function.Surjective (fun x : s => (x : U)) :=
    (Subtype.val_injective.bijective_of_nat_card_le (by
      rw [show Nat.card s = 4 by simp only [Nat.card_eq_fintype_card,Fintype.card_coe,hsc]]
      exact pair_space_card_le_four U hp)).2
  intro v hv
  obtain ⟨x,hx⟩ := hsurj ⟨v,hv⟩
  have hm := x.property
  change (x : U) = ⟨v,hv⟩ at hx
  rw [hx] at hm
  simpa only [s,Finset.mem_insert,Finset.mem_singleton,Subtype.ext_iff,Submodule.coe_zero,Submodule.coe_add,va,vb] using hm

end MathieuCode.J4Fusion

namespace MathieuCode.J4Fusion
open Representation.BinaryOffender
private theorem exists_second_pair (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B)
    (A : PointPair) (hc : 2 < Nat.card U) :
    ∃ B : PointPair, pairVector B ∈ U ∧ B ≠ A := by
  classical
  by_contra hh
  have hc' : ∀ v ∈ U, v = 0 ∨ v = pairVector A := by
    intro v hv
    by_cases hv0 : v=0
    · exact Or.inl hv0
    obtain ⟨B,rfl⟩ := hp v hv hv0
    exact Or.inr (congrArg pairVector (by by_contra hn; exact hh ⟨B,hv,hn⟩))
  let f : U → Bool := fun v => decide (v.val = 0)
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    rcases hc' v v.property with hv | hv <;>
      rcases hc' w w.property with hw | hw
    · exact hv.trans hw.symm
    · change decide (v.val = 0) = decide (w.val = 0) at he
      rw [hv,hw] at he
      simp only [decide_true,pairVector_ne_zero,decide_false,Bool.true_eq_false] at he
    · change decide (v.val = 0) = decide (w.val = 0) at he
      rw [hv,hw] at he
      simp only [decide_true,pairVector_ne_zero,decide_false,Bool.false_eq_true] at he
    · exact hv.trans hw.symm
  have hb := Nat.card_le_card_of_injective f hf
  have hbool : Nat.card Bool = 2 := by simp
  omega

/-- A nontrivial pair plane with a distinguished pair has a third coordinate
fixed by its stabilizer inside the distinguished pair stabilizer. -/
theorem pair_plane_fixed_coordinate (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B)
    (A : PointPair) (ha : pairVector A ∈ U) (hc : 2 < Nat.card U) :
    ∃ i : Fin 24, i ∉ A.val ∧
      (cocodeVectorStabilizer cocodeRepresentation (pairVector A) ⊓
        subspaceStabilizer cocodeRepresentation U : Subgroup M24) ≤
          MulAction.stabilizer M24 i := by
  classical
  obtain ⟨B,hb,hBA⟩ := exists_second_pair U hp A hc
  have hsum : pairVector A + pairVector B ≠ 0 := by
    intro he
    have hh := congrArg (fun v : Cocode => v + pairVector B) he
    have hbb : pairVector B + pairVector B = 0 := by
      rw [←two_smul (ZMod 2),show (2 : ZMod 2) = 0 from rfl,zero_smul]
    rw [add_assoc,hbb,add_zero,zero_add] at hh
    exact hBA (pairVector_injective hh).symm
  obtain ⟨C,hC⟩ := hp _ (U.add_mem ha hb) hsum
  obtain ⟨i,hi,hiC⟩ := pair_external_singleton A B C hC
  have hiB : i ∈ B.val \ A.val := by rw [hi]; exact Finset.mem_singleton_self _
  refine ⟨i,(Finset.mem_sdiff.mp hiB).2,?_⟩
  intro g hg
  have hgA : mapPair g A = A := pairVector_injective ((pairVector_equivariant g A).symm.trans hg.1)
  have hgAv : g • A.val = A.val := congrArg Subtype.val hgA
  have hgB : pairVector (mapPair g B) ∈ U := by
    rw [←pairVector_equivariant]
    exact (hg.2 _).mpr hb
  have hcases := pair_space_elements U hp A B ha hb hBA.symm _ hgB
  have hBcases : mapPair g B = B ∨ mapPair g B = C := by
    rcases hcases with h0 | hA | hB | hBC
    · exact (pairVector_ne_zero _ h0).elim
    · have he : mapPair g B = mapPair g A := (pairVector_injective hA).trans hgA.symm
      exact (hBA (Subtype.ext (MulAction.injective g (congrArg Subtype.val he)))).elim
    · exact Or.inl (pairVector_injective hB)
    · exact Or.inr (pairVector_injective (hBC.trans hC))
  have hgiA : g • i ∉ A.val := by
    intro hh
    have hm := (MulAction.mem_stabilizer_finset.mp hgAv i).mp hh
    exact (Finset.mem_sdiff.mp hiB).2 hm
  have hgiB : g • i ∈ g • B.val := Finset.smul_mem_smul_finset (Finset.mem_sdiff.mp hiB).1
  have hfix : g • i = i := by
    rcases hBcases with he | he
    · have hev : g • B.val = B.val := congrArg Subtype.val he
      rw [hev] at hgiB
      have hm := Finset.mem_sdiff.mpr ⟨hgiB,hgiA⟩
      rw [hi] at hm
      exact Finset.mem_singleton.mp hm
    · have hev : g • B.val = C.val := congrArg Subtype.val he
      rw [hev] at hgiB
      have hm := Finset.mem_sdiff.mpr ⟨hgiB,hgiA⟩
      rw [hiC] at hm
      exact Finset.mem_singleton.mp hm
  exact hfix

/-- The source normalizer estimate follows from the actual M23 point
stabilizer embedding, preserving the distinguished Todd pair. -/
theorem pair_plane_stabilizer_rank_le_four (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B)
    (A : PointPair) (ha : pairVector A ∈ U) (hc : 2 < Nat.card U) :
    primeRank 2 (cocodeVectorStabilizer cocodeRepresentation (pairVector A) ⊓
      subspaceStabilizer cocodeRepresentation U : Subgroup M24) ≤ 4 := by
  obtain ⟨i,-,hi⟩ := pair_plane_fixed_coordinate U hp A ha hc
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 (24 : Fin 24) i
  let e := (MulAction.stabilizerEquivStabilizer hg.symm).symm.trans
    m23EquivM24PointStabilizer.symm
  have hr := Theory.GroupTheory.primeRank_le_of_injective 2
    (Subgroup.inclusion hi) (Subgroup.inclusion_injective hi)
  rw [Theory.GroupTheory.primeRank_equiv 2 e] at hr
  exact hr.trans m23_twoRank_le_four

end MathieuCode.J4Fusion

namespace MathieuCode.J4Fusion
open Representation.BinaryOffender

/-- The fixed ranks seven and six of AS91 (6.3)(a), from the already
classified native involutions. -/
theorem involution_fixed_finrank (s : M24) (hs : orderOf s = 2) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (zpowers s)) = 7 ∨
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (zpowers s)) = 6 := by
  have hd := fixedCodim_add_finrank cocodeRepresentation (zpowers s)
  rw [finrank_cocode] at hd
  rcases M24InvolutionCentralizers.involution_classes s hs with hz | ht
  · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_z s hz] at hd
    exact Or.inl (by omega)
  · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_t s ht] at hd
    exact Or.inr (by omega)

/-- Every involution in the marked pair-plane normalizer fixes seven
Todd dimensions: its fixed third coordinate excludes the fixed-point-free class. -/
theorem pair_plane_involution_fixed_finrank (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B)
    (A : PointPair) (ha : pairVector A ∈ U) (hc : 2 < Nat.card U)
    (s : M24) (hs : s ∈ cocodeVectorStabilizer cocodeRepresentation (pairVector A) ⊓
      subspaceStabilizer cocodeRepresentation U) (ho : orderOf s = 2) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (zpowers s)) = 7 := by
  obtain ⟨i,-,hi⟩ := pair_plane_fixed_coordinate U hp A ha hc
  have hz := CocodeOctad.Involutions.isConj_z_of_fixedPoint s ho ⟨i,hi hs⟩
  have hd := fixedCodim_add_finrank cocodeRepresentation (zpowers s)
  rw [finrank_cocode,CocodeOctad.Involutions.fixedCodim_of_isConj_z s hz] at hd
  omega

end MathieuCode.J4Fusion
