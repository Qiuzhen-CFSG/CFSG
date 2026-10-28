module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReflectionSelection
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalReflection
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels

/-!
# Natural-root reflection choice on the original marked endpoint

Apply the natural-kernel reflection calculation to a literal endpoint of
the universal reduced amalgam. The quotient is its original quotient by
O₂, marked by SL₂ coordinates. The chosen involution belongs to an actual
path radical. The constructed reflection fixes its marked endpoint, moves
the other endpoint, normalizes the whole original Cartan, and is conjugate
inside that endpoint to the same path-root involution.

The full radius-one permutation kernel is handled separately: its image
is normal and lies in the marked upper triangular Borel, hence is trivial.
Its intersection with the odd Cartan is therefore trivial. This proves
the required Cartan/local-kernel centralization for this branch without
identifying the full local kernel with O₂ in the general setup.

This specialized result assumes SL₂ on the full endpoint quotient.
Chapter 10's natural action on a smaller local actor does not automatically
supply that hypothesis. The actor/full-Cartan transport, the remaining
reflection cases, the corrected (14.14)--(14.19) alternatives and quotient
root signs remain source obligations.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--156, and
(14.2), pp.210--211, with the universal tree convention of (14.0), p.208.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F : Type*} [Field F] [CharP F 2]

private theorem reflection_middle_eq : originalMiddle (reducedAmalgam L S) =
    Universal.cosetFamily (reducedAmalgam L S) false ⊓
      Universal.cosetFamily (reducedAmalgam L S) true :=
  (Universal.overlap_eq _ (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).symm

private theorem reflection_middle_le (i : Bool) :
    originalMiddle (reducedAmalgam L S) ≤ reflectionEndpoint L S i := by
  rw [reflection_middle_eq]
  cases i
  · exact inf_le_left
  · exact inf_le_right

/-- A marked SL₂ quotient with upper triangular Borel kills the image of
the actual radius-one permutation kernel. Relative normality is used. -/
theorem natural_localKernel_image_eq_bot (i : Bool)
    (π : reflectionEndpoint L S i →* SL(2,F)) (honto : Function.Surjective π)
    (htri : ∀ z : reflectionEndpoint L S i,
      (z : (reducedAmalgam L S).Universal)∈originalMiddle (reducedAmalgam L S) →
      (π z).val 1 0=0) :
    (((RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1).subgroupOf
        (reflectionEndpoint L S i)).map π)=⊥ := by
  let A := reducedAmalgam L S
  let P := reflectionEndpoint L S i
  let M := RankTwo.ballKernel (Universal.cosetFamily A) (base (Universal.cosetFamily A) i) 1
  have hn : P ≤ normalizer (M : Set A.Universal) := by
    simpa only [RankTwo.stabilizer,stabilizer_base] using
      RankTwo.stabilizer_le_normalizer_ballKernel (Universal.cosetFamily A)
        (base (Universal.cosetFamily A) i) 1
  let : (M.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  let : ((M.subgroupOf P).map π).Normal := by
    constructor
    rintro y ⟨x,hx,rfl⟩ g
    obtain ⟨u,rfl⟩ := honto g
    exact ⟨u*x*u⁻¹,(inferInstance : (M.subgroupOf P).Normal).conj_mem x hx u,
      by simp only [map_mul,map_inv]⟩
  apply normal_triangular_eq_bot
  rintro z ⟨x,hx,rfl⟩
  apply htri x
  have hadj : (sourceGraph A).Adj (base (Universal.cosetFamily A) i)
      (base (Universal.cosetFamily A) (!i)) := ⟨by change i≠!i; cases i <;> decide,incident_base _ _ _⟩
  have hh := RankTwo.ballKernel_one_le_edge (Universal.cosetFamily A) hadj hx
  simp only [RankTwo.stabilizer,stabilizer_base] at hh
  rw [reflection_middle_eq]
  cases i
  · exact hh
  · exact ⟨hh.2,hh.1⟩

variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

include h in
/-- Choose an actual reflection from a marked natural local profile and an
involution in the original path radical. The conjugator remains in the
same endpoint, and the full Cartan/local-kernel centralization clause holds. -/
theorem source_natural_root_reflection (i : Bool)
    (e : reflectionQuotient L S i ≃* SL(2,F))
    (d : NaturalKernel (e.toMonoidHom.comp (reflectionQuotientMap L S i)))
    (hdiag : ∀ k : reflectionEndpoint L S i, (k : (reducedAmalgam L S).Universal)∈cartan c →
      ∃ b : F, ∃ hb : b≠0, e (reflectionQuotientMap L S i k)=Matrix.SpecialLinearGroup.diag2 b hb)
    (htri : ∀ k : reflectionEndpoint L S i,
      (k : (reducedAmalgam L S).Universal)∈originalMiddle (reducedAmalgam L S) →
      (e (reflectionQuotientMap L S i k)).val 1 0=0)
    {v : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk v
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (x : reflectionEndpoint L S i)
    (hxR : (x : (reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal) p)
    (hx : x*x=1) (a : F) (ha : a≠0)
    (hπx : e (reflectionQuotientMap L S i x)=upper a) :
    ∃ t : (reducedAmalgam L S).Universal,
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i=
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t=1 ∧ t∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) p,
        orderOf y=2 ∧ ∃ g∈reflectionEndpoint L S i, g*y*g⁻¹=t) ∧
      ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  let A := reducedAmalgam L S
  let P := reflectionEndpoint L S i
  let K := (cartan c).subgroupOf P
  let π := e.toMonoidHom.comp (reflectionQuotientMap L S i)
  have honto : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  let : Finite P := by
    change Finite (Universal.cosetFamily A i)
    rw [←stabilizer_base (Universal.cosetFamily A) i]
    exact source_vertexStabilizer_finite _ _
  have hKP : cartan c ≤ P := (cartan_le c).trans (reflection_middle_le i)
  have hodd : Nat.Coprime 2 (Nat.card K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKP).toEquiv]
    exact cartan_odd c
  let := cartan_abelian h c
  let : IsMulCommutative K := IsMulCommutative.of_comm fun x y =>
    (subgroupOfEquivOfLe hKP).injective (by simp only [map_mul]; exact mul_comm' _ _)
  let : Group.IsSolvable K := Group.isSolvable_of_comm (mul_comm' (M := K))
  obtain ⟨t,ht,htsq,_,hπt,g,hg⟩ := d.exists_diagonal_cartan_reflection honto K hodd
    hdiag x hx a ha hπx
  have hnot : (t:A.Universal)∉originalMiddle A := by
    intro hb
    have hh := htri t hb
    change (π t).val 1 0=0 at hh
    rw [hπt,braid_matrix a ha] at hh
    exact inv_ne_zero ha hh
  have hfix : (t:A.Universal) • base (Universal.cosetFamily A) i=base (Universal.cosetFamily A) i := by
    have hh := t.property
    change (t:A.Universal)∈Universal.cosetFamily A i at hh
    rwa [←stabilizer_base (Universal.cosetFamily A) i] at hh
  have hmove : (t:A.Universal) • base (Universal.cosetFamily A) (!i)≠base (Universal.cosetFamily A) (!i) := by
    intro he
    apply hnot
    have hh : (t:A.Universal)∈Universal.cosetFamily A (!i) := by rw [←stabilizer_base (Universal.cosetFamily A) (!i)]; exact he
    rw [reflection_middle_eq]
    cases i
    · exact ⟨t.property,hh⟩
    · exact ⟨hh,t.property⟩
  have hnorm : (t:A.Universal)∈normalizer (cartan c : Set A.Universal) := by
    have hh := K.le_normalizer_map P.subtype (mem_map_of_mem P.subtype ht)
    have heK : K.map P.subtype=cartan c := map_subgroupOf_eq_of_le hKP
    rwa [heK] at hh
  refine ⟨t,hfix,hmove,congrArg Subtype.val htsq,hnorm,?_,?_⟩
  · refine ⟨x,hxR,?_,g,g.property,congrArg Subtype.val hg⟩
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime (show x^2=1 by simpa only [pow_two] using hx)
    intro he
    have hh := congrArg (fun z : SL(2,F) => z.val 0 1) hπx
    rw [he,map_one,map_one] at hh
    change (1 : SL(2,F)).val 0 1=(upper a).val 0 1 at hh
    have hz : (0:F)=a := by simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh
    exact ha hz.symm
  · intro z hzK hzM
    let zP : P := ⟨z,hKP hzK⟩
    have hM := natural_localKernel_image_eq_bot i π honto htri
    have hzker : zP∈π.ker := by
      apply (Subgroup.map_eq_bot_iff _).mp hM
      exact hzM
    have hdis : K ⊓ π.ker=⊥ := by
      obtain ⟨n,hn⟩ := d.isTwo.exists_card_eq
      exact (disjoint_of_coprime_natCard (by rw [hn]; exact hodd.symm.pow_right n)).eq_bot
    have hm : zP∈K ⊓ π.ker := ⟨hzK,hzker⟩
    rw [hdis] at hm
    have hz : z=1 := congrArg Subtype.val (show zP=1 from hm)
    rw [hz]
    exact Commute.one_right _

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
