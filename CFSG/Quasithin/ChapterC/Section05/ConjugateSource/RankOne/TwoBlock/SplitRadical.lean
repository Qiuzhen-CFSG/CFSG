module
public import Theory.GroupTheory.Gaschutz
public import Theory.GroupTheory.PPerfectHom
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.RelativeComplementProjection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The splitting step for the actual elementary radical

A normal subgroup supplemented by an elementary abelian group splits over
the intersection by a vector-space complement. Gaschütz extends this local
splitting from a Sylow subgroup. The crossed retraction of that complement
then shows that a two-perfect subgroup meets the radical only in its
commutator layer. Central layers of the original module are retained.

Source: Aschbacher–Smith, C.5.6(7), printed p.159, applying A.1.39.
-/
public section
open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G]

/-- A two-perfect subgroup meets a split abelian two-radical in its
commutator layer. The layer need not itself be a complement. -/
theorem split_radical_intersection_le (Q A K U : Subgroup G)
    [Q.Normal] [IsMulCommutative Q] (hQ : IsPGroup 2 Q)
    (hc : Q.IsComplement' A) (hK : IsPPerfect 2 K)
    (hcomm : ⁅K,Q⁆ ≤ U) : K ⊓ Q ≤ U := by
  let f : G → Q := fun g => (hc.equiv g).1
  have hf (x y : G) : f (x*y) = f x * MulAut.conjNormal x (f y) := by
    calc
      (hc.equiv (x * y)).1 = (hc.equiv (x * (hc.equiv y).1)).1 := by
        conv_lhs => rw [← hc.equiv_fst_mul_equiv_snd y, ← mul_assoc, hc.equiv_mul_right]
      _ = (hc.equiv ((MulAut.conjNormal x (hc.equiv y).1 : Q) * x)).1 := by
        congr 2
        simp [mul_assoc]
      _ = MulAut.conjNormal x (hc.equiv y).1 * (hc.equiv x).1 := by
        rw [hc.equiv_mul_left]
      _ = (hc.equiv x).1 * MulAut.conjNormal x (hc.equiv y).1 := mul_comm _ _
  have hfQ (q : Q) : f q = q := hc.equiv_fst_eq_self_of_mem_of_one_mem A.one_mem q.property
  let q := QuotientGroup.mk' (U.subgroupOf Q)
  have hact (k : K) (v : Q) : q (MulAut.conjNormal (k : G) v) = q v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (k : G) * (v : G) * (k : G)⁻¹ / (v : G) ∈ U
    simpa only [div_eq_mul_inv,commutatorElement_def] using hcomm (commutator_mem_commutator k.property v.property)
  let d : K →* Q ⧸ U.subgroupOf Q := {
    toFun := fun k => q (f k)
    map_one' := by
      have he := hfQ 1
      simpa only [OneMemClass.coe_one,map_one] using congrArg q he
    map_mul' := by
      intro k l
      rw [Subgroup.coe_mul,hf,map_mul,hact] }
  have hd := hK.hom_eq_one_of_isPGroup (hQ.of_surjective q (QuotientGroup.mk'_surjective _)) d
  rintro k ⟨hkK,hkQ⟩
  have he := DFunLike.congr_fun hd (⟨k,hkK⟩ : K)
  change q (f k) = 1 at he
  rw [hfQ ⟨k,hkQ⟩] at he
  have hm : (⟨k,hkQ⟩ : Q) ∈ U.subgroupOf Q := (QuotientGroup.eq_one_iff _).mp he
  exact hm

/-- A vector-space complement in the elementary supplement splits the
normal subgroup, without requiring trivial intersection of the given factors. -/
theorem exists_complement_of_elementary_supplement
    (Q V : Subgroup G) [Q.Normal] [IsElementaryAbelian 2 V]
    (hspan : Q ⊔ V = ⊤) : ∃ A : Subgroup G, Q.IsComplement' A := by
  obtain ⟨B,hB⟩ := IsElementaryAbelian.exists_isCompl 2 V (Q.subgroupOf V)
  let A := B.map V.subtype
  have hdis : Disjoint Q A := by
    apply disjoint_def.mpr
    rintro a haQ ⟨b,hb,rfl⟩
    exact congrArg Subtype.val (disjoint_def.mp hB.disjoint haQ hb)
  have hVA : V ≤ Q ⊔ A := by
    have he := congrArg (map V.subtype) hB.sup_eq_top
    rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at he
    rw [← he]
    apply sup_le ?_ le_sup_right
    rintro _ ⟨v,hv,rfl⟩
    exact mem_sup_left hv
  have hQA : Q ⊔ A = ⊤ := top_unique (hspan ▸ sup_le le_sup_left hVA)
  refine ⟨A,isComplement'_of_disjoint_and_mul_eq_univ hdis ?_⟩
  rw [← coe_mul_of_right_le_normalizer_left Q A (by simp only [Q.normalizer_eq_top,le_top]),hQA]
  rfl

/-- Gaschütz applies to the actual radical and the actual Sylow supplement. -/
theorem radical_intersection_le_of_sylow_supplement [Finite G]
    (Q K U V : Subgroup G) [Q.Normal] [IsMulCommutative Q]
    [IsElementaryAbelian 2 V] (hQ : IsPGroup 2 Q)
    (hK : IsPPerfect 2 K) (hcomm : ⁅K,Q⁆ ≤ U)
    (P : Sylow 2 G) (hV : V ≤ P) (hspan : (P : Subgroup G) = Q ⊔ V) :
    K ⊓ Q ≤ U := by
  have hQP : Q ≤ P := hspan ▸ le_sup_left
  have hlocal : ∃ A : Subgroup P, (Q.subgroupOf (P : Subgroup G)).IsComplement' A := by
    let : IsElementaryAbelian 2 (V.subgroupOf (P : Subgroup G)) :=
      IsElementaryAbelian.subgroupOf hV
    apply exists_complement_of_elementary_supplement (Q.subgroupOf (P : Subgroup G))
      (V.subgroupOf (P : Subgroup G))
    rw [← subgroupOf_sup hQP hV,← hspan,subgroupOf_self]
  obtain ⟨A,hA⟩ := (Q.exists_complement_iff_sylow hQ P).mpr hlocal
  exact split_radical_intersection_le Q A K U hQ hA hK hcomm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
