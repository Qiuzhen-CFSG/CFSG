module
public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.Frattini.BinarySquares
public import Theory.ElementaryAbelian.Quotient
public import Theory.Frattini.Intersection
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.Representation.AffineNine.QuaternionSource

/-!
# Normal elementary subgroups in the order-144 affine-nine case

An order-sixteen group embedded in GL₂(3) is a Sylow two-subgroup.
The semidihedral presentation puts every normal elementary subgroup in
its central involution, which is a square and hence lies in Frattini.

For a two-core-free group of order 144 with a normal elementary nine,
that nine has a Sylow two-complement and is self-centralizing. Conjugation
therefore embeds the complement in GL₂(3), giving the same conclusion
on each actual Sylow subgroup. No ambient group identification is assumed.

This is the Sylow obstruction needed for the small projective enlargement
in DGS, Groups and Graphs (1985), (10.7), pp.158--159; the semidihedral
presentation is the one in Alperin--Brauer--Gorenstein II.2, Lemma 1.
-/

public noncomputable section
open Subgroup
namespace Matrix.GeneralLinearGroup

/-- Every normal elementary subgroup of an order-sixteen group embedded in GL₂(3) lies in Frattini. -/
theorem normal_elementary_le_frattini_of_card_sixteen_embedding
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 16)
    (f : H →* GL (Fin 2) (ZMod 3)) (hf : Function.Injective f)
    (E : Subgroup H) [E.Normal] [IsElementaryAbelian 2 E] : E ≤ frattini H := by
  let U := f.range
  have hU : Nat.card U = 16 := (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans hH
  have hp : IsPGroup 2 U := IsPGroup.of_card (p := 2) (n := 4) hU
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hi : U.index = 3 := by
    have hc := U.card_mul_index
    rw [hU,hGL] at hc
    omega
  let T := hp.toSylow (by rw [hi]; decide)
  obtain ⟨S,n,hn,hS,a,b,ha,hb,hc,hg,_⟩ :=
    exists_semidihedral_sylow (ZMod 3) (by norm_num [Nat.card_zmod])
  have hSc : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,hGL]
    decide +kernel
  have hn4 : n = 4 := by
    have he : 2^n = 2^4 := hS.symm.trans hSc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) he
  subst n
  norm_num only at ha hc
  let e : H ≃* S := (MonoidHom.ofInjective hf).trans (T.equiv S)
  let D := E.map e.toMonoidHom
  let : D.Normal := (inferInstance : E.Normal).map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_surjective
    (e.toMonoidHom.subgroupMap E) (e.toMonoidHom.subgroupMap_surjective E)
  have hD : D ≤ frattini S := by
    by_cases hz : D = ⊥
    · rw [hz]; exact bot_le
    rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg D hz]
    apply zpowers_le.mpr
    rw [S.isPGroup'.frattini_eq_closure_squares]
    exact subset_closure ⟨a^2, by simp only [←pow_mul]⟩
  intro x hx
  have hh := hD (mem_map_of_mem e.toMonoidHom hx)
  rw [←frattini_map_equiv e] at hh
  obtain ⟨y,hy,he⟩ := hh
  exact e.injective he ▸ hy
end Matrix.GeneralLinearGroup

namespace Theory.GroupTheory
open Representation.AffineNine
/-- The order-144 affine-nine case has no normal elementary Sylow subgroup outside Frattini. -/
theorem normal_elementary_le_frattini_of_normal_nine
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 144)
    (N : Subgroup K) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hcore : pCore 2 K = ⊥)
    (S : Sylow 2 K) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] :
    E ≤ frattini S := by
  have hS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,hK]
    decide +kernel
  have hNS : N.IsComplement' (S : Subgroup K) := by
    apply isComplement'_of_coprime
    · rw [hN,hS,hK]
    · rw [hN,hS]; decide
  have hc := centralizer_eq_nine_of_twoCore_eq_bot N S S.isPGroup' hNS.sup_eq_top hcore
  let a := (MulAut.conjNormal : K →* MulAut N).comp (S : Subgroup K).subtype
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro s hs
    have hsN : (s : K) ∈ N := by
      rw [←hc,←MulAut.conjNormal_ker_eq_centralizer N]
      exact hs
    exact Subtype.ext (mem_bot.mp (hNS.disjoint.le_bot ⟨hsN,s.property⟩))
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) N (by rw [hN]; decide)
  exact Matrix.GeneralLinearGroup.normal_elementary_le_frattini_of_card_sixteen_embedding
    hS (f.comp a) (hf.comp ha) E
end Theory.GroupTheory
