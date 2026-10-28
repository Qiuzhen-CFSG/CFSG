module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFourSpace
public import Theory.GroupTheory.SolvableResidual.Transport
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions

/-!
# The original M22-code four-space normalizer action

The geometric code four-space recovers the quintet stabilizer. Native
five-point lifts in the inner M22 make the action of the original relative
normalizer surjective onto S5. Restricting to its actual solvable residual
then gives A5 on the same four-space. Both actions retain their pointwise
centralizers and the complete original component-map kernel.

The Chapter 12 pair constructs all markings and discharges the hypotheses.
The subsequent two-core identification uses its original central cover;
there is no assertion here that the full component kernel is a two-group.
Source: Aschbacher--Smith 8.2.6(2), H.16.3(2,4), printed pp.717,403,
refs/quasithin.pdf.
-/

public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer
open MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open MathieuCode.NormalizedShadowRows.M22CodeFourSpace
variable {G : Type*} [Group G]

/-- The literal relative normalizer has the full five-point action, retaining
its original covering kernel and pointwise centralizer. -/
theorem marked_normalizer_action
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* m22PairStabilizer) (hq : m22ToPairStabilizer.range ≤ q.range)
    (F : Additive W ≃ₗ[ZMod 2] M22Code)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        m22OuterCodeRepresentation (q l) (F (Additive.ofMul w)))
    (hspace : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ V4) :
    let N := L ⊓ normalizer (U : Set G)
    ∃ (f : N →* Q) (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5))),
      Function.Surjective (NaturalQuotient.q.comp f) ∧
      f.ker = q.ker.comap (inclusion (show N ≤ L from inf_le_left)) ∧
      (∀ l, (f l).val = q ⟨l,l.property.1⟩) ∧
      (NaturalQuotient.q.comp f).ker = (centralizer (U : Set G)).subgroupOf N ∧
      (∀ u : U, e u = Multiplicative.ofAdd (naturalMarking
        ⟨F (Additive.ofMul (inclusion hUW u)),(hspace _).mp u.property⟩)) ∧
      ∀ (n : N) (u : U),
        (e (U.normalizerMonoidHom ⟨n,n.property.2⟩ u)).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 5) (NaturalQuotient.q (f n)) (e u).toAdd := by
  let N := L ⊓ normalizer (U : Set G)
  have hn (l : L) : q l ∈ Q ↔ l.val ∈ normalizer (U : Set G) := by
    rw [←V4_stabilizer_eq_native]
    constructor
    · intro ht
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hh := (ht (F (Additive.ofMul ⟨x,hUW hx⟩))).mpr ((hspace _).mp hx)
        rw [←hF,←hspace] at hh
        exact hh
      · intro hx
        have hxW := (mem_normalizer_iff.mp (hLW l.property) x).mpr (hUW hx)
        apply (hspace ⟨x,hxW⟩).mpr
        apply (ht _).mp
        rw [←hF]
        exact (hspace _).mp hx
    · intro hl v
      obtain ⟨w,rfl⟩ := F.surjective v
      have he := hF l w.toMul
      simp only [ofMul_toMul] at he
      rw [←he,←hspace]
      have hp := hspace w.toMul
      simp only [ofMul_toMul] at hp
      rw [←hp]
      exact (mem_normalizer_iff.mp hl w.toMul.val).symm
  let j : N →* L := inclusion inf_le_left
  let f : N →* Q := (q.comp j).codRestrict _ (fun n => (hn (j n)).mpr n.property.2)
  let e₀ : U →* Multiplicative V4 := {
    toFun u := Multiplicative.ofAdd ⟨F (Additive.ofMul (inclusion hUW u)),(hspace _).mp u.property⟩
    map_one' := by apply Subtype.ext; exact F.map_zero
    map_mul' u v := by
      apply Subtype.ext
      change F (Additive.ofMul (inclusion hUW (u*v))) = _
      rw [map_mul]
      exact F.map_add _ _ }
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro u v he
      apply Subtype.ext
      have he' : F (Additive.ofMul (inclusion hUW u)) =
          F (Additive.ofMul (inclusion hUW v)) := congrArg (fun w : Multiplicative V4 => w.toAdd.val) he
      exact congrArg (fun w : Additive W => w.toMul.val) (F.injective he')
    · intro v
      obtain ⟨w,hw⟩ := F.surjective v.toAdd.val
      have hu : w.toMul.val ∈ U := (hspace w.toMul).mpr (hw.symm ▸ v.toAdd.property)
      exact ⟨⟨w.toMul,hu⟩,Subtype.ext hw⟩
  let e := (MulEquiv.ofBijective e₀ he₀).trans naturalMarking.toAddEquiv.toMultiplicative
  refine ⟨f,e,?_,?_,fun _ => rfl,?_,fun _ => rfl,?_⟩
  · intro τ
    obtain ⟨g,hg,h0⟩ := M22ChapterH.Quintet.q_lift τ
    obtain ⟨l,hl⟩ := hq ((m22ToPairStabilizer_mem_range_iff_fixed_zero g.val).mpr h0)
    have hlN : l.val ∈ N := ⟨l.property,(hn l).mp (hl.symm ▸ g.property)⟩
    refine ⟨⟨l,hlN⟩,?_⟩
    change NaturalQuotient.q (f ⟨l,hlN⟩) = τ
    have he : f ⟨l,hlN⟩ = g := Subtype.ext hl
    rw [he,hg]
  · ext n
    exact Subtype.ext_iff
  · ext n
    change NaturalQuotient.q (f n) = 1 ↔ n.val ∈ centralizer (U : Set G)
    rw [←quotient_trivial_iff NaturalQuotient.q NaturalQuotient.marking
      NaturalQuotient.marking_equivariant,←fixes_annihilator_iff]
    constructor
    · intro hf
      rw [mem_centralizer_iff]
      intro u hu
      have he := (hF (j n) ⟨u,hUW hu⟩).trans (hf _ ((hspace _).mp hu))
      have hc : n.val * u * n.val⁻¹ = u :=
        congrArg (fun w : Additive W => w.toMul.val) (F.injective he)
      exact (mul_inv_eq_iff_eq_mul).mp hc |>.symm
    · intro hc v hv
      obtain ⟨w,rfl⟩ := F.surjective v
      have hu : w.toMul.val ∈ U := (hspace w.toMul).mpr hv
      change m22OuterCodeRepresentation (q (j n)) (F w) = F w
      have he := hF (j n) w.toMul
      simp only [ofMul_toMul] at he
      rw [←he]
      apply congrArg F
      apply Additive.ofMul.injective.eq_iff.mpr
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_iff.mp hc _ hu).symm
  · intro n u
    change naturalMarking ⟨F (Additive.ofMul (inclusion hUW
      (U.normalizerMonoidHom ⟨n,n.property.2⟩ u))),_⟩ = _
    have he : (⟨F (Additive.ofMul (inclusion hUW
        (U.normalizerMonoidHom ⟨n,n.property.2⟩ u))),
          (hspace _).mp (U.normalizerMonoidHom ⟨n,n.property.2⟩ u).property⟩ : V4) =
        V4Subrepresentation.toRepresentation (f n)
          ⟨F (Additive.ofMul (inclusion hUW u)),(hspace _).mp u.property⟩ := by
      apply Subtype.ext
      exact hF (j n) (inclusion hUW u)
    exact (congrArg naturalMarking he).trans
      (naturalMarking_equivariant (f n)
        ⟨F (Additive.ofMul (inclusion hUW u)),(hspace _).mp u.property⟩)


private theorem symmetric_residual :
    solvableResidual (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply le_antisymm
  · have h := solvableResidual_le_derivedSeries (G := Equiv.Perm (Fin 5)) 1
    rw [derivedSeries_one] at h
    exact h.trans_eq (alternatingGroup.commutator_perm_eq (by simp))
  · exact le_solvableResidual_of_isPerfect _

/-- The solvable residual acts as the actual alternating five-point group.
Its pointwise kernel is retained; no two-core identification is assumed. -/
theorem residual_action [Finite G]
    (L U : Subgroup G)
    (p : (L ⊓ normalizer (U : Set G) : Subgroup G) →* Equiv.Perm (Fin 5))
    (hp : Function.Surjective p)
    (hk : p.ker = (centralizer (U : Set G)).subgroupOf (L ⊓ normalizer (U : Set G)))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
    (he : ∀ (n : (L ⊓ normalizer (U : Set G) : Subgroup G)) (u : U),
      (e (U.normalizerMonoidHom ⟨n,n.property.2⟩ u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 5) (p n) (e u).toAdd) :
    let R := Chapter8.Section02.Normalizer.localResidual L U
    ∃ r : R →* alternatingGroup (Fin 5), Function.Surjective r ∧
      r.ker = (centralizer (U : Set G)).subgroupOf R ∧
      (∀ x, (r x).val = p (inclusion (Chapter8.Section02.Normalizer.localResidual_le L U) x)) ∧
      ∀ (x : R) (u : U),
        (e (U.normalizerMonoidHom
          ⟨x,(Chapter8.Section02.Normalizer.localResidual_le L U x.property).2⟩ u)).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 5) (r x).val (e u).toAdd := by
  let N := L ⊓ normalizer (U : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let b : solvableResidual N ≃* R :=
    (solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective
  let j := inclusion (Chapter8.Section02.Normalizer.localResidual_le L U)
  let a := MulEquiv.subgroupCongr symmetric_residual
  let r : R →* alternatingGroup (Fin 5) :=
    a.toMonoidHom.comp (p.solvableResidualMap.comp b.symm.toMonoidHom)
  have hb (x : R) : (b.symm x).val = j x := by
    apply Subtype.ext
    exact congrArg (fun y : R => (y : G)) (b.apply_symm_apply x)
  have hr (x : R) : (r x).val = p (j x) := by
    change p (b.symm x).val = _
    rw [hb]
  refine ⟨r,a.surjective.comp ((p.solvableResidualMap_surjective hp).comp b.symm.surjective),
    ?_,hr,?_⟩
  · ext x
    change r x = 1 ↔ x.val ∈ centralizer (U : Set G)
    rw [Subtype.ext_iff,hr]
    exact SetLike.ext_iff.mp hk (j x)
  · intro x u
    rw [hr]
    exact he (j x) u

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer
