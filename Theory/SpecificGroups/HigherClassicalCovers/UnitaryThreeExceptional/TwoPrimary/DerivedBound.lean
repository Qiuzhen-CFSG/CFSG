module

public import Theory.GroupTheory.Commutator.CentralIndexFourDerivedBound
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.Wreath
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution

/-!
# Derived kernels above an index-four binary central product

Let B be the concrete binary tetrahedral group and j : B × B → C have
normal range of index four and kernel of order two. Every finite central
two-extension g : D → C satisfies |ker(g) ∩ D'| ≤ 4.

Lift the two factors and their commutation through the central two-kernel.
Their common image R is two-perfect, so normalizer lifting makes R normal
in D. Moreover ker(g) ∩ R is the image of ker(j), of order at most two.
Modulo R the image of ker(g) is central of index four, and the generic
derived bound supplies the second factor of two.

The specialization uses the literal full projective involution centralizer
in PSU₄(3). Its binary map and three model facts remain explicit; they are
supplied by the independent model construction. This is the local
calculation for the two-primary upper bound in Aschbacher--Smith I.1.4(5),
printed p.408 of `refs/quasithin.pdf`, and GLS3 §6.1. The complete multiplier
statement, including its structure and three-primary part, is separate.
-/

public section

open Subgroup GLS3.Chapter5.SchurPresentation
open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary

private theorem binary_product_isTwoPerfect :
    IsPPerfect 2 (BinaryTetrahedral × BinaryTetrahedral) := by
  intro N hN hp
  let := hN
  let q := QuotientGroup.mk' N
  have hl := binary_hom_eq_one hp (q.comp (MonoidHom.inl _ _))
  have hr := binary_hom_eq_one hp (q.comp (MonoidHom.inr _ _))
  apply top_unique
  intro b _
  apply (QuotientGroup.eq_one_iff b).mp
  change q b = 1
  have hl' : q (b.1, 1) = 1 := DFunLike.congr_fun hl b.1
  have hr' : q (1, b.2) = 1 := DFunLike.congr_fun hr b.2
  calc
    q b = q ((b.1, 1) * (1, b.2)) := by simp
    _ = q (b.1, 1) * q (1, b.2) := map_mul q _ _
    _ = 1 := by rw [hl', hr', mul_one]

/-- Both literal binary factors lift simultaneously through a central two-kernel. -/
theorem exists_binary_product_lift {D C : Type*} [Group D] [Group C]
    (g : D →* C) (hg : Function.Surjective g)
    (hc : g.ker ≤ center D) (hk : IsPGroup 2 g.ker)
    (j : (BinaryTetrahedral × BinaryTetrahedral) →* C) :
    ∃ s : (BinaryTetrahedral × BinaryTetrahedral) →* D, g.comp s = j := by
  obtain ⟨l, hl⟩ := exists_binary_lift g hg hc hk (j.comp (MonoidHom.inl _ _))
  obtain ⟨r, hr⟩ := exists_binary_lift g hg hc hk (j.comp (MonoidHom.inr _ _))
  have hl' (x) : g (l x) = j (x, 1) := DFunLike.congr_fun hl x
  have hr' (x) : g (r x) = j (1, x) := DFunLike.congr_fun hr x
  have hcomm (x y) : Commute (l x) (r y) := binary_lifts_commute g hc hk l r
    (fun a b => by
      rw [hl', hr']
      exact (show Commute (a, (1 : BinaryTetrahedral)) (1, b) by
        change (a, (1 : BinaryTetrahedral)) * (1, b) = (1, b) * (a, 1)
        simp).map j) x y
  let s : (BinaryTetrahedral × BinaryTetrahedral) →* D := {
    toFun x := l x.1 * r x.2
    map_one' := by simp
    map_mul' x y := by
      change l (x.1*y.1)*r (x.2*y.2) = (l x.1*r x.2)*(l y.1*r y.2)
      rw [map_mul, map_mul]
      calc
        (l x.1*l y.1)*(r x.2*r y.2) = l x.1*(l y.1*r x.2)*r y.2 := by group
        _ = (l x.1*r x.2)*(l y.1*r y.2) := by rw [(hcomm y.1 x.2).eq]; group }
  refine ⟨s, ?_⟩
  apply MonoidHom.ext
  intro x
  change g (l x.1 * r x.2) = j x
  rw [map_mul, hl', hr', ← map_mul]
  simp

/-- An index-four normal binary central product bounds the derived part
of every central two-kernel by four. Neither group need be perfect. -/
theorem card_ker_inf_commutator_le_four_of_binary_product
    {C D : Type*} [Group C] [Finite C] [Group D] [Finite D]
    (j : (BinaryTetrahedral × BinaryTetrahedral) →* C)
    (hjn : j.range.Normal) (hjk : Nat.card j.ker = 2) (hji : j.range.index = 4)
    (g : D →* C) (hg : Function.Surjective g)
    (hc : g.ker ≤ center D) (hk : IsPGroup 2 g.ker) :
    Nat.card (g.ker ⊓ _root_.commutator D : Subgroup D) ≤ 4 := by
  let := hjn
  obtain ⟨s, hs⟩ := exists_binary_product_lift g hg hc hk j
  have hR : IsPPerfect 2 s.range :=
    binary_product_isTwoPerfect.of_surjective s.rangeRestrict s.rangeRestrict_surjective
  have hm : s.range.map g = j.range := by
    rw [← MonoidHom.range_comp, hs]
  have hn : s.range.Normal := by
    apply normalizer_eq_top_iff.mp
    rw [← comap_normalizer_map_of_pPerfect g s.range hR hk
      (hc.trans (center_le_normalizer _)), hm, normalizer_eq_top, comap_top]
  let := hn
  have hindex : (g.ker ⊔ s.range).index = 4 := by
    rw [sup_comm, ← comap_map_eq, hm, j.range.index_comap_of_surjective hg]
    exact hji
  have hsmall : Nat.card (g.ker ⊓ s.range : Subgroup D) ≤ 2 := by
    have heq : g.ker ⊓ s.range = j.ker.map s := by
      apply le_antisymm
      · rintro x ⟨hx, b, rfl⟩
        refine ⟨b, ?_, rfl⟩
        change j b = 1
        exact (DFunLike.congr_fun hs b).symm.trans hx
      · rintro _ ⟨b, hb, rfl⟩
        refine ⟨?_, ⟨b, rfl⟩⟩
        change g (s b) = 1
        exact (DFunLike.congr_fun hs b).trans hb
    rw [heq]
    exact (Nat.le_of_dvd (by omega : 0 < Nat.card j.ker)
      (j.ker.card_map_dvd s)).trans_eq hjk
  have hb := card_inf_commutator_le_of_central_index_four_mod_normal
    g.ker s.range hc hindex
  exact hb.trans (by omega)

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

/-- The local calculation for the literal standard projective involution
centralizer. The independent binary-model calculation supplies exactly
`j`, its normal range, its order-two kernel and its index-four range. -/
theorem standardCentralizer_card_ker_inf_commutator_le_four
    (j : (BinaryTetrahedral × BinaryTetrahedral) →* standardCentralizer)
    (hjn : j.range.Normal) (hjk : Nat.card j.ker = 2) (hji : j.range.index = 4)
    {D : Type*} [Group D] [Finite D]
    (g : D →* standardCentralizer) (hg : Function.Surjective g)
    (hc : g.ker ≤ center D) (hk : IsPGroup 2 g.ker) :
    Nat.card (g.ker ⊓ _root_.commutator D : Subgroup D) ≤ 4 :=
  card_ker_inf_commutator_le_four_of_binary_product j hjn hjk hji g hg hc hk

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary
