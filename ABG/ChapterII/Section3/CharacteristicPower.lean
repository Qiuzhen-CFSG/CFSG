module
public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import ABG.ChapterII.Section3.QCharacteristicPower
public import ABG.ChapterII.Section2.InvolutionCentralizer

/-!
# The characteristic power of a QD-group

Every finite QD-group has a unique source characteristic power, and it is
the characteristic power of the centralizer of every involution. This is
ABG II.3 Definition 2 and its preceding independence discussion (article
p23, repository source page-024.tex).

The full involution-centralizer proposition supplies a Q-group with the
required Sylow shape. Its odd-core quotient has a unique characteristic
SL2 constituent, giving existence. All involutions are conjugate in a
QD-group. Conjugation gives an actual isomorphism of their centralizers;
transport of the odd core and characteristic constituent makes the chosen
power independent of the involution. Q-group uniqueness then proves
uniqueness for the original group.

These results use the preliminary SL2 definition exclusively. The final
GL2/GU2 characteristic parameters in the three main theorems remain a
separate downstream identification, so no main theorem is assumed here.
-/

namespace ABG
universe u

private def centralizerEquiv {G : Type u} [Group G] (e : G ≃* G) (x : G) :
    Subgroup.centralizer {x} ≃* Subgroup.centralizer {e x} where
  toFun a := ⟨e a, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_centralizer_singleton_iff.mp a.property))⟩
  invFun a := ⟨e.symm a, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp a.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv a := Subtype.ext (e.apply_symm_apply a)
  map_mul' a b := Subtype.ext (map_mul e (a : G) (b : G))

private theorem involutions_conjugate {G : Type u} [Group G]
    (hG : IsQDGroup G) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hG with ⟨_, _, _, _, hp⟩ | ⟨_, _, _, _, _, hp⟩ <;> exact hp.2.1
  obtain ⟨r, _, _, hc⟩ := hclass
  obtain ⟨i, hi⟩ := hc x hx
  obtain ⟨j, hj⟩ := hc y hy
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

/-- The source characteristic power is independent of the chosen involution. -/
public theorem HasSourceCharacteristicPower.at_involution
    {G : Type u} [Group G] (hG : IsQDGroup G) {q : ℕ}
    (hq : HasSourceCharacteristicPower G q) (y : G) (hy : orderOf y = 2) :
    HasSourceQCharacteristicPower (Subgroup.centralizer {y}) q := by
  obtain ⟨x, hx, hq⟩ := hq
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_conjugate hG hx hy)
  have h := hq.mulEquiv (centralizerEquiv (MulAut.conj g) x)
  have he : (MulAut.conj g) x = y := hg
  rwa [he] at h

/-- Every finite QD-group has a unique source-stage characteristic power. -/
public theorem exists_sourceCharacteristicPower
    {G : Type u} [Group G] [Finite G] (hG : IsQDGroup G) :
    ∃! q, HasSourceCharacteristicPower G q := by
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hG with ⟨_, _, _, _, hp⟩ | ⟨_, _, _, _, _, hp⟩ <;> exact hp.2.1
  obtain ⟨r, hr, _, _⟩ := hclass
  let x := r 0
  have hx : orderOf x = 2 := hr 0
  obtain ⟨hC, S, hS⟩ := qd_involutionCentralizer_isQGroup hG x hx
  obtain ⟨q, hq, huniq⟩ := exists_unique_sourceQCharacteristicPower hC S hS
  refine ⟨q, ⟨x, hx, hq⟩, ?_⟩
  intro q' hq'
  exact huniq q' (hq'.at_involution hG x hx)

end ABG

