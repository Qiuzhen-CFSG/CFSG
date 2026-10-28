module
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage00
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage01
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage02
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage03
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage04
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage05
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage06
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage07
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage08
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses.Coverage09
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# At most seven odd-order conjugacy classes in PSL₃(3)

Every determinant-one base-three matrix code has a kernel-checked conjugator
to one of twelve explicit matrices. Five have even order, leaving the identity,
two unipotent representatives and four powers of a Singer element. Transport
through the canonical `Matrix.PSL3Three.equiv` covers the odd-order elements
of the literal projective group. Their conjugacy-class image is contained in
a seven-element range; no class distinctness or representation theory is needed.

Source: the class-count input to Guralnick--Malle, *Classification of 2F-modules I*,
Proposition 4.2, manuscript pp.9--10. All finite witnesses are independently
checked in the descendants of this module; no external table is assumed.
-/

namespace Matrix.PSL3Three.OddClassCertificate

@[expose] public def oddRepresentative (i : Fin 7) : SL :=
  representative ⟨i.val, by omega⟩

private theorem code_coverage (c : MatrixCode) (hc : codeDet c = 1) :
    ∃ j : Fin 12, IsConj (finiteModelEquiv ⟨c, hc⟩) (representative j) := by
  by_cases h0 : c.val < 2048
  · exact Coverage00.covered c (by omega) h0 hc
  by_cases h1 : c.val < 4096
  · exact Coverage01.covered c (by omega) h1 hc
  by_cases h2 : c.val < 6144
  · exact Coverage02.covered c (by omega) h2 hc
  by_cases h3 : c.val < 8192
  · exact Coverage03.covered c (by omega) h3 hc
  by_cases h4 : c.val < 10240
  · exact Coverage04.covered c (by omega) h4 hc
  by_cases h5 : c.val < 12288
  · exact Coverage05.covered c (by omega) h5 hc
  by_cases h6 : c.val < 14336
  · exact Coverage06.covered c (by omega) h6 hc
  by_cases h7 : c.val < 16384
  · exact Coverage07.covered c (by omega) h7 hc
  by_cases h8 : c.val < 18432
  · exact Coverage08.covered c (by omega) h8 hc
  exact Coverage09.covered c (by omega) c.isLt hc

private theorem all_sl (g : SL) : ∃ j : Fin 12, IsConj g (representative j) := by
  let c := finiteModelEquiv.symm g
  have h := code_coverage c.val c.property
  simpa only [c, finiteModelEquiv.apply_symm_apply] using h

/-- Every odd-order special linear matrix is conjugate to one of seven matrices. -/
public theorem sl_odd_coverage
    (g : SL) (hg : ¬ 2 ∣ orderOf g) :
    ∃ i : Fin 7, IsConj g (oddRepresentative i) := by
  obtain ⟨j, hj⟩ := all_sl g
  have ho : orderOf g = orderOf (representative j) := by
    obtain ⟨k, hk⟩ := hj
    exact SemiconjBy.orderOf_eq (k : SL) hk
  have hlt : j.val < 7 := by
    by_contra h
    apply hg
    rw [ho]
    exact even_representative j (by omega)
  exact ⟨⟨j.val, hlt⟩, hj⟩

/-- Coverage in the literal projective group through the canonical quotient. -/
public theorem psl_odd_coverage
    (g : PSL) (hg : ¬ 2 ∣ orderOf g) :
    ∃ i : Fin 7, IsConj g (equiv (oddRepresentative i)) := by
  have hg' : ¬ 2 ∣ orderOf (equiv.symm g) := by
    rwa [equiv.symm.orderOf_eq]
  obtain ⟨i, hi⟩ := sl_odd_coverage (equiv.symm g) hg'
  refine ⟨i, ?_⟩
  have h : IsConj (equiv (equiv.symm g)) (equiv (oddRepresentative i)) :=
    equiv.toMonoidHom.map_isConj hi
  rwa [equiv.apply_symm_apply] at h

end Matrix.PSL3Three.OddClassCertificate

namespace Matrix.PSL3Three
open OddClassCertificate

/-- The native odd-order class bound used in the characteristic-two degree argument. -/
public theorem odd_conjClasses_card_le_seven :
    Nat.card (ConjClasses.mk '' {g : PSL | ¬ 2 ∣ orderOf g}) ≤ 7 := by
  let f : Fin 7 → ConjClasses PSL := fun i => ConjClasses.mk (equiv (oddRepresentative i))
  have hsub : ConjClasses.mk '' {g : PSL | ¬ 2 ∣ orderOf g} ⊆ Set.range f := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi⟩ := psl_odd_coverage g hg
    exact ⟨i, (ConjClasses.mk_eq_mk_iff_isConj.mpr hi).symm⟩
  calc
    Nat.card (ConjClasses.mk '' {g : PSL | ¬ 2 ∣ orderOf g}) ≤
        Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
    _ ≤ Nat.card (Fin 7) := Nat.card_le_card_of_surjective
      (Set.rangeFactorization f) Set.rangeFactorization_surjective
    _ = 7 := Nat.card_fin 7

end Matrix.PSL3Three
