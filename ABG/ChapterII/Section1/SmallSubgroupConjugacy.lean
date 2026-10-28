module
public import ABG.ChapterII.Section1.SmallSubgroups
public import Theory.GroupTheory.SubgroupConjugacy

/-!
# Ambient conjugacy of small subgroups inside a quasi-dihedral subgroup

Let `P` be a quasi-dihedral subgroup of an ambient group. Two Klein four
subgroups contained in `P`, or two quaternion subgroups of order eight
contained in `P`, are conjugate by an element of `P`. The conclusion is an
equality of subgroups of the ambient group, oriented from `V` to `U`.
No Sylow or ambient finiteness hypothesis is needed.

View `U` and `V` as their actual `subgroupOf P` subgroups. The canonical
subgroup equivalences transport the Klein four or quaternion property.
Lemma II.1.1(ii) supplies conjugators from a common representative; composing
one with the inverse of the other sends `V` to `U`. Mapping this equality
along `P.subtype` gives the ambient conclusion, since inclusion commutes
with conjugation by an element of `P`.

This is the ambient form of Alperin–Brauer–Gorenstein, Chapter II, §1,
Lemma 1(ii), article p.9 of `refs/latex/alperin-brauer-gorenstein.tex`.
It supplies the representative change used in the normalizer-fusion
argument for Proposition 1, article pp.10–11.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem ambient_of_internal (P U V : Subgroup G) (hUP : U ≤ P) (hVP : V ≤ P)
    (h : ∃ s : P, (V.subgroupOf P).map (MulAut.conj s).toMonoidHom = U.subgroupOf P) :
    ∃ s : P, V.map (MulAut.conj (s : G)).toMonoidHom = U := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_⟩
  have hm := congrArg (fun W : Subgroup P => W.map P.subtype) hs
  have he : P.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : G)).toMonoidHom.comp P.subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, he, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hVP, Subgroup.map_subgroupOf_eq_of_le hUP] at hm
  exact hm

/-- Two subgroups of the same small type inside `P` are ambient conjugates by an element of `P`. -/
public theorem small_subgroup_ambient_conjugacy (P U V : Subgroup G)
    (hP : Stellmacher.IsSemidihedralGroup P) (hUP : U ≤ P) (hVP : V ≤ P)
    (hUV : (IsKleinFour U ∧ IsKleinFour V) ∨
      (Nonempty (U ≃* QuaternionGroup 2) ∧ Nonempty (V ≃* QuaternionGroup 2))) :
    ∃ s : P, V.map (MulAut.conj (s : G)).toMonoidHom = U := by
  apply ambient_of_internal P U V hUP hVP
  let eU := Subgroup.subgroupOfEquivOfLe hUP
  let eV := Subgroup.subgroupOfEquivOfLe hVP
  obtain ⟨R, Q, _, _, hfour, hquaternion, _⟩ := four_quaternion_subgroups hP
  rcases hUV with ⟨hU, hV⟩ | ⟨⟨fU⟩, ⟨fV⟩⟩
  · have hU' : IsKleinFour (U.subgroupOf P) := {
      card_four := (Nat.card_congr eU.toEquiv).trans hU.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eU).trans hU.exponent_two }
    have hV' : IsKleinFour (V.subgroupOf P) := {
      card_four := (Nat.card_congr eV.toEquiv).trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).trans hV.exponent_two }
    exact Subgroup.conjugate_of_same_class R _ _ (hfour _ hU') (hfour _ hV')
  · exact Subgroup.conjugate_of_same_class Q _ _ (hquaternion _ ⟨eU.trans fU⟩)
      (hquaternion _ ⟨eV.trans fV⟩)

/-- Ambient Klein four subgroups contained in a quasi-dihedral subgroup are conjugate inside it. -/
public theorem four_subgroup_ambient_conjugacy (P U V : Subgroup G)
    (hP : Stellmacher.IsSemidihedralGroup P) (hUP : U ≤ P) (hVP : V ≤ P)
    (hU : IsKleinFour U) (hV : IsKleinFour V) :
    ∃ s : P, V.map (MulAut.conj (s : G)).toMonoidHom = U :=
  small_subgroup_ambient_conjugacy P U V hP hUP hVP (Or.inl ⟨hU, hV⟩)

/-- Ambient quaternion subgroups of order eight contained in `P` are conjugate inside `P`. -/
public theorem quaternion_subgroup_ambient_conjugacy (P U V : Subgroup G)
    (hP : Stellmacher.IsSemidihedralGroup P) (hUP : U ≤ P) (hVP : V ≤ P)
    (hU : Nonempty (U ≃* QuaternionGroup 2)) (hV : Nonempty (V ≃* QuaternionGroup 2)) :
    ∃ s : P, V.map (MulAut.conj (s : G)).toMonoidHom = U :=
  small_subgroup_ambient_conjugacy P U V hP hUP hVP (Or.inr ⟨hU, hV⟩)
end ABG.QuasiDihedral
