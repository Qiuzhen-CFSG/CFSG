module
public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.CharacteristicTwoNormal

/-!
# Characteristic two for centralizers containing an ambient Sylow

Under Hypothesis One, the centralizer of a nontrivial two-subgroup is
solvable and has characteristic two whenever it contains an ambient Sylow
2-subgroup. The given Sylow need not be the distinguished Sylow S₀.

The normalizer of the nontrivial two-subgroup is a genuine two-local.
Conjugating the supplied Sylow to S₀ lets Hypothesis One apply to a
conjugate of that normalizer. Solvability and characteristic two transport
back through the conjugation equivalence. The centralizer is normal in
the normalizer, so it inherits characteristic two by the solvable normal
subgroup theorem and inherits solvability through its inclusion.

This provides the centralizer transfer in Stellmacher (9.3), Journal of
Algebra 190 (1997), p.50, once a conjugate ambient Sylow centralizes R₀.
The argument uses the normalizer as its two-local overgroup throughout.
-/

namespace Stellmacher.SectionsFiveToSeven

private theorem characteristicTwo_transport
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hchar : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hcore := pCore_map_iso 2 e
  intro h hh
  obtain ⟨g, rfl⟩ := e.surjective h
  rw [← hcore]
  apply Subgroup.mem_map_of_mem
  apply hchar
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply e.injective
  have hyH : e y ∈ pCore 2 H := by
    rw [← hcore]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hh (e y) hyH

private theorem local_properties_of_contains_ambient_sylow
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hyp : HypothesisOne H S0) (N : Subgroup H) (hN : IsTwoLocal N)
    (P : Sylow 2 H) (hPN : (P : Subgroup H) ≤ N) :
    Group.IsSolvable N ∧ IsCharacteristicTwoType N := by
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq H P S0
  let equiv : H ≃* H := MulAut.conj conjugator
  have hlocal : IsTwoLocal (N.map equiv.toMonoidHom) := by
    obtain ⟨Q, hQne, hQp, rfl⟩ := hN
    refine ⟨Q.map equiv.toMonoidHom, ?_, hQp.map _, ?_⟩
    · intro hbot
      exact hQne (Subgroup.map_injective equiv.injective (by simpa using hbot))
    · exact Subgroup.map_equiv_normalizer_eq Q equiv
  have hS0 : (S0 : Subgroup H) ≤ N.map equiv.toMonoidHom := by
    rw [← hconjugator]
    exact Subgroup.map_mono hPN
  obtain ⟨hsolv, hchar⟩ := hyp.local_solvable_characteristicTwo _ hlocal hS0
  let _ := hsolv
  let e := N.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective, characteristicTwo_transport e.symm hchar⟩

/-- The centralizer of a nontrivial two-subgroup containing an ambient
Sylow is solvable and of characteristic two under Hypothesis One. -/
public theorem centralizer_characteristicTwo_of_contains_sylow
    {H : Type*} [Group H] [Finite H] {S0 : Sylow 2 H}
    (h : HypothesisOne H S0) (R : Subgroup H)
    (hRne : R ≠ ⊥) (hRp : IsPGroup 2 R)
    (P : Sylow 2 H) (hPC : (P : Subgroup H) ≤ Subgroup.centralizer (R : Set H)) :
    Group.IsSolvable (Subgroup.centralizer (R : Set H)) ∧
      IsCharacteristicTwoType (Subgroup.centralizer (R : Set H)) := by
  let C := Subgroup.centralizer (R : Set H)
  let N := Subgroup.normalizer (R : Set H)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  obtain ⟨hsolv, hchar⟩ := local_properties_of_contains_ambient_sylow S0 h N
    ⟨R, hRne, hRp, rfl⟩ P (hPC.trans hCN)
  let _ := hsolv
  have hCsolv : Group.IsSolvable C :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hCN) (Subgroup.inclusion_injective hCN)
  have hCchar := characteristicTwo_normal_subgroup hsolv hchar (C.subgroupOf N)
  exact ⟨hCsolv, characteristicTwo_transport (Subgroup.subgroupOfEquivOfLe hCN) hCchar⟩

end Stellmacher.SectionsFiveToSeven
