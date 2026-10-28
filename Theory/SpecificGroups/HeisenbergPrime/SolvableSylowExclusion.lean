module
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Inner Heisenberg actions in solvable odd-index subgroups

An odd-index subgroup of an automorphism overgroup contains the inner image
of a full Sylow two-subgroup. Pulling it back by faithful inner conjugation
preserves solvability. If solvable Sylow overgroups normalize that Sylow and
the normalizer has two-group derived subgroup, every odd subgroup of the
pullback is abelian. This excludes any faithful inner ternary Heisenberg action.

Source: the Borel argument behind the characteristic-two model inspection in
Aschbacher–Smith 14.7.26, printed p.1053 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace HeisenbergPrime
variable {Q : Type*} [Group Q] [Finite Q]

/-- Solvable Sylow control and an abelian odd Borel quotient exclude inner Heisenberg actors. -/
theorem no_inner_action_in_solvable_odd_index
    (hz : center Q = ⊥) (hcontrol : SolvableSylowControl 2 Q)
    (hderived : ∀ S : Sylow 2 Q, ⁅normalizer (S : Set Q),normalizer (S : Set Q)⁆ ≤ (S : Subgroup Q))
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (J : Subgroup A) [Group.IsSolvable J] (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f)
    (hJ : ∀ y, f y ∈ J) (hi : ∀ y, (f y : MulAut Q) ∈ MulAut.innerSubgroup Q) : False := by
  let I := (MulAut.innerSubgroup Q).subgroupOf A
  let e : Q ≃* I := (MonoidHom.ofInjective
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)).trans (subgroupOfEquivOfLe hA).symm
  let j : Q →* A := (MulAut.conj : Q →* MulAut Q).codRestrict A (fun q => hA ⟨q,rfl⟩)
  have hj : Function.Injective j := fun _ _ hh =>
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hz) (congrArg Subtype.val hh)
  have he (y : I) : j (e.symm y) = y.val := by
    apply Subtype.ext
    exact congrArg (fun z : I => ((z : A) : MulAut Q)) (e.apply_symm_apply y)
  let N := J.comap j
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := j.subgroupComap J) (fun _ _ hh => Subtype.ext (hj (congrArg Subtype.val hh)))
  let P₀ := (default : Sylow 2 J)
  let P₁ : Subgroup A := (P₀ : Subgroup J).map J.subtype
  have hp : IsPGroup 2 P₁ := P₀.isPGroup'.map J.subtype
  have hind : ¬2 ∣ P₁.index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P₀.not_dvd_index ho.not_two_dvd_nat
  let P := hp.toSylow hind
  obtain ⟨R,hR⟩ := P.exists_subgroupOf_eq_of_normal I
  let S := R.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hSN : (S : Subgroup Q) ≤ N := by
    rintro _ ⟨r,hr,rfl⟩
    change j (e.symm r) ∈ J
    rw [he]
    rw [hR] at hr
    exact (map_subtype_le (P₀ : Subgroup J)) hr
  have hN : N ≤ normalizer (S : Set Q) := hcontrol S N inferInstance hSN
  let fi : HeisenbergPrime 3 →* I := f.codRestrict I hi
  let k := e.symm.toMonoidHom.comp fi
  have hk : Function.Injective k := e.symm.injective.comp
    (fun _ _ hh => hf (congrArg Subtype.val hh))
  have hkN : k.range ≤ N := by
    rintro _ ⟨y,rfl⟩
    change j (e.symm (fi y)) ∈ J
    rw [he]
    exact hJ y
  have h3 : IsPGroup 3 k.range :=
    (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_surjective
      k.rangeRestrict k.rangeRestrict_surjective
  have hdis : Disjoint k.range (S : Subgroup Q) := h3.disjoint_of_coprime S.isPGroup' (by decide)
  have hc : ⁅k.range,k.range⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [←hdis.eq_bot]
    exact le_inf (commutator_le_sup k.range k.range |>.trans (sup_idem k.range).le) ((commutator_mono
      (hkN.trans hN) (hkN.trans hN)).trans (hderived S))
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hc
  apply HeisenbergPrime.not_isMulCommutative (p := 3)
  exact ⟨⟨fun x y => hk (by
    rw [map_mul,map_mul]
    exact hcentral ⟨y,rfl⟩ _ ⟨x,rfl⟩)⟩⟩
end HeisenbergPrime
