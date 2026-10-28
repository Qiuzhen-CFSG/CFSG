module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.Extraction

/-!
# Odd subgroups from positioned outer-actor coordinates

In fixed-field root coordinates the projective root line has prime order p
and is inverted by the marked inner involution. In rotation coordinates
the injective norm-one torus has order p+1 and is inverted by that involution;
its r-th power kernel, for an odd prime r dividing (p+1)/2, supplies the
required subgroup. Both constructions transport through the actual socle
isomorphism and preserve normalization by the entire ambient centralizer.

The final output supplies exactly the `hone` premise of
`CentralizerGeometry.false_of_congruence_constructions`; the companion
`Consumer` module gives that conditional application without an import cycle.
The unresolved model geometry is existence of `HasInvertedCoordinates` for
a conjugate of the whole original actor. This module does not assert that
existence or the unconditional outer four-actor construction.

Source: Aschbacher--Smith, E.1.1--2, E.1.5 and E.1.14(7), printed
pp.209--210,214; A.2.3(2), p.33; A.3.21, p.55; Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open InnerGeometry.SemidihedralTorus
variable {G : Type*} [Group G] [Finite G]

/-- Either concrete coordinate family supplies a nontrivial normalized odd-prime subgroup. -/
theorem exists_odd_subgroup_of_coordinates (L R : Subgroup G) [L.Normal]
    (z : L) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : p % 4 = 1)
    (hcoords : HasInvertedCoordinates L R z p) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧ X ≠ ⊥ ∧ R ≤ normalizer (X : Set G) ∧
        ∀ x ∈ X, (z : G) * x * (z : G)⁻¹ = x⁻¹ := by
  obtain ⟨F, _, _, J, hcard, hconj, hroot | htorus⟩ := hcoords
  · obtain ⟨hJ, h2, e, hez, hscale⟩ := hroot
    let : Fact p.Prime := ⟨hp⟩
    have hf : Nat.card (FixedBy.subfield F J.conj) = p := by
      let ef : FixedBy.subfield F J.conj ≃ {x : F // J.conj x = x} := {
        toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      refine (Nat.card_congr ef).trans ?_
      simpa only [pow_one] using
        (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
          (by simpa only [pow_one] using hcard)
          (by simpa only [pow_one] using hconj))
    obtain ⟨X, ⟨eX⟩, hn, hi⟩ := transport_subgroup L e R
      (fixedRoot J hJ h2).range z
      (by
        rintro x ⟨t, rfl⟩
        rw [hez]
        exact fixedRoot_inverted J hJ h2 t)
      (by
        rintro s hs x ⟨t, rfl⟩
        obtain ⟨c, hc⟩ := hscale s hs
        exact ⟨Multiplicative.ofAdd ((c : FixedBy.subfield F J.conj) * t.toAdd),
          (hc t.toAdd).symm⟩)
    have hxcard : Nat.card X = p := (Nat.card_congr eX.toEquiv).symm.trans
      (fixedRoot_card J hJ h2 hf)
    refine ⟨p, hp, ho, X, IsPGroup.of_card (n := 1) (by simpa using hxcard), ?_, hn, hi⟩
    intro he
    have he' := (eq_bot_iff_card X).mp he
    have := hp.two_le
    omega
  · obtain ⟨hJ, h2, e, hez, haction⟩ := htorus
    obtain ⟨X, ⟨eX⟩, hn, hi⟩ := transport_subgroup L e R
      (projectiveRotation J hJ h2).range z
      (by
        rw [hez]
        exact projectiveRotation_inverted J hJ h2)
      (by
        rintro s hs x ⟨k, rfl⟩
        obtain ⟨ε, hε⟩ := haction s hs
        exact ⟨if ε then k⁻¹ else k, (hε k).symm⟩)
    let : IsCyclic (projectiveRotation J hJ h2).range := projectiveRotation_isCyclic J hJ h2
    let : IsCyclic X := eX.isCyclic.mp inferInstance
    have hxcard : Nat.card X = p + 1 := (Nat.card_congr eX.toEquiv).symm.trans
      (projectiveRotation_card J hJ h2 hcard hconj)
    exact odd_subgroup_of_cyclic X R hp.one_lt hm hxcard z hi hn

/-- The exact outer-actor witness, conditional only on its explicit matrix placement. -/
theorem exists_conjugate_inverted_odd_subgroup_of_coordinates
    {T : Sylow 2 G} {A : Subgroup G} {z : G}
    (hzL : z ∈ generalizedFitting G)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : p % 4 = 1)
    (hcoords : ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      HasInvertedCoordinates (generalizedFitting G)
        ((T : Subgroup G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G))
        ⟨z, hzL⟩ p) :
    ∃ (g : G) (r : ℕ), r.Prime ∧ Odd r ∧
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      ∃ X : Subgroup G, IsPGroup r X ∧ X ≠ ⊥ ∧
        (T : Subgroup G) ⊓ centralizer
          (A.map (MulAut.conj g).toMonoidHom : Set G) ≤ normalizer (X : Set G) ∧
        ∀ x ∈ X, z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨g, hBT, hzB, hc⟩ := hcoords
  obtain ⟨r, hr, hro, X, hX, hne, hn, hi⟩ :=
    exists_odd_subgroup_of_coordinates _ _ ⟨z, hzL⟩ hp ho hm hc
  exact ⟨g, r, hr, hro, hBT, hzB, X, hX, hne, hn, hi⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
