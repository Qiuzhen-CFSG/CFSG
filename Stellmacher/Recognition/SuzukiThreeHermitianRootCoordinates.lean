module

public import Stellmacher.Recognition.SuzukiThreeCoordinateData
public import Theory.SpecificGroups.UnitaryThree.RootTorus
public import Theory.SpecificGroups.UnitaryThree.RootRecognition
public import Theory.SpecificGroups.UnitaryThree.RootAutomorphisms

/-!
# Hermitian root and torus coordinates at q = 3

To identify the Borel action, it suffices to identify the root group and the
action of one generator of the cyclic two-point stabilizer. The generator
determines an isomorphism of the torus with F₉ˣ, and equality on that generator
extends to equality of the two action homomorphisms.

The final reduction transports the torus action through any root-group
isomorphism. Conjugating the transported order-eight automorphism to a scalar
action then supplies Borel coordinates. Root-group identification and this
automorphism conjugacy are the two algebraic inputs to that reduction.
The final theorem supplies both inputs from the local structure: the root
group is nonabelian of order 27 and exponent three, and every order-eight
automorphism of the Hermitian root group is conjugate to a scalar action.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section IV. At q = 3 the prime-field twisting is trivial.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

/-- Compatibility for one torus generator gives compatibility for every torus
element, and hence Borel coordinates. -/
public theorem nonempty_borelCoordinates_of_generator (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root)
    (k : stabilizer (stabilizer G a) b) (hk : orderOf k = 8)
    (r : FiniteField.Nineˣ) (hr : orderOf r = 8)
    (he : ∀ q : Q, e (torusRootAut (Q := Q) b k q) = UnitaryThree.scale r (e q)) :
    Nonempty (SuzukiThreeBorelCoordinates h b hb) := by
  let K := stabilizer (stabilizer G a) b
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [h.twoPoint_card b hb]; decide)
  have hkTop : Subgroup.zpowers k = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (by
      rw [Nat.card_zpowers, hk, h.twoPoint_card b hb])
  have hrTop : Subgroup.zpowers r = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (by
      rw [Nat.card_zpowers, hr, UnitaryThree.torus_card])
  have hkg (l : K) : l ∈ Subgroup.zpowers k := hkTop ▸ Subgroup.mem_top l
  have hrg (s : FiniteField.Nineˣ) : s ∈ Subgroup.zpowers r :=
    hrTop ▸ Subgroup.mem_top s
  let kappa : K ≃* FiniteField.Nineˣ := mulEquivOfOrderOfEq hkg hrg (hk.trans hr.symm)
  have hkappa : kappa k = r := mulEquivOfOrderOfEq_apply_gen hkg hrg (hk.trans hr.symm)
  let lhs : K →* MulAut UnitaryThree.Root :=
    (MulAut.congr e).toMonoidHom.comp (torusRootAut (Q := Q) b)
  let rhs : K →* MulAut UnitaryThree.Root :=
    UnitaryThree.scaleHom.comp kappa.toMonoidHom
  have hhom : lhs = rhs := by
    apply (MonoidHom.eq_iff_eq_on_generator hkg lhs rhs).mpr
    apply MulEquiv.ext
    intro p
    change e (torusRootAut (Q := Q) b k (e.symm p)) = UnitaryThree.scaleHom (kappa k) p
    rw [UnitaryThree.scaleHom_apply, hkappa, he, e.apply_symm_apply]
  refine ⟨SuzukiThreeBorelCoordinates.ofRootTorusEquiv h b hb e kappa ?_⟩
  intro l q
  have heq := DFunLike.congr_fun (DFunLike.congr_fun hhom l) (e q)
  change e (torusRootAut (Q := Q) b l (e.symm (e q))) =
    UnitaryThree.scaleHom (kappa l) (e q) at heq
  simpa only [e.symm_apply_apply, UnitaryThree.scaleHom_apply] using heq

/-- Root-group identification and conjugacy of order-eight root automorphisms
to scalar actions suffice for the Borel-coordinate construction. -/
public theorem nonempty_borelCoordinates_of_rootEquiv_of_conjugate_scale
    [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) (e : Q ≃* UnitaryThree.Root)
    (hnormalize : ∀ f : MulAut UnitaryThree.Root, orderOf f = 8 →
      ∃ (c : MulAut UnitaryThree.Root) (r : FiniteField.Nineˣ),
        orderOf r = 8 ∧ ∀ p : UnitaryThree.Root, c (f p) = UnitaryThree.scale r (c p)) :
    Nonempty (SuzukiThreeBorelCoordinates h b hb) := by
  let K := stabilizer (stabilizer G a) b
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [h.twoPoint_card b hb]; decide)
  let : IsCyclic K := h.twoPoint_cyclic b hb
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hk8 : orderOf k = 8 := hk.trans (h.twoPoint_card b hb)
  let f : MulAut UnitaryThree.Root := (MulAut.congr e) (torusRootAut (Q := Q) b k)
  have hf : orderOf f = 8 :=
    ((MulAut.congr e).orderOf_eq _).trans
      ((orderOf_injective (torusRootAut (Q := Q) b)
        (h.torusRootAut_injective b hb) k).trans hk8)
  obtain ⟨c, r, hr, hc⟩ := hnormalize f hf
  apply h.nonempty_borelCoordinates_of_generator b hb (e.trans c) k hk8 r hr
  intro q
  have heq := hc (e q)
  change c (e (torusRootAut (Q := Q) b k (e.symm (e q)))) =
    UnitaryThree.scale r (c (e q)) at heq
  simpa only [e.symm_apply_apply, MulEquiv.trans_apply] using heq

/-- Suzuki's local structure gives Hermitian coordinates for the root group
and its torus action. -/
public theorem nonempty_borelCoordinates [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (hlocal : SuzukiThreeLocalStructure G Ω a b Q) :
    Nonempty (SuzukiThreeBorelCoordinates h b hb) := by
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.root_card]; decide)
  obtain ⟨e⟩ := UnitaryThree.nonempty_mulEquiv_root h.root_card
    hlocal.root_cube hlocal.root_noncommuting
  exact h.nonempty_borelCoordinates_of_rootEquiv_of_conjugate_scale b hb e
    UnitaryThree.conjugate_scale_of_orderOf_eq_eight

end Stellmacher.Recognition.SuzukiThreeHypotheses
