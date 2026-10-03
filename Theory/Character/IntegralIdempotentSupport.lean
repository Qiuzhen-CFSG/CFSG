module

public import Theory.Character.ModularBlock.PrimeSingularIdempotentSupport
public import Theory.RingTheory.ComplexIntegralLocalization

/-!
# Integral central idempotents have prime-regular support

A central idempotent in the complex group algebra of a finite group has zero
coefficient at every element whose order is divisible by `p`, if a denominator
prime to `p` makes all its coefficients integral over `ℤ`.

Choose a local subring of `ℂ` containing these coefficients and all roots of
unity, with `p` a nonunit. Lift the group-algebra element to that ring. The
injective coefficient inclusion reflects idempotence and centrality, so the
local prime-singular support theorem applies. Mapping its conclusion back to
`ℂ` gives the result without any character-realization hypothesis.

This is the support step in the ordinary central-idempotent proof of
defect-zero vanishing, as used by Fong, *Some Sylow subgroups of order 32 and a
characterization of U(3,3)* (1967), pp. 74–75. The local trace argument is
formalized in `Theory.Character.ModularBlock.PrimeSingularIdempotentSupport`;
the coefficient ring is constructed in `Theory.RingTheory.ComplexIntegralLocalization`.
-/

public section

noncomputable section

namespace IntegralIdempotentSupport

/-- A complex central idempotent with coefficients integral after clearing a
denominator prime to `p` vanishes at every element of order divisible by `p`. -/
theorem coeff_eq_zero_of_prime_dvd_orderOf
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (e : MonoidAlgebra ℂ G)
    (he : IsIdempotentElem e) (hc : e ∈ Set.center (MonoidAlgebra ℂ G))
    (hint : ∃ m : ℕ, ¬ p ∣ m ∧ ∀ x : G, IsIntegral ℤ ((m : ℂ) * e.coeff x)) :
    ∀ g : G, p ∣ orderOf g → e.coeff g = 0 := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨S, hlocal, hp, hmem, hroots⟩ := ComplexIntegralLocalization.exists_subring p
  let : IsLocalRing S := hlocal
  obtain ⟨m, hm, hint⟩ := hint
  let a : MonoidAlgebra S G := MonoidAlgebra.ofCoeff
    ((Finsupp.equivFunOnFinite : (G →₀ S) ≃ (G → S)).symm
      (fun x => ⟨e.coeff x, hmem _ ⟨m, hm, hint x⟩⟩))
  let f : MonoidAlgebra S G →+* MonoidAlgebra ℂ G := MonoidAlgebra.mapRingHom G S.subtype
  have hf : Function.Injective f := by
    intro x y h
    ext g
    exact congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g) h
  have ha : f a = e := by
    ext g
    simp [f, a]
  have hae : IsIdempotentElem a := by
    apply hf
    simpa only [map_mul, ha] using (show e * e = e from he)
  have hac : a ∈ Set.center (MonoidAlgebra S G) := by
    rw [Semigroup.mem_center_iff] at hc ⊢
    intro b
    apply hf
    simpa only [map_mul, ha] using hc (f b)
  intro g hg
  have hz := ModularBlock.CentralIdempotentSupport.coeff_eq_zero_of_prime_dvd_orderOf
    p hp (fun n hn _ => hroots n hn) a hae hac g hg
  have hz' := congrArg (fun x : S => (x : ℂ)) hz
  simpa [a] using hz'

end IntegralIdempotentSupport
