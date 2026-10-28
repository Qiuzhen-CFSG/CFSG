module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.AlternatingFixedSpace.FourDimensional

/-!
# Trivial summands in the four-dimensional A₇ alternative

The cubic witness for every faithful four-dimensional A₇ action lifts
through any equivariant map with central kernel. In particular, this
retains arbitrary trivial summands without choosing a particular A₇ action.

The section version takes an invariant submodule with the four-dimensional
quotient and a trivial supplement in the whole module. A Sylow-fixed vector
decomposes into a fixed vector of the submodule and an invariant vector;
the cubic lifting argument fixes the first, and invariance fixes the second.
An actual embedding of A₇ permits transport to any finite ambient actor.

B.5.1(2) excludes additional nonsplit extensions for the four-dimensional
A₇ alternative of B.4.2(7). Thus its allowed direct sums satisfy the stated
supplement hypothesis. The A₆/S₆ nonsplit cases are treated separately in
`Permutation` and `Symplectic`, without assuming such a supplement.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.4.2(7), B.5.1(1),(2),(4), and the module comparison
in Lemma 15.4.18, printed pp.86,99,1163.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
open Representation Representation.BinaryOffender

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The four-dimensional A₇ witness survives any central kernel, including
arbitrary trivial summands. No splitting or surjectivity of the map is needed. -/
theorem four_dimensional_quotient_enlargement
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (hσ : Function.Injective σ) (hdim : Module.finrank (ZMod 2) W = 4)
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = σ g (q v))
    (hker : ∀ g, ∀ v ∈ q.ker, ρ g v = v)
    (S : Sylow 2 (alternatingGroup (Fin 7))) :
    ∃ d : alternatingGroup (Fin 7), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup _), ρ d v = v :=
  sylow_fixedSpace_enlargement_of_cubic_quotient ρ σ q hq hker S
    (four_dimensional_enlargement σ hσ hdim S)

/-- The actual section and trivial-supplement configuration of B.5.1 for
the four-dimensional A₇ alternative. Only the embedded A₇ must act trivially
on the supplement; the ambient actor may act on it nontrivially. -/
theorem four_dimensional_supplement_enlargement
    {D : Type*} [Group D] [Finite D]
    (ρ : Representation (ZMod 2) D V)
    (f : alternatingGroup (Fin 7) →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f))
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (hσ : Function.Injective σ) (hdim : Module.finrank (ZMod 2) W = 4)
    (q : U.toSubmodule →ₗ[ZMod 2] W)
    (hq : ∀ g u, q (U.toRepresentation g u) = σ g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hsup : U.toSubmodule ⊔ Representation.invariants (ρ.comp f) = ⊤)
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let T : Sylow 2 (alternatingGroup (Fin 7)) := Classical.choice inferInstance
  obtain ⟨d, hd, hd3, hfix⟩ := four_dimensional_enlargement σ hσ hdim T
  have hdne : d ≠ 1 := fun he => hd (he ▸ T.one_mem)
  have hU := cubic_fixedSpace_of_map U.toRepresentation σ (T : Subgroup _) d hd3
    q hq (fun u hu => hker d u hu) hfix
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf
    (T : Subgroup _) T.isPGroup' d hd3 hdne _ S
  intro v hv
  have hvtop : v ∈ U.toSubmodule ⊔ Representation.invariants (ρ.comp f) := by
    rw [hsup]
    trivial
  obtain ⟨u, hu, c, hc, huv⟩ := Submodule.mem_sup.mp hvtop
  have hcentral : ∀ g, ρ (f g) c = c := hc
  have hufix : (⟨u, hu⟩ : U.toSubmodule) ∈ fixedSpace U.toRepresentation (T : Subgroup _) := by
    intro t
    apply Subtype.ext
    have ht := hv t
    change ρ (f t.val) v = v at ht
    rw [← huv, map_add, hcentral t.val] at ht
    exact add_right_cancel ht
  rw [← huv, map_add, hcentral d]
  exact congrArg (fun x : V => x + c) (congrArg Subtype.val (hU ⟨u, hu⟩ hufix))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
