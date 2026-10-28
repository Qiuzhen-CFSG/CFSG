module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedFiltration
public import Theory.Representation.QuadraticFourGroup.Basic
public import Theory.Representation.SimpleHeadQuotient

/-!
# Odd-index fixed spaces from the actual irreducible sections

Choose a maximal proper subrepresentation of each invariant submodule.
Its irreducible quotient is a literal section of the original action, and
odd-index trace lifts fixed-space equality through the extension. Induction
on the original submodule's dimension therefore needs no semisimplicity or
splitting of the module.

Source: Aschbacher–Smith 15.3.65, p.1152; GLS2 G.25.14 section conclusions.
-/

@[expose] public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction Representation.QuadraticFourGroup
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The irreducible hypotheses concern only actual sections of this representation. -/
theorem fixedSpace_le_of_irreducible_sections (B : Subgroup D) (hindex : Odd B.index)
    (hsections : ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) D W),
      IsIrreducibleSection ρ σ → fixedSpace σ B ≤ fixedSpace σ ⊤) :
    fixedSpace ρ B ≤ fixedSpace ρ ⊤ := by
  classical
  have main : ∀ n, ∀ S : Subrepresentation ρ,
      Module.finrank (ZMod 2) S.toSubmodule = n →
      fixedSpace S.toRepresentation B ≤ fixedSpace S.toRepresentation ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases ht : Subsingleton S.toSubmodule
      · let := ht
        intro v hv g
        exact Subsingleton.elim _ _
      · let : Nontrivial S.toSubmodule := not_subsingleton_iff_nontrivial.mp ht
        let : IsCoatomic (Subrepresentation S.toRepresentation) :=
          SimpleHeadQuotient.subrepresentation_coatomic S.toRepresentation
        obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation S.toRepresentation)
        have hi := SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
        have hQ := hsections (S.toSubmodule ⧸ N.toSubmodule) N.quotientRepresentation
          ⟨hi,S,N,⟨Representation.Equiv.refl _⟩⟩
        let C : Subrepresentation ρ := {
          toSubmodule := N.toSubmodule.map S.toSubmodule.subtype
          apply_mem_toSubmodule g v hv := by
            obtain ⟨w,hw,rfl⟩ := hv
            exact ⟨S.toRepresentation g w,N.apply_mem_toSubmodule g hw,rfl⟩ }
        have hCS : C.toSubmodule < S.toSubmodule := by
          refine lt_of_le_of_ne (Submodule.map_subtype_le _ _) ?_
          intro he
          apply hN.1
          apply top_unique
          intro w _
          have hw : (w : V) ∈ C.toSubmodule := he.symm ▸ w.property
          obtain ⟨z,hz,heq⟩ := hw
          have hzw : z = w := Subtype.ext heq
          exact hzw ▸ hz
        have hdim : Module.finrank (ZMod 2) C.toSubmodule < n := by
          rw [← hn]
          exact Submodule.finrank_lt_finrank_of_lt hCS
        have hC := ih _ hdim C rfl
        apply fixedSpace_le_of_extension S.toRepresentation N B hindex ?_ hQ
        rintro w ⟨hw,hwB⟩ g
        let z : C.toSubmodule := ⟨w.val,⟨w,hw,rfl⟩⟩
        have hzB : z ∈ fixedSpace C.toRepresentation B := by
          intro b
          apply Subtype.ext
          change ρ (b : D) w.val = w.val
          exact congrArg (fun x : S.toSubmodule => (x : V)) (hwB b)
        apply Subtype.ext
        change ρ (g : D) w.val = w.val
        exact congrArg (fun x : C.toSubmodule => (x : V)) (hC hzB g)
  have ht := main _ (⊤ : Subrepresentation ρ) rfl
  intro v hv g
  have hvtop : (⟨v,Submodule.mem_top⟩ : (⊤ : Subrepresentation ρ).toSubmodule) ∈
      fixedSpace (⊤ : Subrepresentation ρ).toRepresentation B := by
    intro b
    exact Subtype.ext (hv b)
  exact congrArg Subtype.val (ht hvtop g)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
