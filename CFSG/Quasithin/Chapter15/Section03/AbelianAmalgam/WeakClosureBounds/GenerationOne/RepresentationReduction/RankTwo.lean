module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SLTwo
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Theory.Representation.SymplecticNatural

/-!
# Borel fixed spaces on the two rank-two natural pairs

A nonidentity split torus scalar eliminates every coordinate in the natural
SL₃ and Sp₄ representations. Products and Borel-preserving twists retain this
vanishing. Equivariant linear equivalences transport the calculations to the
literal quotient I/C_I(K) of an invariant subspace of the original module.

The twist is the actual group automorphism. These calculations work for any
Borel-preserving twist; proving that the source action moves the Dynkin diagram
and supplies this pair remains the representation restriction step. Sp₄ here
means the full symplectic group; no equality with Sp₄(2)' is asserted.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.65, case (ii) and its fixed-space argument, printed p.1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open Representation Representation.BinaryOffender Matrix
open scoped Matrix

private theorem eq_zero_of_scalar_fixed {F : Type*} [Field F]
    {x v : F} (hx : x ≠ 1) (h : x * v = v) : v = 0 := by
  have he : (x - 1) * v = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hx)

section Linear
variable {D V X : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- Vanishing Borel fixed spaces passes to the actual direct sum action. -/
theorem fixedSpace_prod_eq_bot (ρ : Representation (ZMod 2) D V)
    (σ : Representation (ZMod 2) D X) (B : Subgroup D)
    (hρ : fixedSpace ρ B = ⊥) (hσ : fixedSpace σ B = ⊥) :
    fixedSpace (ρ.prod σ) B = ⊥ := by
  apply bot_unique
  intro v hv
  have h₁ : v.1 ∈ fixedSpace ρ B := fun b => congrArg Prod.fst (hv b)
  have h₂ : v.2 ∈ fixedSpace σ B := fun b => congrArg Prod.snd (hv b)
  rw [hρ] at h₁
  rw [hσ] at h₂
  exact Prod.ext h₁ h₂

/-- Twisting an actual representation by a Borel-preserving automorphism
preserves vanishing of its Borel fixed space. -/
theorem fixedSpace_twist_eq_bot (ρ : Representation (ZMod 2) D V)
    (γ : MulAut D) (B : Subgroup D) (hB : B.map γ.toMonoidHom = B)
    (hρ : fixedSpace ρ B = ⊥) :
    fixedSpace (ρ.comp γ.toMonoidHom) B = ⊥ :=
  fixedSpace_eq_bot_of_equivariant _ ρ γ.toMonoidHom (LinearEquiv.refl _ _)
    (fun _ _ => rfl) B B hB hρ

/-- The sum of a module and its diagram conjugate, with the conjugate action
specified by the actual automorphism rather than by a dimension. -/
theorem fixedSpace_diagram_pair_eq_bot (ρ : Representation (ZMod 2) D V)
    (γ : MulAut D) (B : Subgroup D) (hB : B.map γ.toMonoidHom = B)
    (hρ : fixedSpace ρ B = ⊥) :
    fixedSpace (ρ.prod (ρ.comp γ.toMonoidHom)) B = ⊥ :=
  fixedSpace_prod_eq_bot ρ _ B hρ (fixedSpace_twist_eq_bot ρ γ B hB hρ)

end Linear

section SLThree
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- The two split torus directions in the actual SL₃ flag Borel eliminate
all three coordinates of a fixed vector. -/
theorem slThree_borel_fixedSpace_eq_bot (hF : 2 < Nat.card F) :
    fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
      (PSL3.LinearThree.borelSL F) = ⊥ := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have hi1 : (↑a⁻¹ : F) ≠ 1 := by simpa using inv_ne_one.mpr ha1
  apply bot_unique
  intro v hv
  have hp := hv ⟨PSL3.LinearThree.pointTorus F a,
    PSL3.LinearThree.pointTorus_mem_borel F a⟩
  have hl := hv ⟨PSL3.LinearThree.lineTorus F a,
    PSL3.LinearThree.lineTorus_mem_borel F a⟩
  change specialLinearNatural 3 (PSL3.LinearThree.pointTorus F a) v = v at hp
  change specialLinearNatural 3 (PSL3.LinearThree.lineTorus F a) v = v at hl
  rw [specialLinearNatural_apply] at hp hl
  have h0 : (a : F) * v 0 = v 0 := by
    simpa [specialLinearNatural_apply, PSL3.LinearThree.pointTorus,
      mulVec, dotProduct, Fin.sum_univ_three] using congrFun hp 0
  have h1 : (↑a⁻¹ : F) * v 1 = v 1 := by
    simpa [specialLinearNatural_apply, PSL3.LinearThree.pointTorus,
      mulVec, dotProduct, Fin.sum_univ_three] using congrFun hp 1
  have h2 : (a : F) * v 2 = v 2 := by
    simpa [specialLinearNatural_apply, PSL3.LinearThree.lineTorus,
      mulVec, dotProduct, Fin.sum_univ_three] using congrFun hl 2
  have hz0 := eq_zero_of_scalar_fixed ha1 h0
  have hz1 := eq_zero_of_scalar_fixed hi1 h1
  have hz2 := eq_zero_of_scalar_fixed ha1 h2
  ext i
  fin_cases i <;> assumption

/-- The Borel calculation on the natural SL₃ module and its actual twist.
Source restriction to a nontrivial diagram action is a separate obligation. -/
theorem slThree_diagram_pair_fixedSpace_eq_bot
    (γ : MulAut (SpecialLinearGroup (Fin 3) F))
    (hB : (PSL3.LinearThree.borelSL F).map γ.toMonoidHom = PSL3.LinearThree.borelSL F)
    (hF : 2 < Nat.card F) :
    let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
    fixedSpace (σ.prod (σ.comp γ.toMonoidHom)) (PSL3.LinearThree.borelSL F) = ⊥ :=
  fixedSpace_diagram_pair_eq_bot _ γ _ hB (slThree_borel_fixedSpace_eq_bot hF)

/-- The calculation on a literal invariant section, using an actual model
equivalence and an equivariant identification of its central quotient. -/
theorem slThree_centralQuotient_diagram_fixed
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (φ : K ≃* SpecialLinearGroup (Fin 3) F)
    (γ : MulAut (SpecialLinearGroup (Fin 3) F))
    (hγ : (PSL3.LinearThree.borelSL F).map γ.toMonoidHom = PSL3.LinearThree.borelSL F)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] ((Fin 3 → F) × (Fin 3 → F)))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      (specialLinearNatural 3 (φ g) (e v).1,
        specialLinearNatural 3 (γ (φ g)) (e v).2))
    (hB : (B.subgroupOf K).map φ.toMonoidHom = PSL3.LinearThree.borelSL F)
    (hF : 2 < Nat.card F) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  apply inf_fixedSpace_le_of_centralQuotient ρ K B I hI
  let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
  exact fixedSpace_eq_bot_of_equivariant _ (σ.prod (σ.comp γ.toMonoidHom))
    φ.toMonoidHom e he _ _ hB (slThree_diagram_pair_fixedSpace_eq_bot γ hγ hF)

end SLThree

section SpFour
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- On the natural Sp₄ module, diag(a,a,a⁻¹,a⁻¹) in the actual flag Borel
has no eigenvalue one. This statement uses Sp₄ itself, not its derived subgroup. -/
theorem spFour_borel_fixedSpace_eq_bot (hF : 2 < Nat.card F) :
    fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
      (borel (F := F)) = ⊥ := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have hi1 : (↑a⁻¹ : F) ≠ 1 := by simpa using inv_ne_one.mpr ha1
  apply bot_unique
  intro v hv
  have he := hv ⟨diagonalTorus a a, diagonalTorus_mem_borel a a⟩
  have hleft (i : Fin 2) : (a : F) * v (.inl i) = v (.inl i) := by
    have h := congrFun he (.inl i)
    fin_cases i <;> simpa [restrictScalars, symplecticNatural_apply, diagonalTorus,
      mulVec_diagonal] using h
  have hright (i : Fin 2) : (↑a⁻¹ : F) * v (.inr i) = v (.inr i) := by
    have h := congrFun he (.inr i)
    fin_cases i <;> simpa [restrictScalars, symplecticNatural_apply, diagonalTorus,
      mulVec_diagonal] using h
  ext i
  rcases i with i | i
  · exact eq_zero_of_scalar_fixed ha1 (hleft i)
  · exact eq_zero_of_scalar_fixed hi1 (hright i)

/-- The corresponding sum with a genuine automorphism twist on Sp₄. -/
theorem spFour_diagram_pair_fixedSpace_eq_bot (γ : MulAut (Sp F))
    (hB : (borel (F := F)).map γ.toMonoidHom = borel)
    (hF : 2 < Nat.card F) :
    let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
    fixedSpace (σ.prod (σ.comp γ.toMonoidHom)) (borel (F := F)) = ⊥ :=
  fixedSpace_diagram_pair_eq_bot _ γ _ hB (spFour_borel_fixedSpace_eq_bot hF)

/-- The corresponding actual central-quotient calculation for Sp₄. -/
theorem spFour_centralQuotient_diagram_fixed
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (φ : K ≃* Sp F) (γ : MulAut (Sp F))
    (hγ : (borel (F := F)).map γ.toMonoidHom = borel)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2]
      (((Fin 2 ⊕ Fin 2) → F) × ((Fin 2 ⊕ Fin 2) → F)))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      (symplecticNatural 2 (φ g) (e v).1,
        symplecticNatural 2 (γ (φ g)) (e v).2))
    (hB : (B.subgroupOf K).map φ.toMonoidHom = borel)
    (hF : 2 < Nat.card F) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  apply inf_fixedSpace_le_of_centralQuotient ρ K B I hI
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  exact fixedSpace_eq_bot_of_equivariant _ (σ.prod (σ.comp γ.toMonoidHom))
    φ.toMonoidHom e he _ _ hB (spFour_diagram_pair_fixedSpace_eq_bot γ hγ hF)

end SpFour
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
