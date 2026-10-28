module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.FieldTransport

/-!
# Selecting and transporting the interior degree-twenty factor

A permutation module on 126 points has a constant line and an augmentation
quotient of dimension one. If its two intervening simple factors have
allowed degrees 20 and 104, their total dimension is 124, so at least one
has degree twenty. This selects a specified factor rather than inferring
its occurrence from an allowed-degree list alone.

An equivariant linear equivalence pulls back both invariant subspaces and
their literal quotient action. Applied to the existing identification
[t ⊗ a] ↦ a δ(t⁻¹B) and to Borel-preserving matrix-field transport, this puts
the selected factor in the original trivial-character induced module.
The coefficient field is unchanged, and the factor is not assumed absolute.

The canonical middle flag and the coset count remain explicit premises.
Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.TrivialCalculation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

set_option backward.isDefEq.respectTransparency false in
/-- The 126-point dimension forces one actual middle quotient to have degree twenty. -/
public theorem twenty_factor_of_middle_flag
    {K G Ω : Type*} [Field K] [Group G] [MulAction G Ω] [Fintype Ω] [Nonempty Ω]
    (hcard : Nat.card Ω = 126) (h : MiddleFlag (K := K) (G := G) (Ω := Ω)) :
    ∃ (S : Subrepresentation (functionAction (K := K) (G := G) (Ω := Ω)))
      (T : Subrepresentation S.toRepresentation),
      T.quotientRepresentation.IsIrreducible ∧
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 := by
  obtain ⟨U, hCU, hUA, hs₁, hs₂, hd₁, hd₂⟩ := h
  have hdim : Module.finrank K (Ω → K) = 126 := by
    simpa only [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] using hcard
  have hC := finrank_constants (K := K) (G := G) (Ω := Ω)
  have hA := finrank_augmentation_quotient (K := K) (G := G) (Ω := Ω)
  have hCU := (withinEquiv (k := K) (G := G) constants U hCU).finrank_eq
  have hUA := (withinEquiv (k := K) (G := G) U augmentationKernel hUA).finrank_eq
  have hu := Submodule.finrank_quotient_add_finrank (within (k := K) (G := G) constants U).toSubmodule
  have ha := Submodule.finrank_quotient_add_finrank (within (k := K) (G := G) U augmentationKernel).toSubmodule
  have ht := Submodule.finrank_quotient_add_finrank
    (augmentationKernel (K := K) (G := G) (Ω := Ω)).toSubmodule
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd₁ hd₂
  rcases hd₁ with hd₁ | hd₁
  · exact ⟨U, within (k := K) (G := G) constants U, hs₁, hd₁⟩
  · refine ⟨augmentationKernel (K := K) (G := G) (Ω := Ω), within (k := K) (G := G) U augmentationKernel, hs₂, ?_⟩
    omega

private theorem irreducible_transport
    {K G H V W : Type*} [Field K] [Group G] [Group H]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K H W)
    (e : G ≃* H) (E : V ≃ₗ[K] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))
    (hs : σ.IsIrreducible) : ρ.IsIrreducible := by
  have hc : IsIrreducible (σ.comp e.toMonoidHom) :=
    (RepEquiv.irreducible_iff_group_iso (ρ := σ.comp e.toMonoidHom) e (fun _ _ => rfl)).mpr hs
  let R : ρ.Equiv (σ.comp e.toMonoidHom) :=
    Representation.Equiv.mk E (fun g => LinearMap.ext (hE g))
  exact (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv R)).mpr hc

/-- Pull back both invariant subspaces through a marked group and module equivalence. -/
public theorem simple_section_transport
    {K G H V W : Type*} [Field K] [Group G] [Group H]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K H W)
    (e : G ≃* H) (E : V ≃ₗ[K] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))
    (S : Subrepresentation σ) (T : Subrepresentation S.toRepresentation)
    (hs : T.quotientRepresentation.IsIrreducible) {d : ℕ}
    (hd : Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = d) :
    ∃ (P : Subrepresentation ρ) (Q : Subrepresentation P.toRepresentation),
      Q.quotientRepresentation.IsIrreducible ∧
        Module.finrank K (P.toSubmodule ⧸ Q.toSubmodule) = d := by
  let P : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap E.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change E (ρ g v) ∈ S.toSubmodule
      rw [hE]
      exact S.apply_mem_toSubmodule (e g) hv }
  let Es : P.toSubmodule ≃ₗ[K] S.toSubmodule := {
    toFun := fun v => ⟨E v, v.property⟩
    invFun := fun w => ⟨E.symm w, by change E (E.symm w) ∈ S; simp⟩
    left_inv := fun v => Subtype.ext (E.symm_apply_apply v)
    right_inv := fun w => Subtype.ext (E.apply_symm_apply w)
    map_add' := fun v w => Subtype.ext (E.map_add v w)
    map_smul' := fun c v => Subtype.ext (E.map_smul c v) }
  have hes (g : G) (v : P.toSubmodule) :
      Es (P.toRepresentation g v) = S.toRepresentation (e g) (Es v) :=
    Subtype.ext (hE g v)
  let Q : Subrepresentation P.toRepresentation := {
    toSubmodule := T.toSubmodule.comap Es.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change Es (P.toRepresentation g v) ∈ T.toSubmodule
      rw [hes]
      exact T.apply_mem_toSubmodule (e g) hv }
  have hmap : Q.toSubmodule.map Es.toLinearMap = T.toSubmodule :=
    Submodule.map_comap_eq_of_surjective Es.surjective _
  let Eq := Submodule.Quotient.equiv Q.toSubmodule T.toSubmodule Es hmap
  have heq (g : G) (v : P.toSubmodule ⧸ Q.toSubmodule) :
      Eq (Q.quotientRepresentation g v) = T.quotientRepresentation (e g) (Eq v) := by
    induction v using Submodule.Quotient.induction_on with
    | H v => exact congrArg T.toSubmodule.mkQ (hes g v)
  exact ⟨P, Q, irreducible_transport _ _ e Eq heq hs, Eq.finrank_eq.trans hd⟩

private theorem induced_section_of_coset_section
    {K G H : Type*} [Field K] [Group G] [Group H] [Finite H]
    (B : Subgroup G) (C : Subgroup H) (e : G ≃* H)
    (he : ∀ g, e g ∈ C ↔ g ∈ B)
    (S : Subrepresentation (functionAction (K := K) (G := H) (Ω := H ⧸ C)))
    (T : Subrepresentation S.toRepresentation)
    (hs : T.quotientRepresentation.IsIrreducible) {d : ℕ}
    (hd : Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = d) :
    ∃ (P : Subrepresentation (ind B.subtype (Degrees.scalarCharacter (1 : B →* Kˣ))))
      (Q : Subrepresentation P.toRepresentation),
      Q.quotientRepresentation.IsIrreducible ∧
        Module.finrank K (P.toSubmodule ⧸ Q.toSubmodule) = d := by
  let a := inductionCosetEquiv (K := K) B
  let b := cosetModuleEquiv (K := K) B C e he
  let c := functionEquiv (K := K) (Ω := H ⧸ C)
  let E := a.trans (b.trans c)
  have hE : ∀ g v,
      E (ind B.subtype (Degrees.scalarCharacter (1 : B →* Kˣ)) g v) =
        functionAction (e g) (E v) := by
    intro g v
    change c (b (a (ind B.subtype (Degrees.scalarCharacter (1 : B →* Kˣ)) g v))) = _
    rw [inductionCosetEquiv_equivariant, cosetModuleEquiv_equivariant,
      functionEquiv_equivariant]
    rfl
  exact simple_section_transport (K := K) (G := G) (H := H) _ _ e E hE S T hs hd

private theorem scalar_character_agreement {K B : Type*} [Field K] [Group B]
    (χ : B →* Kˣ) : scalarCharacter χ = Degrees.scalarCharacter χ := rfl

private theorem induced_twenty_factor_of_middle_flag
    {K G H : Type*} [Field K] [Group G] [Group H] [Finite H]
    (B : Subgroup G) (C : Subgroup H) [Fintype (H ⧸ C)] (e : G ≃* H)
    (he : ∀ g, e g ∈ C ↔ g ∈ B) (hcard : Nat.card (H ⧸ C) = 126)
    (hm : MiddleFlag (K := K) (G := H) (Ω := H ⧸ C)) :
    ∃ (P : Subrepresentation (ind B.subtype (scalarCharacter (1 : B →* Kˣ))))
      (Q : Subrepresentation P.toRepresentation),
      Q.quotientRepresentation.IsIrreducible ∧
        Module.finrank K (P.toSubmodule ⧸ Q.toSubmodule) = 20 := by
  rw [scalar_character_agreement]
  obtain ⟨S, T, hs, hd⟩ := twenty_factor_of_middle_flag
    (K := K) (G := H) (Ω := H ⧸ C) hcard hm
  exact induced_section_of_coset_section (K := K) (G := G) (H := H) B C e he S T hs hd

universe v
/-- The concrete middle flag supplies a simple degree-twenty section of the
literal induced module over the original matrix and coefficient fields. -/
public theorem trivial_twenty_factor_of_middle_flags
    (hcard : Nat.card CanonicalPoints = 126) (hm : CanonicalMiddleFlags.{v})
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (K : Type v) [Field K] [Finite K] [CharP K 2] :
    ∃ (S : Subrepresentation (ind (standardBorel J).subtype
        (scalarCharacter (1 : standardBorel J →* Kˣ))))
      (T : Subrepresentation S.toRepresentation),
      T.quotientRepresentation.IsIrreducible ∧
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 := by
  have hp : ∃ e : standardGroup J ≃* CanonicalGroup,
      ∀ g, e g ∈ canonicalBorel ↔ g ∈ standardBorel J :=
    borel_field_transport F J hc hconj
  obtain ⟨e, he⟩ := hp
  exact induced_twenty_factor_of_middle_flag (K := K) (G := standardGroup J)
    (H := CanonicalGroup) (standardBorel J) canonicalBorel e he hcard (hm K)
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
