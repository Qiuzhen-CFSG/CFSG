module

public import Theory.Representation.SolvableDimension
public import Theory.Representation.Induction
public import Theory.Character.Induction
public import Theory.GroupTheory.NilpotentSecondCenter

/-!
# Faithful irreducibles of nilpotent groups are properly induced

A faithful nonlinear irreducible complex representation of a finite nilpotent
group is induced from an irreducible character of a proper subgroup.

Choose a noncentral element of the second center and take its proper normal
centralizer. A simple constituent of the restriction has no equivalent
conjugate outside this centralizer: Schur's lemma on the constituent and on the
ambient representation would force the corresponding central commutator into
the faithful representation's kernel. The coinduction criterion then identifies
the ambient representation, and the induced character formula gives the stated
class-function identity. A choice of basis puts the constituent in the standard
finite-dimensional model required by `IsIrreducibleCharacter`.

Source: Serre, *Linear Representations of Finite Groups*, the proof that finite
nilpotent groups are monomial.
-/

open Representation
open scoped commutatorElement
noncomputable section
namespace Theory.Character

private theorem central_scalar {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ Subgroup.center G) :
    ∃ a : ℂ, ρ z = a • (1 : Module.End ℂ V) := by
  let f := IntertwiningMap.centralMul (ρ := ρ) z hz
  obtain ⟨a, ha⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  exact ⟨a, (congrArg IntertwiningMap.toLinearMap ha).symm⟩

private def standardRep {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  ((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ).toMonoidHom.comp ρ

private def standardRepEquiv {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : ρ ≃ₗ standardRep ρ := by
  refine Representation.RepEquiv.mk (Module.finBasis ℂ V).equivFun ?_
  intro g
  ext v
  simp [standardRep, LinearEquiv.conjAlgEquiv]

private theorem character_irreducible {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [hρ : ρ.IsIrreducible] :
    IsIrreducibleCharacter ρ.character := by
  let e := standardRepEquiv ρ
  let σ := standardRep ρ
  have hσ : σ.IsIrreducible := (Representation.RepEquiv.irreducible_euqiv e).mp hρ
  exact ⟨Module.finrank ℂ V, σ, hσ,
    Representation.char_iso e.toRepresentationEquiv⟩

private theorem ind_character {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) (σ : Representation ℂ H V) :
    (Representation.ind H.subtype σ).character = inducedClassFunction H σ.character := by
  classical
  funext g
  rw [Representation.induced_character_formula]
  unfold inducedClassFunction
  congr 1
  rw [Subsingleton.elim (Fintype.ofFinite G) (inferInstance : Fintype G)]
  simpa only [Equiv.inv_apply, inv_inv] using
    Equiv.sum_comp (Equiv.inv G) (fun x : G =>
      if hx : x⁻¹ * g * x ∈ H then σ.character ⟨x⁻¹ * g * x, hx⟩ else 0)

set_option backward.isDefEq.respectTransparency false in
/-- A faithful nonlinear irreducible representation of a finite nilpotent group
is induced from an irreducible character of a proper subgroup. -/
public theorem nilpotent_faithful_proper_induction
    {G : Type*} [Group G] [Fintype G] (hG : Group.IsNilpotent G)
    (n : ℕ) (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : Representation.IsIrreducible ρ) (hf : Function.Injective ρ) (hn : n ≠ 1) :
    ∃ K : Subgroup G, K ≠ ⊤ ∧ ∃ ψ : ClassFunction K,
      IsIrreducibleCharacter ψ ∧ ρ.character = inducedClassFunction K ψ := by
  classical
  let := hG
  let := hρ
  have hncomm : ¬ IsMulCommutative G := by
    intro hc
    let := hc
    exact hn (by simpa using IsIrreducible.finrank_eq_one_of_isMulCommutative ρ)
  obtain ⟨x, hx₂, hxZ⟩ := Group.exists_mem_upperCentralSeries_two_not_mem_center hncomm
  let H := Subgroup.centralizer ({x} : Set G)
  let : H.Normal := Group.normal_centralizer_singleton_of_mem_upperCentralSeries_two x hx₂
  have hH : H ≠ ⊤ := by
    intro he
    apply hxZ
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ H := he ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hxH : x ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let xH : H := ⟨x, hxH⟩
  have hxZH : xH ∈ Subgroup.center H := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.property
  let : Nontrivial (Fin n → ℂ) := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨M, hM⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (ρ.comp H.subtype)
  let := hM
  let : FiniteDimensional ℂ M.toSubmodule :=
    FiniteDimensional.of_injective M.toSubmodule.subtype Subtype.val_injective
  let : Nontrivial M.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial M.toRepresentation
  have hnconj : ∀ g : G, (g : G ⧸ H) ≠ 1 →
      ¬ Nonempty (M.toRepresentation ≃ₗ conjugateRep M.toRepresentation g) := by
    intro g hg ⟨e⟩
    obtain ⟨a, ha⟩ := central_scalar M.toRepresentation hxZH
    have hconj : ∀ w : M.toSubmodule,
        (conjugateRep M.toRepresentation g) xH w = M.toRepresentation xH w := by
      intro w
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [← e.isIntertwining, ha]
      exact e.toLinearEquiv.map_smul a v
    let c := ⁅g, x⁆
    have hcZ : c ∈ Subgroup.center G := by
      have hxg := (Subgroup.mem_upperCentralSeries_succ_iff.mp hx₂) g
      have : ⁅x, g⁆ ∈ Subgroup.center G := by simpa using hxg
      simpa only [commutatorElement_inv] using (Subgroup.center G).inv_mem this
    obtain ⟨b, hb⟩ := central_scalar ρ hcZ
    obtain ⟨w, hw⟩ := exists_ne (0 : M.toSubmodule)
    have hwval : (w : Fin n → ℂ) ≠ 0 := fun he => hw (Subtype.ext he)
    have hv : ρ x (w : Fin n → ℂ) ≠ 0 := by
      intro he
      apply hwval
      exact (Representation.apply_bijective ρ x).injective (he.trans (map_zero _).symm)
    have hfix : ρ c (ρ x (w : Fin n → ℂ)) = ρ x (w : Fin n → ℂ) := by
      have hh := congrArg Subtype.val (hconj w)
      change ρ (g * x * g⁻¹) (w : Fin n → ℂ) = ρ x (w : Fin n → ℂ) at hh
      calc
        ρ c (ρ x (w : Fin n → ℂ)) = ρ (c * x) (w : Fin n → ℂ) := by
          rw [map_mul]; rfl
        _ = ρ (g * x * g⁻¹) (w : Fin n → ℂ) := by
          congr 2
          simp [c, commutatorElement_def, mul_assoc]
        _ = ρ x (w : Fin n → ℂ) := hh
    have hb1 : b = 1 := by
      have hsmul : b • ρ x (w : Fin n → ℂ) = (1 : ℂ) • ρ x (w : Fin n → ℂ) := by
        simpa [hb] using hfix
      exact (smul_left_injective ℂ hv) hsmul
    have hc1 : c = 1 := hf (by simp [hb, hb1])
    have hgH : g ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hc1)
    exact hg (QuotientGroup.eq_one_iff g |>.mpr hgH)
  let ecoind := coindEquivOfSubrep_noNontrivialConj ρ (Or.inl ringChar.eq_zero) M hnconj
  refine ⟨H, hH, M.toRepresentation.character, character_irreducible _, ?_⟩
  let τ : Representation ℂ G (Representation.coindV H.subtype M.toRepresentation) :=
    Representation.coind H.subtype M.toRepresentation
  calc
    ρ.character = τ.character :=
      Representation.char_iso (ρ := ρ)
        (W := Representation.coindV H.subtype M.toRepresentation) (σ := τ) ecoind.toRepresentationEquiv
    _ = (Representation.ind H.subtype M.toRepresentation).character :=
      by
        have he := Representation.char_iso
          (ρ := Representation.ind H.subtype M.toRepresentation)
          (W := Representation.coindV H.subtype M.toRepresentation) (σ := τ)
          (indCoindEquiv H M.toRepresentation)
        exact he.symm
    _ = inducedClassFunction H M.toRepresentation.character := ind_character H _
end Theory.Character
