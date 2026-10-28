module
public import Theory.Representation.HexacodeAction.SmallInvolution.Descent
public import Theory.Representation.HexacodeAction.InvariantForms

/-!
# Cubic descent from a small moving quotient with invariant forms

A fully moved binary module with no fixed vectors and an even involution
of displacement at most three has only one nontrivial simple constituent.
The two-group kernel of the actual even-cover projection therefore acts
trivially. If the cubic center survived, the faithful-degree calculation
would give the six-dimensional hexacode: three conjugate involutions bound
the degree by nine, excluding degree eighteen. Separating invariant bilinear
forms exclude that hexacode action. Thus the original projection's cubic
center acts trivially, without identifying the cover itself with A6.

Source: the self-dual constituent argument of Meierfrankenfeld--Stellmacher
(1993), (3.8), printed pp.878--879. The concrete cover results retain the
ATLAS attribution documented in their imported modules.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace Representation.Hexacode.SmallInvolution

variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
private theorem full_quotient_of_full
    (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (N : Subrepresentation ρ) :
    subspaceCommutator N.quotientRepresentation ⊤ ⊤ = ⊤ := by
  have h : subspaceCommutator ρ ⊤ ⊤ ≤
      (subspaceCommutator N.quotientRepresentation ⊤ ⊤).comap N.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    change N.toSubmodule.mkQ (ρ g v - v) ∈ subspaceCommutator N.quotientRepresentation ⊤ ⊤
    rw [map_sub,←N.quotientRepresentation_mk]
    exact Submodule.subset_span ⟨g,hg,N.toSubmodule.mkQ v,Submodule.mem_top,rfl⟩
  rw [hfull] at h
  apply top_unique
  intro q _
  obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective q
  exact h Submodule.mem_top

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
private theorem action_ne_one_of_full [Nontrivial W]
    (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) : ρ ≠ 1 := by
  intro he
  have hz : subspaceCommutator ρ ⊤ ⊤ ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    simp [he]
  rw [hfull] at hz
  exact top_ne_bot (le_bot_iff.mp hz)

private theorem even_projected_irreducible_three [Nontrivial W]
    (π : H →* HexEvenAutomorphisms) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup H) (t : HexEvenAutomorphisms) (ht : orderOf t = 2)
    (htA : t ∈ A.map π) (hcost : fixedCodim ρ A ≤ 3) : IsIrreducible ρ := by
  let f := hexSign.ker.subtype.comp π
  have hE : hexSign.ker ≤ f.range := by
    intro g hg
    obtain ⟨x,hx⟩ := hπ ⟨g,hg⟩
    exact ⟨x,congrArg Subtype.val hx⟩
  have hpf : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ hexSign.ker.subtype_injective]
    exact hp
  have hAE : A.map f ≤ hexSign.ker := by
    rintro _ ⟨x,_,rfl⟩
    exact (π x).property
  have htAf : t.val ∈ A.map f := by
    obtain ⟨x,hx,hxt⟩ := htA
    exact ⟨x,hx,congrArg Subtype.val hxt⟩
  obtain ⟨N,hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let := hN
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  have hn : N.toRepresentation ≠ 1 := by
    intro he
    obtain ⟨v,hv⟩ := exists_ne (0 : N.toSubmodule)
    apply hv
    apply Subtype.ext
    have hh : v.val ∈ fixedSpace ρ ⊤ := by
      intro g
      exact congrArg Subtype.val (LinearMap.congr_fun
        (congrArg (fun σ => σ g.val) he) v)
    change v.val = 0
    simpa only [hfix,Submodule.mem_bot] using hh
  have hlo := projected_simple_fixedCodim_lower f hE hpf N.toRepresentation hn A hAE t ht htAf
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ N A
  have hsmall : fixedCodim N.quotientRepresentation A ≤ 1 := by omega
  have htop : N = ⊤ := by
    by_contra hne
    have hnsub : N.toSubmodule ≠ ⊤ := fun he => hne (Subrepresentation.toSubmodule_injective he)
    let : Nontrivial (W ⧸ N.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hnsub
    let : IsCoatomic (Subrepresentation N.quotientRepresentation) :=
      SimpleHeadQuotient.subrepresentation_coatomic _
    obtain ⟨D,hD,_⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation N.quotientRepresentation)).resolve_left bot_ne_top
    let := SimpleHeadQuotient.irreducible_quotient_of_isCoatom D hD
    let := Subrepresentation.irreducible_module_nontrivial D.quotientRepresentation
    have hd := full_quotient_of_full N.quotientRepresentation (full_quotient_of_full ρ hfull N) D
    have hlow := projected_simple_fixedCodim_lower f hE hpf D.quotientRepresentation
      (action_ne_one_of_full D.quotientRepresentation hd) A hAE t ht htAf
    have hupper := fixedCodim_quotient_add_subrepresentation_le N.quotientRepresentation D A
    omega
  exact isSimpleOrder_iff_isAtom_top.mpr
    (htop ▸ (Subrepresentation.irreducible_iff_isAtom N).mp hN)

/-- A literal even-cover projection with two-group kernel kills its cubic
center on a fully moved module with cost at most three and separating
invariant forms. The conclusion concerns the original actor action. -/
theorem projected_center_le_ker_of_separating_forms
    (π : H →* HexEvenAutomorphisms) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup H) (t : HexEvenAutomorphisms) (ht : orderOf t = 2)
    (htA : t ∈ A.map π) (hcost : fixedCodim ρ A ≤ 3)
    (forms : Set (LinearMap.BilinForm (ZMod 2) W))
    (hsep : ∀ v, (∀ B ∈ forms, ∀ w, B v w = 0) → v = 0)
    (hinv : ∀ g : H, ∀ B ∈ forms, ∀ v w, B (ρ g v) (ρ g w) = B v w) :
    (center HexEvenAutomorphisms).comap π ≤ ρ.ker := by
  classical
  rcases subsingleton_or_nontrivial W with hsub | hnon
  · let := hsub
    intro g _
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _
  let := hnon
  let : IsIrreducible ρ := even_projected_irreducible_three π hπ hp ρ hfull hfix A t ht htA hcost
  let σ := BinaryLinearThree.ResidualFFForms.irreducibleDescent π hπ hp ρ
  have hcomp : σ.comp π = ρ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_comp π hπ hp ρ
  let : IsIrreducible σ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_irreducible π hπ hp ρ
  have hcenter : center HexEvenAutomorphisms ≤ σ.ker := by
    by_contra hn
    have hf := faithful_of_center_not_le_ker σ hn
    have hnσ : σ ≠ 1 := by
      intro he
      apply action_ne_one_of_full ρ hfull
      rw [←hcomp,he]
      rfl
    have hmono : fixedCodim σ (zpowers t) ≤ fixedCodim σ (A.map π) := by
      have hm := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr htA))
      have h₁ := fixedCodim_add_finrank σ (zpowers t)
      have h₂ := fixedCodim_add_finrank σ (A.map π)
      omega
    have hcostσ : fixedCodim σ (A.map π) = fixedCodim ρ A := by
      rw [←hcomp]
      unfold fixedCodim
      rw [fixedSpace_comp_map]
    have hdim := finrank_le_three_mul σ (simple_fixedSpace_eq_bot σ hnσ) t ht
    have hd : Module.finrank (ZMod 2) W = 6 := by
      have hdegrees := TwelveDimensional.faithful_finrank_six_or_eighteen σ hf
      change Module.finrank (ZMod 2) W = 6 ∨ Module.finrank (ZMod 2) W = 18 at hdegrees
      omega
    obtain ⟨a,E,hE⟩ := EvenBinaryRecognition.exists_equivariant σ hf inferInstance hd
    let f := hexSign.ker.subtype.comp (a.toMonoidHom.comp π)
    have hfonto : hexSign.ker ≤ f.range := by
      intro g hg
      obtain ⟨x,hx⟩ := a.surjective.comp hπ ⟨g,hg⟩
      exact ⟨x,congrArg Subtype.val hx⟩
    have hcoord (g : H) (v : W) : E (ρ g v) = action (f g) (E v) := by
      rw [←hcomp]
      exact hE (π g) v
    have hzero (B : LinearMap.BilinForm (ZMod 2) W) (hB : B ∈ forms) : B = 0 :=
      invariant_bilinear_eq_zero_of_hexacode_marking ρ f hfonto E hcoord B
        (fun g v w => hinv g B hB v w)
    obtain ⟨v,hv⟩ := exists_ne (0 : W)
    apply hv
    apply hsep v
    intro B hB w
    rw [hzero B hB]
    rfl
  intro g hg
  have he : σ (π g) = 1 := hcenter hg
  change ρ g = 1
  rw [←hcomp]
  exact he

/-- Residual-invariant forms suffice: irreducibility kills the genuine
two-group kernel, and the residual surjects onto the perfect even cover. -/
theorem projected_center_le_ker_of_residual_forms
    (π : H →* HexEvenAutomorphisms) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup H) (t : HexEvenAutomorphisms) (ht : orderOf t = 2)
    (htA : t ∈ A.map π) (hcost : fixedCodim ρ A ≤ 3)
    (forms : Set (LinearMap.BilinForm (ZMod 2) W))
    (hsep : ∀ v, (∀ B ∈ forms, ∀ w, B v w = 0) → v = 0)
    (hinv : ∀ g : H, g ∈ pResidual 2 H →
      ∀ B ∈ forms, ∀ v w, B (ρ g v) (ρ g w) = B v w) :
    (center HexEvenAutomorphisms).comap π ≤ ρ.ker := by
  classical
  rcases subsingleton_or_nontrivial W with hsub | hnon
  · let := hsub
    intro g _
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _
  let := hnon
  let : IsIrreducible ρ := even_projected_irreducible_three π hπ hp ρ hfull hfix A t ht htA hcost
  let σ := BinaryLinearThree.ResidualFFForms.irreducibleDescent π hπ hp ρ
  have hcomp : σ.comp π = ρ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_comp π hπ hp ρ
  have hperfect : pResidual 2 HexEvenAutomorphisms = ⊤ := by
    let := even_isPerfect
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN htwo
    let := hN
    by_contra hn
    let : Nontrivial (HexEvenAutomorphisms ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (HexEvenAutomorphisms ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let := htwo.isNilpotent
    exact Group.IsPerfect.not_isSolvable (HexEvenAutomorphisms ⧸ N) inferInstance
  have hres : (pResidual 2 H).map π = ⊤ :=
    (map_pResidual_of_surjective 2 π hπ).trans hperfect
  apply projected_center_le_ker_of_separating_forms π hπ hp ρ hfull hfix A t ht htA hcost forms hsep
  intro g B hB v w
  obtain ⟨l,hl,he⟩ := (show π g ∈ (pResidual 2 H).map π from hres ▸ mem_top _)
  have hact : ρ l = ρ g := by
    rw [←hcomp]
    exact congrArg σ he
  rw [←hact]
  exact hinv l hl B hB v w

end Representation.Hexacode.SmallInvolution
