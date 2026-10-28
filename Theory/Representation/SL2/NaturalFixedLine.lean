module
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Theory.Representation.SL2.NaturalHomogeneous
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.MarkedAlternatives

/-!
# Fixed lines in homogeneous natural modules

A two-group acting on the copies of a natural SL₂ constituent has a fixed
copy inside any invariant subspace containing that constituent. The selected
copy retains the canonical semilinear action. If an elementary actor has a
one-dimensional binary fixed space on the larger subspace, the fixed field
on the selected copy forces the coefficient field to have order at most four.
Clifford homogeneity extends the obstruction to every nonzero invariant part
of an irreducible ambient module.

Source: Aschbacher--Smith D.2.9(6), D.3.9 and D.3.21, printed pp.182--183,
199--201 and204--207; the semilinear fixed-line estimate is G.11.7.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups MonoidAlgebra
namespace Representation.SL2AutomorphismNatural
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2]
  [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance naturalFixedLineAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

omit [Finite G] in
/-- A two-subgroup fixes a natural copy inside the prescribed invariant subspace. -/
theorem fixed_natural_copy_le
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (α : G → MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (S : Subrepresentation (ρ.comp K.subtype)) (hS : S.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] S.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = S.toRepresentation k (E v))
    (B : Subgroup G) (hB : IsPGroup 2 B)
    (I : Submodule (ZMod 2) V) (hSI : S.toSubmodule ≤ I)
    (hBI : B ≤ subspaceStabilizer ρ I) :
    ∃ U : Subrepresentation (ρ.comp K.subtype), SameModule S U ∧
      U.toSubmodule ≤ I ∧ B ≤ subspaceStabilizer ρ U.toSubmodule := by
  let c := subgroupTypeAction ρ K B
  obtain ⟨U,hU,he,hu,hh⟩ := c.exists_homogeneous_copy hB S hS
  have hle : U.toSubmodule ≤ I := by
    apply (show U.toSubmodule ≤ (c.span S).toSubmodule from hU).trans
    change (⨆ b : B, c.conjugate b S).toSubmodule ≤ I
    rw [toSubmodule_iSup]
    apply iSup_le
    intro b
    change (conjugateSubrepresentationOrderIso ρ K (b : G) S).toSubmodule ≤ I
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    rintro _ ⟨v,hv,rfl⟩
    exact (hBI b.property v).2 (hSI hv)
  refine ⟨U,he,hle,?_⟩
  intro b hb
  apply (subspace_map_eq_iff ρ U.toSubmodule b).mp
  have hmem : (⟨b,hb⟩ : B) ∈ c.inertia S :=
    natural_sameModule_conjugate ρ K q α hα S E hE b
  have hmem' : (⟨b,hb⟩ : B) ∈ c.inertia U := (c.inertia_eq_of_sameModule he) ▸ hmem
  have hfix := (c.homogeneous_iff_inertia_fixes U hu).mp hh ⟨b,hb⟩ hmem'
  exact (conjugateSubrepresentationOrderIso_toSubmodule ρ K b U).symm.trans
    (congrArg Subrepresentation.toSubmodule hfix)

/-- A natural constituent inside an invariant subspace with a binary fixed line
forces the coefficient field to have order at most four. -/
theorem card_le_four_of_natural_fixed_line
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q) (α : G → MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (S : Subrepresentation (ρ.comp K.subtype)) (hS : S.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] S.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = S.toRepresentation k (E v))
    (B : Subgroup G) [IsElementaryAbelian 2 B]
    (I : Submodule (ZMod 2) V) (hSI : S.toSubmodule ≤ I)
    (hBI : B ≤ subspaceStabilizer ρ I)
    (hline : Module.finrank (ZMod 2) (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) = 1) :
    Nat.card F ≤ 4 := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨U,he,hUI,hBU⟩ := fixed_natural_copy_le ρ K q α hα S hS E hE B
    (IsElementaryAbelian.isPGroup 2 B) I hSI hBI
  obtain ⟨e,he⟩ := he
  let E' := E.trans e
  have hE' (k : K) (v : Fin 2 → F) :
      E' ((q k).val.mulVec v) = U.toRepresentation k (E' v) := by
    change e (E ((q k).val.mulVec v)) = _
    rw [hE,he]
    rfl
  let τ := (invariantSubspace ρ B U.toSubmodule hBU).toRepresentation
  let ν : Representation (ZMod 2) B (Fin 2 → F) :=
    (E'.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp τ
  have hν (b : B) (v : Fin 2 → F) : E' (ν b v) = τ b (E' v) :=
    E'.apply_symm_apply _
  have hcov (b : B) (g : SL(2,F)) (v : Fin 2 → F) :
      ν b (g.val.mulVec v) = (α b g).val.mulVec (ν b v) := by
    obtain ⟨k,rfl⟩ := hq g
    apply E'.injective
    rw [hν,←hα b k,hE',hE']
    rw [hν]
    apply Subtype.ext
    change ρ b (ρ k (E' v : V)) = ρ (b * (k : G) * (b : G)⁻¹) (ρ b (E' v : V))
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hsemi : ∀ b : B, ∃ σ : F ≃+* F, ∀ c v, ν b (c • v) = σ c • ν b v := by
    intro b
    exact OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (specialLinearNatural 2 (k := F))
      (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf) (α b)
      (LinearEquiv.ofBijective (ν b) (ν.apply_bijective b)) (hcov b)
  have hdim : Module.finrank (ZMod 2) (fixedSpace ν ⊤) ≤ 1 := by
    let f : fixedSpace ν ⊤ →ₗ[ZMod 2] (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) := {
      toFun v := ⟨(E' v : V),hUI (E' v).property,by
        intro b
        have hv := v.property (⟨b,mem_top b⟩ : (⊤ : Subgroup B))
        change ν b (v : Fin 2 → F) = v at hv
        have hh := hν b v
        rw [hv] at hh
        exact congrArg Subtype.val hh.symm⟩
      map_add' _ _ := by
        apply Subtype.ext
        exact congrArg (fun z : U.toSubmodule => (z : V)) (map_add E' _ _)
      map_smul' _ _ := by
        apply Subtype.ext
        exact congrArg (fun z : U.toSubmodule => (z : V)) (map_smul E' _ _) }
    have hf : Function.Injective f := by
      intro v w hh
      apply Subtype.ext
      apply E'.injective
      have hh' : (E' (v : Fin 2 → F) : V) = (E' (w : Fin 2 → F) : V) := congrArg (fun z : (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) => (z : V)) hh
      exact Subtype.ext hh'
    exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq hline
  let : IsElementaryAbelian 2 (⊤ : Subgroup B) := IsElementaryAbelian.of_injective
    (⊤ : Subgroup B).subtype (⊤ : Subgroup B).subtype_injective
  obtain ⟨v,hv,hv0,hvf⟩ := PermutedSupports.exists_nonzero_fixed ν ⊤
    (IsElementaryAbelian.isPGroup 2 (⊤ : Subgroup B)) ⊤ top_ne_bot
    (le_subspaceStabilizer ν ⊤ (by intros; trivial))
  have hpos : 0 < Module.finrank (ZMod 2) (fixedSpace ν ⊤) := by
    exact Nat.pos_of_ne_zero (fun hz => hv0 ((Submodule.finrank_eq_zero.mp hz).le hvf))
  have hfix : fixedSpace ν ⊤ = Submodule.span (ZMod 2) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (by omega) hvf hv0
  exact MarkedSemilinearPlane.card_le_four_of_fixed_line ν hsemi ⊤ v hv0 hfix

omit [Finite G] in
/-- Every nonzero invariant subspace contains a copy of the natural normal
constituent when the ambient action is irreducible. -/
theorem exists_natural_copy_le
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (α : G → MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (S : Subrepresentation (ρ.comp K.subtype)) (hS : S.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] S.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = S.toRepresentation k (E v))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I ≠ ⊥) :
    ∃ U : Subrepresentation (ρ.comp K.subtype), U.toRepresentation.IsIrreducible ∧
      U ≤ I ∧ SameModule S U := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have ht : (normalTypeAction ρ K).inertia S = ⊤ := by
    apply top_unique
    intro a _
    exact natural_sameModule_conjugate ρ K q α hα S E hE a
  have htype := restriction_isotypic_of_typeInertia_top ρ K S hS ht
  obtain ⟨U,hU,hUI⟩ := (eq_bot_or_exists_atom_le I).resolve_left hI
  have hu := (Subrepresentation.irreducible_iff_isAtom U).mpr hU
  let := simple_asSubmodule U hu
  exact ⟨U,hu,hUI,((sameModule_iff_linearEquiv _ _).mpr (htype U.asSubmodule)).symm⟩

/-- A nonzero invariant part of a homogeneous natural restriction cannot have
a one-dimensional elementary-actor fixed space over a field larger than four. -/
theorem card_le_four_of_homogeneous_fixed_line
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q) (α : G → MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (S : Subrepresentation (ρ.comp K.subtype)) (hS : S.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] S.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = S.toRepresentation k (E v))
    (B : Subgroup G) [IsElementaryAbelian 2 B]
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I ≠ ⊥)
    (hBI : B ≤ subspaceStabilizer ρ I.toSubmodule)
    (hline : Module.finrank (ZMod 2)
      (I.toSubmodule ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) = 1) :
    Nat.card F ≤ 4 := by
  obtain ⟨U,hu,hUI,e,he⟩ := exists_natural_copy_le ρ K q α hα S hS E hE I hI
  apply card_le_four_of_natural_fixed_line ρ K q hq α hα U hu (E.trans e)
    ?_ B I.toSubmodule hUI hBI hline
  intro k v
  change e (E ((q k).val.mulVec v)) = _
  rw [hE,he]
  rfl

end Representation.SL2AutomorphismNatural
