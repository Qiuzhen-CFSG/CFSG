module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Preparation
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
/-!
# The original local residuals and their binary linear quotients

The original quotient marking restricts to a surjection from N_L(Vᵢ)
onto the corresponding concrete parabolic. Restricting this map to the
solvable residual preserves its two-group kernel. The literal block
quotient therefore identifies Lᵢ/O₂(Lᵢ) with SL₃(2) for i = 1,3 and
SL₄(2) for i = 4,6. The maps retain the original quotient projection;
no isomorphism of unrelated carriers is substituted for this action.

These quotients and perfectness supply the local-family membership
used at the beginning of 12.5.3. They do not classify its overcomponents.
Source: Aschbacher--Smith, 12.5.2 and the opening of 12.5.3, p.817.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)
def componentActor : L →* Representation.SL5TenDimensional.Group :=
  a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
theorem componentActor_surjective : Function.Surjective a.componentActor :=
  a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
theorem componentActor_ker : a.componentActor.ker = pCore 2 L := by
  rw [componentActor, MonoidHom.ker_comp_of_injective _ _ a.quotientEquiv.injective,
    QuotientGroup.ker_mk']

theorem mem_normalizer_subspace (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V)
    (l : L) : (l : G) ∈ normalizer (a.subspace W : Set G) ↔
      a.componentActor l ∈ Representation.SL5ExteriorSquare.exteriorStabilizer W := by
  constructor
  · intro h w
    let v := a.coordinates.symm (Multiplicative.ofAdd w)
    have he := a.equivariant l v
    have hm := (mem_normalizer_iff.mp h (v : G))
    rw [a.mem_subspace W v, a.mem_subspace W
      ⟨(l : G) * (v : G) * (l : G)⁻¹,
        (mem_normalizer_iff.mp (D.normalizes l.property) (v : G)).mp v.property⟩] at hm
    change Representation.SL5TenDimensional.exteriorAction 2
      (a.quotientEquiv (QuotientGroup.mk' _ l)) w ∈ W ↔ w ∈ W
    simpa only [he, v, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hm.symm
  · intro h
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      have hxV := a.subspace_le W hx
      have he := a.equivariant l ⟨x, hxV⟩
      apply (a.mem_subspace W ⟨(l : G) * x * (l : G)⁻¹,
        (mem_normalizer_iff.mp (D.normalizes l.property) x).mp hxV⟩).mpr
      rw [he]
      exact (h _).mpr ((a.mem_subspace W ⟨x, hxV⟩).mp hx)
    · intro hx
      have hxV : x ∈ V := (mem_normalizer_iff.mp (D.normalizes l.property) x).mpr
        (a.subspace_le W hx)
      have he := a.equivariant l ⟨x, hxV⟩
      apply (a.mem_subspace W ⟨x, hxV⟩).mpr
      apply (h _).mp
      have hm := (a.mem_subspace W ⟨(l : G) * x * (l : G)⁻¹,
        (mem_normalizer_iff.mp (D.normalizes l.property) x).mp hxV⟩).mp hx
      rwa [he] at hm
end ExteriorMarking

/-- Natural flag dimensions corresponding to the exterior dimensions. -/
def localFlagDimension (i : ℕ) : ℕ :=
  match i with | 1 => 2 | 3 => 3 | 4 => 1 | 6 => 4 | _ => 0

/-- The nonabelian diagonal block of each local residual. -/
def localLinearDimension (i : ℕ) : ℕ := if i = 1 ∨ i = 3 then 3 else 4

namespace ExteriorMarking
variable (a : ExteriorMarking D)

theorem mem_Gi_iff_actor (i : ℕ) (hi : LocalIndex i) (l : L) :
    (l : G) ∈ a.Gi i ↔ a.componentActor l ∈
      Representation.SL5ExteriorSquare.parabolic (localFlagDimension i) := by
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [Gi, Vi, localFlagDimension,
      ← Representation.SL5ExteriorSquare.exteriorStabilizer_V₁_eq_parabolic] using
      a.mem_normalizer_subspace Representation.SL5ExteriorSquare.V₁ l
  · simpa only [Gi, Vi, localFlagDimension,
      ← Representation.SL5ExteriorSquare.exteriorStabilizer_V₃_eq_parabolic] using
      a.mem_normalizer_subspace Representation.SL5ExteriorSquare.V₃ l
  · simpa only [Gi, Vi, localFlagDimension,
      ← Representation.SL5ExteriorSquare.exteriorStabilizer_V₄_eq_parabolic] using
      a.mem_normalizer_subspace Representation.SL5ExteriorSquare.V₄ l
  · simpa only [Gi, Vi, localFlagDimension,
      ← Representation.SL5ExteriorSquare.exteriorStabilizer_V₆_eq_parabolic] using
      a.mem_normalizer_subspace Representation.SL5ExteriorSquare.V₆ l

def localActor (i : ℕ) (hi : LocalIndex i) :
    (L ⊓ a.Gi i : Subgroup G) →*
      Representation.SL5ExteriorSquare.parabolic (localFlagDimension i) :=
  (a.componentActor.comp (Subgroup.inclusion inf_le_left)).codRestrict _
    (fun l => (a.mem_Gi_iff_actor i hi ⟨l, l.property.1⟩).mp l.property.2)

theorem localActor_surjective (i : ℕ) (hi : LocalIndex i) :
    Function.Surjective (a.localActor i hi) := by
  intro g
  obtain ⟨l, hl⟩ := a.componentActor_surjective g.val
  exact ⟨⟨l, l.property, (a.mem_Gi_iff_actor i hi l).mpr (hl ▸ g.property)⟩,
    Subtype.ext hl⟩

theorem localActor_ker (i : ℕ) (hi : LocalIndex i) :
    (a.localActor i hi).ker = (pCore 2 L).comap (Subgroup.inclusion inf_le_left) := by
  ext x
  change (a.localActor i hi x = 1) ↔ _
  rw [Subtype.ext_iff]
  change a.componentActor (Subgroup.inclusion inf_le_left x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, a.componentActor_ker]
  rfl

theorem localActor_ker_isPGroup (i : ℕ) (hi : LocalIndex i) :
    IsPGroup 2 (a.localActor i hi).ker := by
  rw [a.localActor_ker i hi]
  exact pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective inf_le_left)

variable [Finite G]

def LiEquivResidual (i : ℕ) :
    a.Li i ≃* solvableResidual (L ⊓ a.Gi i : Subgroup G) :=
  ((solvableResidual (L ⊓ a.Gi i : Subgroup G)).equivMapOfInjective
    _ (L ⊓ a.Gi i).subtype_injective).symm

def modelResidualEquiv (k : ℕ) :
    solvableResidual (Representation.SL5ExteriorSquare.parabolic k) ≃*
      Representation.SL5ExteriorSquare.parabolicResidual k :=
  (solvableResidual (Representation.SL5ExteriorSquare.parabolic k)).equivMapOfInjective
    _ (Representation.SL5ExteriorSquare.parabolic k).subtype_injective

def residualActor (i : ℕ) (hi : LocalIndex i) :
    a.Li i →* Representation.SL5ExteriorSquare.parabolicResidual (localFlagDimension i) :=
  (modelResidualEquiv (localFlagDimension i)).toMonoidHom.comp
    ((a.localActor i hi).solvableResidualMap.comp (a.LiEquivResidual i).toMonoidHom)

theorem residualActor_surjective (i : ℕ) (hi : LocalIndex i) :
    Function.Surjective (a.residualActor i hi) :=
  (modelResidualEquiv (localFlagDimension i)).surjective.comp
    (((a.localActor i hi).solvableResidualMap_surjective
      (a.localActor_surjective i hi)).comp (a.LiEquivResidual i).surjective)

omit [Finite G] in
theorem residualActor_ker_isPGroup (i : ℕ) (hi : LocalIndex i) :
    IsPGroup 2 (a.residualActor i hi).ker := by
  rw [residualActor, MonoidHom.ker_comp_of_injective _ _ (modelResidualEquiv _).injective,
    ← MonoidHom.comap_ker]
  exact ((a.localActor i hi).solvableResidualMap_ker_isPGroup
    (a.localActor_ker_isPGroup i hi)).comap_of_injective _ (a.LiEquivResidual i).injective

omit [Finite G] in
/-- The residual map is the restriction of the original quotient actor. -/
theorem residualActor_apply (i : ℕ) (hi : LocalIndex i) (l : a.Li i) :
    (a.residualActor i hi l : Representation.SL5TenDimensional.Group) =
      a.componentActor ⟨l, a.Li_le_L i l.property⟩ := by
  have hr := congrArg Subtype.val ((a.LiEquivResidual i).symm_apply_apply l)
  change (((a.LiEquivResidual i l).val : (L ⊓ a.Gi i : Subgroup G)) : G) = l.val at hr
  change a.componentActor ⟨(a.LiEquivResidual i l).val, _⟩ = _
  apply congrArg a.componentActor
  exact Subtype.ext hr

/-- Perfectness of the literal embedded terminal derived subgroup. -/
theorem Li_perfect (i : ℕ) : Group.IsPerfect (a.Li i) :=
  Group.IsPerfect.ofSurjective
    (f := ((solvableResidual (L ⊓ a.Gi i : Subgroup G)).equivMapOfInjective
      _ (L ⊓ a.Gi i).subtype_injective).toMonoidHom)
    (equivMapOfInjective _ _ _).surjective
end ExteriorMarking

open Representation.SL5ExteriorSquare
def localModelQuotient (i : ℕ) (hi : LocalIndex i) :
    (parabolicResidual (localFlagDimension i) ⧸
      (parabolicResidualTwoCore (localFlagDimension i)).subgroupOf
        (parabolicResidual (localFlagDimension i))) ≃*
      SL(localLinearDimension i, ZMod 2) := by
  classical
  by_cases h1 : i = 1
  · subst i; exact parabolicTwoResidualQuotientEquiv
  by_cases h3 : i = 3
  · subst i; exact parabolicThreeResidualQuotientEquiv
  by_cases h4 : i = 4
  · subst i; exact parabolicOneResidualQuotientEquiv
  have h6 : i = 6 := hi.resolve_left h1 |>.resolve_left h3 |>.resolve_left h4
  subst i
  exact parabolicFourResidualQuotientEquiv

namespace ExteriorMarking
variable [Finite G] (a : ExteriorMarking D)
def LiLinearHom (i : ℕ) (hi : LocalIndex i) :
    a.Li i →* SL(localLinearDimension i, ZMod 2) :=
  (localModelQuotient i hi).toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (a.residualActor i hi))

theorem LiLinearHom_surjective (i : ℕ) (hi : LocalIndex i) :
    Function.Surjective (a.LiLinearHom i hi) :=
  (localModelQuotient i hi).surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (a.residualActor_surjective i hi))

omit [Finite G] in
theorem LiLinearHom_ker_isPGroup (i : ℕ) (hi : LocalIndex i) :
    IsPGroup 2 (a.LiLinearHom i hi).ker := by
  rw [LiLinearHom, MonoidHom.ker_comp_of_injective _ _ (localModelQuotient i hi).injective,
    ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact (pCore_isPGroup.map (parabolicResidualFlag (localFlagDimension i)).subtype).comap_subtype.comap_of_ker_isPGroup
    (a.residualActor i hi) (a.residualActor_ker_isPGroup i hi)

private theorem binaryLinear_twoCore (n : ℕ) : pCore 2 SL(n, ZMod 2) = ⊥ := by
  apply Subgroup.map_injective (f := (BinaryLinear.OuterCyclic.slEquivLinear n).toMonoidHom)
    (BinaryLinear.OuterCyclic.slEquivLinear n).injective
  rw [pCore_map_iso, Subgroup.map_bot]
  exact BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot

def LiCoreEquiv (i : ℕ) (hi : LocalIndex i) :
    (a.Li i ⧸ pCore 2 (a.Li i)) ≃* SL(localLinearDimension i, ZMod 2) :=
  ((a.LiLinearHom i hi).pCoreQuotientEquiv (a.LiLinearHom_surjective i hi)
    (a.LiLinearHom_ker_isPGroup i hi)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by exact binaryLinear_twoCore _)).trans
      QuotientGroup.quotientBot)

theorem LiCoreEquiv_mk (i : ℕ) (hi : LocalIndex i) (l : a.Li i) :
    a.LiCoreEquiv i hi (QuotientGroup.mk' _ l) = a.LiLinearHom i hi l := rfl

theorem Li_core_quasisimple (i : ℕ) (hi : LocalIndex i) :
    IsQuasisimple (a.Li i ⧸ pCore 2 (a.Li i)) := by
  have hn : 3 ≤ localLinearDimension i := by simp only [localLinearDimension]; split <;> omega
  let : IsQuasisimple SL(localLinearDimension i, ZMod 2) := {
    toIsPerfect := Atlas.sl_perfect _ hn
    simple := Atlas.psl_simple_high_rank _ hn }
  exact IsQuasisimple.of_mulEquiv (a.LiCoreEquiv i hi).symm
end ExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
