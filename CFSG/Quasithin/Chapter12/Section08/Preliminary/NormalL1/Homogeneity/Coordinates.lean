module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Actions
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Dimension
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Finite homogeneous coordinates from seed intertwiners

For the literal tilded conjugate span, a simple seed and equivalence of its
conjugation twists give injective intertwining maps whose ranges span the
whole module. Its seed isotypic component is therefore the whole module,
so it is semisimple and admits a finite direct sum of copies of the seed.
The resulting linear equivalence retains the actual quotient-action equations.

The final theorem applies this construction with J=G₁ to the commutator-form
dimension obstruction. The marked actor surjects onto GL_(n-1)(2) only for
n>3, using perfectness; the cyclic-three actor at n=3 is not enlarged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 12.8.5(1) and 12.8.8(5), printed pp.850–852 (PDF pp.867–869).
These are conditional implications. Seed simplicity and the conjugation
intertwiners must still be deduced from the marked natural action and the
actual ambient Sylow subgroup before asserting the source homogeneity theorem.
The elementary quotients and invariant form remain earlier-source inputs.
-/

@[expose] public section

open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsMulCommutative V]

/-- Orbit intertwiners for a simple seed yield actual finite homogeneous coordinates.
The Sylow and model argument supplying these intertwiners is a separate obligation. -/
theorem homogeneous_coordinates_of_seed_intertwiners (L J : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (hJH : J ≤ F.H) (hKJ : F.Li L 1 ≤ J)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G))
    [IsElementaryAbelian 2 (F.tilde V)] [IsElementaryAbelian 2 (F.tilde (F.UH J))]
    (hsimple : IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule)
    (htwist : ∀ j : J, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v)) :
    ∃ r : ℕ, ∃ e : Additive (F.tilde (F.UH J)) ≃ₗ[ZMod 2] (Fin r → Additive (F.tilde V)),
      ∀ (k : F.Li L 1) u i,
        e (Additive.ofMul (F.localTildeAction J hJH (inclusion hKJ k) u.toMul)) i =
          Additive.ofMul (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
            ((F.Li_le L 1).trans (inf_le_left.trans hLV)) k (e u i).toMul) := by
  classical
  let σ := F.localSeedRepresentation L hLV
  let ρ := F.localSpanRepresentation J hJH
  let τ : Representation (ZMod 2) (F.Li L 1) (Additive (F.tilde (F.UH J))) :=
    ρ.comp (inclusion hKJ)
  let ι := F.localSeedInclusion J
  let c (j : J) := (htwist j).choose
  have hc (j : J) (k : F.Li L 1) (v : Additive (F.tilde V)) :
      c j (σ k v) = σ (F.localConjugation L J hJK j k) (c j v) :=
    (htwist j).choose_spec k v
  let f (j : J) : σ.IntertwiningMap τ :=
    { toLinearMap := (ρ j⁻¹).comp (ι.comp (c j).toLinearMap)
      isIntertwining' k := by
        apply LinearMap.ext
        intro v
        change ρ j⁻¹ (ι (c j (σ k v))) = ρ (inclusion hKJ k) (ρ j⁻¹ (ι (c j v)))
        rw [hc, F.localSeedInclusion_equivariant L J hLV hJH hKJ]
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        apply Subtype.ext
        simp [F.localConjugation_apply, mul_assoc] }
  have hf (j : J) : Function.Injective (f j) :=
    (Representation.apply_bijective ρ j⁻¹).injective.comp
      ((F.localSeedInclusion_injective J).comp (c j).injective)
  let fA (j : J) := Representation.IntertwiningMap.equivLinearMapAsModule σ τ (f j)
  have hfA (j : J) : Function.Injective (fA j) := hf j
  let C := isotypicComponent (ZMod 2)[F.Li L 1] τ.asModule σ.asModule
  have hC (j : J) : LinearMap.range (fA j) ≤ C :=
    le_sSup ⟨(LinearEquiv.ofInjective (fA j) (hfA j)).symm⟩
  have htop : C = ⊤ := by
    let S : Submodule (ZMod 2) (Additive (F.tilde (F.UH J))) :=
      (C.restrictScalars (ZMod 2)).comap τ.asModuleEquiv.symm.toLinearMap
    have horbit : Submodule.span (ZMod 2) {u | ∃ j v, ρ j (ι v) = u} ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, v, rfl⟩
      apply hC j⁻¹
      refine ⟨σ.asModuleEquiv.symm ((c j⁻¹).symm v), ?_⟩
      change ρ (j⁻¹)⁻¹ (ι (c j⁻¹ ((c j⁻¹).symm v))) = ρ j (ι v)
      rw [inv_inv, LinearEquiv.apply_symm_apply]
    have hS : S = ⊤ := top_unique (F.localSeed_orbit_span J hJH ▸ horbit)
    apply top_unique
    intro u _
    have hu : τ.asModuleEquiv u ∈ S := hS ▸ Submodule.mem_top
    exact hu
  let : IsSimpleModule (ZMod 2)[F.Li L 1] σ.asModule := hsimple
  let eTop := (LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv
  let : IsSemisimpleModule (ZMod 2)[F.Li L 1] τ.asModule :=
    IsSemisimpleModule.congr (M := C) eTop.symm
  let : Module.Finite (ZMod 2) τ.asModule := inferInstance
  let : Module.Finite (ZMod 2)[F.Li L 1] τ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  obtain ⟨r, ⟨e⟩⟩ := (IsIsotypicOfType.of_isotypicComponent_eq_top htop).linearEquiv_fun
  let eU := τ.asModuleEquiv.symm.trans ((e.restrictScalars (ZMod 2)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin r => σ.asModuleEquiv)))
  refine ⟨r, eU, ?_⟩
  intro k u i
  have he := congrArg (fun v : Fin r → σ.asModule => σ.asModuleEquiv (v i))
    (e.map_smul (MonoidAlgebra.of (ZMod 2) (F.Li L 1) k) (τ.asModuleEquiv.symm u))
  change σ.asModuleEquiv (e (τ.asModuleEquiv.symm (τ k u)) i) =
    σ k (σ.asModuleEquiv (e (τ.asModuleEquiv.symm u) i))
  rw [Representation.asModuleEquiv_symm_map_rho]
  simpa only [Pi.smul_apply, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of] using he


end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Subgroup
open scoped IsMulCommutative MonoidAlgebra
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable {F : InvariantFlag T V n} {L : Subgroup G}
variable {hLV : L ≤ normalizer (V : Set G)} [IsElementaryAbelian 2 (F.tilde V)]

namespace NaturalSeedMarking

/-- The literal quotient marking followed by the natural derived-group representation. -/
noncomputable def naturalActor (D : F.NaturalSeedMarking L hLV) :
    F.Li L 1 →* BinaryLinear.OuterCyclic.LinearGroup (n - 1) :=
  (commutator (BinaryLinear.OuterCyclic.LinearGroup (n - 1))).subtype.comp
    (D.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (F.Li L 1))))

/-- Only above dimension two is the marked derived actor the full linear group. -/
theorem naturalActor_surjective (D : F.NaturalSeedMarking L hLV) (hn : 3 < n) :
    Function.Surjective D.naturalActor := by
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup (n - 1)) :=
    BinaryLinear.linearGroup_isPerfect (n - 1) (by omega)
  intro g
  obtain ⟨q, hq⟩ := D.quotientEquiv.surjective ⟨g, Group.IsPerfect.mem_commutator⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  exact ⟨k, congrArg Subtype.val hq⟩

end NaturalSeedMarking

variable [Finite G] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 (F.tilde F.U)]

/-- Actual J=G₁ application: simple untwisted seed conjugates produce the eU
coordinates required by the commutator-form dimension obstruction. No coordinates
for Ũ are assumed. The seed-intertwiner premise remains a separate obligation. -/
theorem nonabelian_exclusion_of_seed_intertwiners (hn : 3 < n)
    (D : F.NaturalSeedMarking L hLV)
    (hHK : F.H ≤ normalizer (F.Li L 1 : Set G))
    (hsimple : IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule)
    (htwist : ∀ j : F.H, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L F.H hHK j k) (c v))
    (B : LinearMap.BilinForm (ZMod 2) (Additive (F.tilde F.U)))
    (hB : ∀ (j : F.Li L 1) u v,
      B (Additive.ofMul (F.localTildeAction F.H le_rfl
        ⟨j, (F.Li_le L 1 j.property).2⟩ u.toMul))
        (Additive.ofMul (F.localTildeAction F.H le_rfl
          ⟨j, (F.Li_le L 1 j.property).2⟩ v.toMul)) = B u v)
    (hrad : ∀ v : Additive (F.tilde F.U),
      (∀ u, B u v = 0) ↔ (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU)
    (hnonab : ¬ IsMulCommutative F.U) : False := by
  let : IsElementaryAbelian 2 (F.tilde (F.UH F.H)) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.tilde F.U))
  obtain ⟨r, e, he⟩ := F.homogeneous_coordinates_of_seed_intertwiners L F.H hLV le_rfl
    ((F.Li_le L 1).trans inf_le_right) hHK hsimple htwist
  let eU : Additive (F.tilde F.U) ≃ₗ[ZMod 2] (Fin r → Fin (n - 1) → ZMod 2) :=
    e.trans (LinearEquiv.piCongrRight (fun _ => D.coordinates))
  apply F.nonabelian_homogeneous_natural_exclusion L hLV hn r D.naturalActor
    (D.naturalActor_surjective hn) D.coordinates eU
    (fun j v => D.equivariant j v) ?_ B hB hrad hnonab
  intro j u i
  change D.coordinates (e (Additive.ofMul
    (F.localTildeAction F.H le_rfl ⟨j, (F.Li_le L 1 j.property).2⟩ u.toMul)) i) = _
  exact (congrArg D.coordinates (he j u i)).trans (D.equivariant j (e u i))

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
