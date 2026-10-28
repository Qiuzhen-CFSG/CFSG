module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Setup
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.ImageHypotheses
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Exact section kernels and markings in the supplied product model

Let `E = ⟨L^B⟩` and `X = L ⊔ B`. A nontrivial action of `E` in an
irreducible binary `X`-module kills exactly `O₂(E)` when a supplied model
identifies `E/O₂(E)` with two copies of `PSL₂(2^n)`, for `n > 1`.

Normality of the action kernel and transitivity of the component orbit
prevent any component from being killed. The component dichotomy then
makes the restricted kernel central. The supplied product is centerless:
its factors are simple and inherit perfectness from the orbit.

The first coordinate of this particular model is a component. If it were
not the image of an orbit component, it would centralize every such image,
and hence the whole product, contradicting its nontrivial perfectness.
Transporting this marking along the canonical embedding gives precisely
the surviving conjugate required by `splitSectionWitness_of_lift`.
No faithfulness of the irreducible action is assumed.

Source: GLS, volume 2, Theorem 25.14, Step 2
(`refs/KGroup/GLS2/ChapterG.tex`, lines 824–849), using the genuine
component calculus of Chapter 3. The two-factor model
is an explicit input; no covering or recognition conclusion is assumed.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup.SectionReduction

private theorem orbit_le_normal {G : Type*} [Group G] (L B N : Subgroup G)
    [N.Normal] (h : L ≤ N) : componentOrbit L B ≤ N := by
  apply iSup_le
  intro b
  rintro _ ⟨l, hl, rfl⟩
  exact (inferInstance : N.Normal).conj_mem l (h hl) b

private theorem orbit_le_centralizer_ker {G Q : Type*} [Group G] [Group Q]
    (L B : Subgroup G) (hL : IsComponent G L) (f : G →* Q)
    (hn : ¬ componentOrbit L B ≤ f.ker) :
    componentOrbit L B ≤ centralizer (f.ker : Set G) := by
  have hsurv : L.map f ≠ ⊥ := fun he => hn (orbit_le_normal L B f.ker
    ((map_eq_bot_iff L).mp he))
  have hc : ⁅L, f.ker⁆ = ⊥ := component_commutator_reflects L f.ker hL f hsurv (by
    rw [(map_eq_bot_iff f.ker).mpr le_rfl]
    simp)
  exact orbit_le_normal L B _ (commutator_eq_bot_iff_le_centralizer.mp hc)

private theorem simple_perfect_center {A : Type*} [Group A] [IsSimpleGroup A]
    [Group.IsPerfect A] : center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim

private theorem model_simple {E : Type*} [Group E] (M : TwoFactorModel E) :
    IsSimpleGroup (Factor M.n) := by
  apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  rw [GaloisField.card 2 M.n (by have := M.one_lt; omega)]
  exact (show 4 = 2 ^ 2 by rfl).le.trans (Nat.pow_le_pow_right (by decide) (by
    have := M.one_lt; omega))

private theorem model_perfect {E : Type*} [Group E] [Group.IsPerfect E]
    (M : TwoFactorModel E) : Group.IsPerfect (Factor M.n) := by
  apply Group.IsPerfect.ofSurjective (f := (MonoidHom.fst _ _).comp M.projection)
  intro x
  obtain ⟨y, hy⟩ := M.projection_surjective (x, 1)
  exact ⟨y, congrArg Prod.fst hy⟩

private theorem first_factor_isComponent {A : Type*} [Group A] [IsSimpleGroup A]
    [Group.IsPerfect A] :
    IsComponent (A × A) (MonoidHom.inl A A).range := by
  let f := MonoidHom.inl A A
  have hf : Function.Injective f := fun x y he => congrArg Prod.fst he
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  let : IsQuasisimple A := {
    simple := by
      exact ((QuotientGroup.quotientMulEquivOfEq (simple_perfect_center (A := A))).trans
        QuotientGroup.quotientBot).isSimpleGroup
  }
  let : f.range.Normal := ⟨by
    rintro _ ⟨x, rfl⟩ g
    refine ⟨g.1 * x * g.1⁻¹, ?_⟩
    ext <;> simp [f]⟩
  exact ⟨(inferInstance : f.range.Normal).isSubnormal, IsQuasisimple.of_mulEquiv e⟩

private theorem exists_first_factor {E A ι : Type*} [Group E] [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A]
    (C : ι → Subgroup E) (hC : ∀ b, IsComponent E (C b)) (hgen : iSup C = ⊤)
    (π : E →* A × A) (hπ : Function.Surjective π) :
    ∃ b, (C b).map π = (MonoidHom.inl A A).range := by
  let F := (MonoidHom.inl A A).range
  have hF : IsComponent (A × A) F := first_factor_isComponent
  let : Group.IsPerfect F := hF.2.toIsPerfect
  let : Nontrivial F := (MonoidHom.ofInjective (show Function.Injective
    (MonoidHom.inl A A) from fun x y he => congrArg Prod.fst he)).symm.surjective.nontrivial
  by_contra! hn
  have hle : (⨆ b, (C b).map π) ≤ centralizer (F : Set (A × A)) := by
    apply iSup_le
    intro b
    rcases (hC b).map_surjective π hπ with hb | hb
    · rw [hb]
      exact bot_le
    · exact commutator_eq_bot_iff_le_centralizer.mp
        (hb.commutator_eq_bot_of_ne hF (hn b))
  rw [← Subgroup.map_iSup, hgen, map_top_of_surjective π hπ] at hle
  exact Group.IsPerfect.not_isMulCommutative F
    (le_centralizer_iff_isMulCommutative.mp (le_top.trans hle))

variable {G V U : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- A nontrivial irreducible ambient action kills precisely the intrinsic
two-core of the component orbit. -/
theorem orbit_ker_eq_twoCore (h : Hypotheses ρ L B a)
    (M : TwoFactorModel (componentOrbit L B))
    (τ : Representation (ZMod 2) (L ⊔ B : Subgroup G) U) [τ.IsIrreducible]
    (hn : ¬ Representation.IsTrivial (τ.comp (orbitInclusion L B))) :
    (τ.comp (orbitInclusion L B)).ker = pCore 2 (componentOrbit L B) := by
  let E := componentOrbit L B
  let X := L ⊔ B
  let i := orbitInclusion L B
  let q := QuotientGroup.mk' τ.ker
  let LX := L.subgroupOf X
  let BX := B.subgroupOf X
  have hL : IsComponent X LX := h.component.subgroupOf le_sup_left
  have hn' : ¬ componentOrbit LX BX ≤ q.ker := by
    intro he
    apply hn
    constructor
    intro x
    have hx : i x ∈ componentOrbit LX BX := by
      rw [localOrbit_eq_range]
      exact ⟨x, rfl⟩
    have hx' := he hx
    rw [QuotientGroup.ker_mk'] at hx'
    exact hx'
  have hc := orbit_le_centralizer_ker LX BX hL q hn'
  have hkcenter : (τ.comp i).ker ≤ center E := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply (Subgroup.inclusion_injective (componentOrbit_le_sup L B))
    have hy : i y ∈ componentOrbit LX BX := by
      rw [localOrbit_eq_range]
      exact ⟨y, rfl⟩
    have hx' : i x ∈ q.ker := by
      rw [QuotientGroup.ker_mk']
      exact hx
    exact (mem_centralizer_iff.mp (hc hy) (i x) hx').symm
  let : Group.IsPerfect E := h.component.orbit_isPerfect B
  let : Group.IsPerfect (Factor M.n) := model_perfect M
  let : IsSimpleGroup (Factor M.n) := model_simple M
  have hz : center (Factor M.n × Factor M.n) = ⊥ := by
    rw [Subgroup.center_prod, simple_perfect_center (A := Factor M.n)]
    simp
  apply le_antisymm ?_ (orbit_twoCore_le_ker L B τ)
  intro x hx
  rw [← M.ker_projection]
  apply mem_bot.mp
  rw [← hz]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := M.projection_surjective y
  simpa only [map_mul] using congrArg M.projection (mem_center_iff.mp (hkcenter hx) y)

private theorem conjugate_le_orbit {G : Type*} [Group G] (L B : Subgroup G) (b : B) :
    L.map (MulAut.conj (b : G)).toMonoidHom ≤ componentOrbit L B :=
  le_iSup (fun c : B => L.map (MulAut.conj (c : G)).toMonoidHom) b

omit [Finite G] in
/-- The first coordinate in the supplied model is the image of an actual
conjugate of the marked component; the model equivalence is not changed. -/
theorem exists_model_component_marking (h : Hypotheses ρ L B a)
    (M : TwoFactorModel (componentOrbit L B)) :
    ∃ b : B,
      ((L.map (MulAut.conj (b : G)).toMonoidHom).subgroupOf (componentOrbit L B)).map
        M.projection = (MonoidHom.inl (Factor M.n) (Factor M.n)).range := by
  let E := componentOrbit L B
  let C : B → Subgroup E := fun b =>
    (L.map (MulAut.conj (b : G)).toMonoidHom).subgroupOf E
  have hC : ∀ b, IsComponent E (C b) := fun b =>
    (h.component.map_conj b).subgroupOf (conjugate_le_orbit L B b)
  have hgen : iSup C = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    change (⨆ b, (C b).map E.subtype) = componentOrbit L B
    unfold componentOrbit
    congr 1
    funext b
    exact map_subgroupOf_eq_of_le (conjugate_le_orbit L B b)
  let : Group.IsPerfect E := h.component.orbit_isPerfect B
  let : Group.IsPerfect (Factor M.n) := model_perfect M
  let : IsSimpleGroup (Factor M.n) := model_simple M
  exact exists_first_factor C hC hgen M.projection M.projection_surjective

/-- Align the canonical embedding with a surviving conjugate inside the
actual generated overgroup. -/
theorem exists_embedding_component_marking (h : Hypotheses ρ L B a)
    (M : TwoFactorModel (componentOrbit L B))
    (τ : Representation (ZMod 2) (L ⊔ B : Subgroup G) U) [τ.IsIrreducible]
    (hn : ¬ Representation.IsTrivial (τ.comp (orbitInclusion L B))) :
    ∃ b : B.subgroupOf (L ⊔ B),
      ((embedding (orbitInclusion L B) τ M (orbit_twoCore_le_ker L B τ)).comp
        (MonoidHom.inl (Factor M.n) (Factor M.n))).range =
        ((L.subgroupOf (L ⊔ B)).map
          (MulAut.conj (b : (L ⊔ B : Subgroup G))).toMonoidHom).map
            (QuotientGroup.mk' τ.ker) ∧
      ((L.subgroupOf (L ⊔ B)).map
        (MulAut.conj (b : (L ⊔ B : Subgroup G))).toMonoidHom).map
          (QuotientGroup.mk' τ.ker) ≠ ⊥ := by
  obtain ⟨b, hb⟩ := exists_model_component_marking h M
  let E := componentOrbit L B
  let X := L ⊔ B
  let i := orbitInclusion L B
  let q := QuotientGroup.mk' τ.ker
  let j := embedding i τ M (orbit_twoCore_le_ker L B τ)
  let C := (L.map (MulAut.conj (b : G)).toMonoidHom).subgroupOf E
  let bX : B.subgroupOf X := ⟨⟨b, (le_sup_right : B ≤ X) b.property⟩, b.property⟩
  have hC : C.map i = (L.subgroupOf X).map (MulAut.conj (bX : X)).toMonoidHom := by
    apply Subgroup.map_injective X.subtype_injective
    rw [map_map, show X.subtype.comp i = E.subtype from rfl,
      map_subgroupOf_eq_of_le (conjugate_le_orbit L B b), map_map]
    have he : X.subtype.comp (MulAut.conj (bX : X)).toMonoidHom =
        (MulAut.conj (b : G)).toMonoidHom.comp X.subtype := by
      ext x
      rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le le_sup_left]
  have hj : j.comp M.projection = q.comp i := by
    ext x
    exact embedding_projection i τ M (orbit_twoCore_le_ker L B τ) x
  have hfirst : (j.comp (MonoidHom.inl (Factor M.n) (Factor M.n))).range =
      ((L.subgroupOf X).map (MulAut.conj (bX : X)).toMonoidHom).map q := by
    rw [MonoidHom.range_comp, ← hb, map_map, hj, ← map_map, hC]
  refine ⟨bX, hfirst, ?_⟩
  rw [← hfirst, MonoidHom.range_comp]
  apply (map_eq_bot_iff_of_injective _
    (embedding_injective i τ M (orbit_twoCore_le_ker L B τ)
      (orbit_ker_eq_twoCore h M τ hn))).not.mpr
  let : IsSimpleGroup (Factor M.n) := model_simple M
  intro hz
  obtain ⟨x, hx⟩ := exists_ne (1 : Factor M.n)
  have hh := mem_bot.mp (hz ▸ (show MonoidHom.inl (Factor M.n) (Factor M.n) x ∈
      (MonoidHom.inl (Factor M.n) (Factor M.n)).range from ⟨x, rfl⟩))
  exact hx (congrArg Prod.fst hh)

end Representation.QuadraticFourGroup.SectionReduction

end
