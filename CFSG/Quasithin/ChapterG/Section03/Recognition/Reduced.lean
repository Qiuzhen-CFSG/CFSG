module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.RootGeometry
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Faithful quotient reduction for binary root orbits

A root-generated spanning orbit has a useful invariant-subspace property:
every proper invariant subspace is fixed pointwise. Thus its quotient by the
common fixed space is irreducible. The kernel of this actual quotient action
is elementary abelian and normal, so a trivial intrinsic two-core makes the
quotient action faithful. Faithful equivariant quotients preserve generation,
the spanning orbit, and the lower bound of four on the size of every root group.

These are reductions for the separately stated trivial-two-core specialization
of Aschbacher--Smith G.3.1, printed pp.337--338. They do not assert recognition
or complete reducibility. Recognition of the irreducible quotient and lifting
its full action are separate proof obligations. In particular, no two-core
hypothesis is passed to an arbitrary subgroup or restriction here.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A spanning orbit of nonzero centers with at least four roots at each center,
which generates the actual acting group. No recognition is included. -/
structure RootGeneratedOrbit (G : Subgroup (GL V)) (Δ : Set V) : Prop where
  nonzero : ∀ x ∈ Δ, x ≠ 0
  orbit : ∃ x : V, Δ = MulAction.orbit G x
  span_eq_top : Submodule.span (ZMod 2) Δ = ⊤
  generated_eq : generated G Δ = G
  large_roots : ∀ x ∈ Δ, 2 < Nat.card (rootGroup G x)

/-- Irreducibility stated directly for the actual linear action. -/
def Irreducible (G : Subgroup (GL V)) : Prop :=
  ∀ U : Submodule (ZMod 2) V, G ≤ parabolic U → U = ⊥ ∨ U = ⊤

variable {G : Subgroup (GL V)} {Δ : Set V}

theorem RootGeneratedOrbit.nonempty (r : RootGeneratedOrbit G Δ) : Δ.Nonempty := by
  obtain ⟨x, rfl⟩ := r.orbit
  exact ⟨x, MulAction.mem_orbit_self x⟩

theorem RootGeneratedOrbit.ne_bot (r : RootGeneratedOrbit G Δ) : G ≠ ⊥ := by
  intro he
  obtain ⟨x, hx⟩ := r.nonempty
  have hb : rootGroup G x = ⊥ := bot_unique ((rootGroup_le G x).trans_eq he)
  have hc := r.large_roots x hx
  rw [hb, Subgroup.card_bot] at hc
  omega

theorem RootGeneratedOrbit.finiteDimensional [Finite G]
    (r : RootGeneratedOrbit G Δ) : FiniteDimensional (ZMod 2) V := by
  obtain ⟨x, hx⟩ := r.orbit
  have hfin : Δ.Finite := hx ▸ Finite.finite_mulAction_orbit x
  have h := Module.Finite.span_of_finite (ZMod 2) hfin
  rw [r.span_eq_top] at h
  exact Module.Finite.of_surjective (⊤ : Submodule (ZMod 2) V).subtype
    (by intro v; exact ⟨⟨v, trivial⟩, rfl⟩)

/-- A proper invariant subspace contains no center from a spanning orbit. -/
theorem RootGeneratedOrbit.center_not_mem (r : RootGeneratedOrbit G Δ)
    (U : Submodule (ZMod 2) V) (hU : G ≤ parabolic U) (hUt : U ≠ ⊤)
    {x : V} (hx : x ∈ Δ) : x ∉ U := by
  intro hxU
  apply hUt
  apply top_unique
  rw [← r.span_eq_top]
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨z, hz⟩ := r.orbit
  have hyx : y ∈ MulAction.orbit G x := by
    rw [hz] at hx hy
    rw [MulAction.orbit_eq_iff.mpr hx]
    exact hy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hyx
  exact (hU g.property x).mpr hxU

/-- Every proper invariant subspace is fixed pointwise. -/
theorem RootGeneratedOrbit.le_fixedSpace (r : RootGeneratedOrbit G Δ)
    (U : Submodule (ZMod 2) V) (hU : G ≤ parabolic U) (hUt : U ≠ ⊤) :
    U ≤ fixedSpace G := by
  have hgen : generated G Δ ≤ pointwiseFixer U := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx a ha v hv
    by_contra hav
    have hax : a v = v + x := root_move_eq_add ha hav
    have hdiff : a v - v ∈ U := U.sub_mem ((hU ha.1 v).mpr hv) hv
    rw [hax, add_sub_cancel_left] at hdiff
    exact r.center_not_mem U hU hUt hx hdiff
  rw [r.generated_eq] at hgen
  intro v hv g hg
  exact hgen hg v hv

/-- Restriction of an actual automorphism to the quotient by an invariant subspace. -/
def quotientAction (G : Subgroup (GL V)) (U : Submodule (ZMod 2) V)
    (hU : G ≤ parabolic U) : G →* GL (V ⧸ U) where
  toFun g := Submodule.Quotient.equiv U U g.val (by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hU g.property v).mpr hv
    · intro v hv
      refine ⟨g.val⁻¹ v, (hU (G.inv_mem g.property) v).mpr hv, ?_⟩
      exact g.val.apply_symm_apply v)
  map_one' := by
    ext v
    obtain ⟨w, rfl⟩ := U.mkQ_surjective v
    rfl
  map_mul' := by
    intro g h
    ext v
    obtain ⟨w, rfl⟩ := U.mkQ_surjective v
    rfl

@[simp] theorem quotientAction_apply_mkQ (U : Submodule (ZMod 2) V)
    (hU : G ≤ parabolic U) (g : G) (v : V) :
    quotientAction G U hU g (U.mkQ v) = U.mkQ (g.val v) := rfl

theorem mem_quotientAction_ker (U : Submodule (ZMod 2) V)
    (hU : G ≤ parabolic U) (g : G) :
    g ∈ (quotientAction G U hU).ker ↔ ∀ v : V, g.val v - v ∈ U := by
  constructor
  · intro hg v
    have he := congrArg (fun e : GL (V ⧸ U) => e (U.mkQ v)) hg
    change U.mkQ (g.val v) = U.mkQ v at he
    exact (Submodule.Quotient.mk_eq_zero U).mp (by
      change U.mkQ (g.val v - v) = 0
      rw [map_sub, he, sub_self])
  · intro hg
    ext v
    obtain ⟨w, rfl⟩ := U.mkQ_surjective v
    change U.mkQ (g.val w) = U.mkQ w
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero U).mpr (hg w)

/-- The kernel on a quotient by a fixed subspace lies in the intrinsic two-core. -/
theorem quotientAction_ker_le_twoCore (U : Submodule (ZMod 2) V)
    (hU : G ≤ parabolic U) (hfix : U ≤ fixedSpace G) :
    (quotientAction G U hU).ker ≤ pCore 2 G := by
  let K := (quotientAction G U hU).ker
  let : IsElementaryAbelian 2 K := elementaryAbelian_of_le_radical
    (G.subtype.comp K.subtype) (Subtype.val_injective.comp Subtype.val_injective)
    U (fun g => ⟨fun v hv => hfix hv g.val.val g.val.property,
      (mem_quotientAction_ker U hU g.val).mp g.property⟩)
  exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 K⟩

theorem quotientAction_injective (U : Submodule (ZMod 2) V)
    (hU : G ≤ parabolic U) (hfix : U ≤ fixedSpace G) (hcore : pCore 2 G = ⊥) :
    Function.Injective (quotientAction G U hU) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique ((quotientAction_ker_le_twoCore U hU hfix).trans_eq hcore)

def fixedQuotientAction (G : Subgroup (GL V)) : G →* GL (V ⧸ fixedSpace G) :=
  quotientAction G (fixedSpace G)
    (G.le_normalizer.trans (normalizer_le_parabolic_fixedSpace G))

@[simp] theorem fixedQuotientAction_apply_mkQ (g : G) (v : V) :
    fixedQuotientAction G g ((fixedSpace G).mkQ v) =
      (fixedSpace G).mkQ (g.val v) := rfl

theorem fixedQuotientAction_injective (hcore : pCore 2 G = ⊥) :
    Function.Injective (fixedQuotientAction G) :=
  quotientAction_injective _ _ le_rfl hcore

/-- The quotient by all fixed vectors is irreducible for a spanning root orbit. -/
theorem RootGeneratedOrbit.fixedQuotient_irreducible (r : RootGeneratedOrbit G Δ) :
    Irreducible (fixedQuotientAction G).range := by
  intro U hU
  let C := fixedSpace G
  let W := U.comap C.mkQ
  have hW : G ≤ parabolic W := by
    intro g hg v
    exact hU (show fixedQuotientAction G ⟨g, hg⟩ ∈ (fixedQuotientAction G).range from
      ⟨⟨g, hg⟩, rfl⟩) (C.mkQ v)
  by_cases hWt : W = ⊤
  · right
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := C.mkQ_surjective v
    exact show w ∈ W from hWt ▸ Submodule.mem_top
  · left
    apply bot_unique
    intro v hv
    obtain ⟨w, rfl⟩ := C.mkQ_surjective v
    have hw : w ∈ W := hv
    exact (Submodule.Quotient.mk_eq_zero C).mpr (r.le_fixedSpace W hW hWt hw)



variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Equivariant linear images take actual roots to actual roots. -/
theorem root_mem_of_equivariant (f : V →ₗ[ZMod 2] W)
    (hf : Function.Surjective f) (ρ : G →* GL W)
    (heq : ∀ (g : G) (v : V), ρ g (f v) = f (g.val v))
    {x : V} {a : GL V} (ha : a ∈ rootGroup G x) :
    ρ ⟨a, ha.1⟩ ∈ rootGroup ρ.range (f x) := by
  refine ⟨⟨⟨a, ha.1⟩, rfl⟩, ?_, ?_⟩
  · intro w hw
    rcases (mem_centerLine_iff (f x) w).mp hw with rfl | rfl
    · exact (ρ ⟨a, ha.1⟩).map_zero
    · rw [heq, ha.2.1 x (Submodule.mem_span_singleton_self x)]
  · intro w
    obtain ⟨v, rfl⟩ := hf w
    rw [heq, ← map_sub]
    rcases (mem_centerLine_iff x (a v - v)).mp (ha.2.2 v) with hz | hx
    · rw [hz, map_zero]
      exact Submodule.zero_mem _
    · rw [hx]
      exact Submodule.mem_span_singleton_self _

/-- Faithful equivariant quotients preserve a root-generated spanning orbit. -/
theorem RootGeneratedOrbit.map [Finite G] (r : RootGeneratedOrbit G Δ)
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f) (ρ : G →* GL W)
    (hρ : Function.Injective ρ)
    (heq : ∀ (g : G) (v : V), ρ g (f v) = f (g.val v))
    (hnz : ∀ x ∈ Δ, f x ≠ 0) : RootGeneratedOrbit ρ.range (f '' Δ) := by
  let : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hnz x hx
  · obtain ⟨x, rfl⟩ := r.orbit
    refine ⟨f x, ?_⟩
    ext w
    constructor
    · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
      exact MulAction.mem_orbit_iff.mpr ⟨⟨ρ g, g, rfl⟩, heq g x⟩
    · intro hw
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hw
      obtain ⟨a, ha⟩ := g.property
      refine ⟨a.val x, MulAction.mem_orbit_iff.mpr ⟨a, rfl⟩, ?_⟩
      exact (heq a x).symm.trans (ha ▸ hg)
  · rw [← Submodule.map_span, r.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hf]
  · apply le_antisymm (generated_le _ _)
    let K := generated ρ.range (f '' Δ)
    have hle : generated G Δ ≤ (K.comap ρ).map G.subtype := by
      apply iSup_le
      intro x
      apply iSup_le
      intro hx a ha
      exact ⟨⟨a, ha.1⟩,
        rootGroup_le_generated ρ.range (Δ := f '' Δ) (x := f x) ⟨x, hx, rfl⟩
          (root_mem_of_equivariant f hf ρ heq ha), rfl⟩
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, ha, hag⟩ := hle (show g.val ∈ generated G Δ by rw [r.generated_eq]; exact g.property)
    have he : a = g := Subtype.ext hag
    exact he ▸ ha
  · rintro _ ⟨x, hx, rfl⟩
    let j : rootGroup G x → rootGroup ρ.range (f x) := fun a =>
      ⟨ρ ⟨a.val, a.property.1⟩, root_mem_of_equivariant f hf ρ heq a.property⟩
    have hj : Function.Injective j := by
      intro a b hab
      have he := hρ (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg (fun z : G => z.val) he)
    exact (r.large_roots x hx).trans_le (Nat.card_le_card_of_injective j hj)

/-- Passing to the quotient by all fixed vectors preserves the genuine root
inputs when the original acting group has trivial two-core. -/
theorem RootGeneratedOrbit.fixedQuotient [Finite G] (r : RootGeneratedOrbit G Δ)
    (hcore : pCore 2 G = ⊥) :
    RootGeneratedOrbit (fixedQuotientAction G).range ((fixedSpace G).mkQ '' Δ) := by
  apply r.map (fixedSpace G).mkQ (fixedSpace G).mkQ_surjective
    (fixedQuotientAction G) (fixedQuotientAction_injective hcore)
    (fun _ _ => rfl)
  intro x hx hz
  apply r.center_not_mem (fixedSpace G)
    (G.le_normalizer.trans (normalizer_le_parabolic_fixedSpace G))
    (fixedSpace_ne_top r.ne_bot) hx
  exact (Submodule.Quotient.mk_eq_zero _).mp hz


end CFSG.Quasithin.ChapterG.Section03.Reduced
