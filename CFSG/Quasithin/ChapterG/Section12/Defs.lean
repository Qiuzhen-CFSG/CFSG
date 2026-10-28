module

public import Theory.LinearAlgebra.BinaryHyperplaneTransvections
public import Theory.ElementaryAbelian.Basic

/-!
# Source inputs for subgroups containing hyperplane transvections

The groups act as actual binary linear automorphisms. `pointRadical` is the
kernel of the action of the vector stabilizer on the perpendicular space
modulo the center line. Its displacement formulation retains the literal
quotient, including elements which are trivial on the hyperplane itself.
`GoodVector` is condition (*) on printed p.370, not a recognition premise.

`ModuleHypotheses` records G.12.12's faithful action, relative normality,
irreducibility, self-duality, and full hyperplane transvection action.
Self-duality uses an invariant perfect pairing without a symmetry assumption;
constructing an invariant alternating form remains a theorem to prove.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), §G.12,
printed pp.370--375, especially G.12.1 and G.12.12.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Automorphisms preserving the specified bilinear form. For a nondegenerate
alternating form this is the full symplectic group on the actual space. -/
def formStabilizer (B : LinearMap.BilinForm (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using
      (hg (g.symm x) (g.symm y)).symm

/-- The automorphisms fixing `v`, preserving `W`, and inducing the identity
on `W/⟨v⟩` when `v ∈ W`. -/
def flagKernel (W : Submodule (ZMod 2) V) (v : V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g v = v ∧ (∀ w, g w ∈ W ↔ w ∈ W) ∧
    ∀ w ∈ W, g w - w ∈ Submodule.span (ZMod 2) {v}}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hgv, hgW, hgd⟩ ⟨hhv, hhW, hhd⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearEquiv.mul_apply, hhv, hgv]
    · intro w
      exact (hgW (h w)).trans (hhW w)
    · intro w hw
      have he := (Submodule.span (ZMod 2) {v}).add_mem
        (hgd (h w) ((hhW w).mpr hw)) (hhd w hw)
      simpa only [sub_add_sub_cancel, LinearEquiv.mul_apply] using he
  inv_mem' := by
    rintro g ⟨hgv, hgW, hgd⟩
    refine ⟨?_, ?_, ?_⟩
    · apply g.injective
      simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using hgv.symm
    · intro w
      simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
        (hgW (g.symm w)).symm
    · intro w hw
      have hm : g.symm w ∈ W := by
        apply (hgW (g.symm w)).mp
        simpa only [LinearEquiv.apply_symm_apply] using hw
      have he := (Submodule.span (ZMod 2) {v}).neg_mem (hgd (g.symm w) hm)
      simpa only [LinearEquiv.apply_symm_apply, neg_sub, LinearEquiv.coe_inv] using he

/-- The source group `C_G(v) ∩ C_G(v⊥/⟨v⟩)`. -/
def pointRadical (G : Subgroup (V ≃ₗ[ZMod 2] V))
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) :
    Subgroup (V ≃ₗ[ZMod 2] V) := G ⊓ flagKernel (B v).ker v

/-- In a form-preserving group, preservation of the perpendicular hyperplane
follows from fixing its center. -/
theorem mem_pointRadical_iff
    {G : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    (hG : G ≤ formStabilizer B) {g : V ≃ₗ[ZMod 2] V} {v : V} :
    g ∈ pointRadical G B v ↔ g ∈ G ∧ g v = v ∧
      ∀ w, B v w = 0 → g w - w ∈ Submodule.span (ZMod 2) {v} := by
  constructor
  · exact fun hg => ⟨hg.1, hg.2.1, hg.2.2.2⟩
  · rintro ⟨hg, hgv, hmove⟩
    refine ⟨hg, hgv, ?_, hmove⟩
    intro w
    change B v (g w) = 0 ↔ B v w = 0
    have he := hG hg v w
    rw [hgv] at he
    rw [he]

/-- The set `𝒱(G)` in G.12.1: the actual point radical induces every
transvection on the perpendicular hyperplane with this center. -/
def GoodVector (G : Subgroup (V ≃ₗ[ZMod 2] V))
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (v : V) : Prop :=
  BinaryTransvection.FullCenterAction (pointRadical G B v).subtype
    (B v).ker ⟨v, hB v⟩

/-- The complete inputs of G.12.1, before any classification alternative. -/
structure ClassificationHypotheses (G : Subgroup (V ≃ₗ[ZMod 2] V))
    [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (u v : V) : Prop where
  alternating : B.IsAlt
  nondegenerate : B.Nondegenerate
  preserves : G ≤ formStabilizer B
  dimension : 4 ≤ Module.finrank (ZMod 2) V
  good_u : GoodVector G B alternating u
  good_v : GoodVector G B alternating v
  pairing : B u v ≠ 0

/-- Irreducibility for the given subgroup's literal action on the space. -/
def Irreducible (K : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ W : Submodule (ZMod 2) V,
    (∀ k ∈ K, ∀ w ∈ W, k w ∈ W) → W = ⊥ ∨ W = ⊤

/-- An actual equivariant linear isomorphism with the contragredient module.
The equivalent pairing equation does not assume symmetry or alternation. -/
def SelfDual (K : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ e : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V,
    ∀ k ∈ K, ∀ x y, e (k x) (k y) = e x y

/-- The genuine source hypotheses of G.12.12, after identifying the faithful
ambient group with its image in the binary linear group. -/
structure ModuleHypotheses (H K Q : Subgroup (V ≃ₗ[ZMod 2] V))
    [FiniteDimensional (ZMod 2) V] (W : Submodule (ZMod 2) V) (v : W) : Prop where
  K_le : K ≤ H
  K_normal : (K.subgroupOf H).Normal
  Q_le : Q ≤ H
  elementary : IsElementaryAbelian 2 Q
  irreducible : Irreducible K
  selfDual : SelfDual K
  dimension : 2 < Module.finrank (ZMod 2) V
  hyperplane : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V
  transvections : BinaryTransvection.FullCenterAction Q.subtype W v

end CFSG.Quasithin.ChapterG.Section12
