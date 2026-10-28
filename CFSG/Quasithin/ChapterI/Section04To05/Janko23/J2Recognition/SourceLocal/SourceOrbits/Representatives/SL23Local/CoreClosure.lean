module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalActionFusion

/-!
# The Q-conjugate closure in the final local construction of 47.5

For the actual extraspecial core Q of H = C_G(z), define L = ⟨X^Q⟩ as
an ambient subgroup. It contains X, lies in H, and is normalized by
N_H(X). The relative normalizer is identified using the literal subgroup
and inclusion maps, without asserting ambient normality of X.

`CoreModel` and `CubicGeometry` are intermediate construction contracts.
Neither is asserted to be inhabited here. The former requires an actual
matrix-group equivalence for L and membership of the distinguished z;
the latter records intrinsic cubic-subgroup geometry. The parent module
uses them to prove the ambient pair stabilizer and construct an actual
Sylow subgroup. They must still be derived from the local core and the
literal SL₂(3) model before completing the source implication.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263.
The underlying core and its characteristic-center normalizer are the
proved `LocalStructure` and `LocalActionFusion` interfaces.
-/

@[expose] public section

open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
variable {G : Type*} [Group G] [Finite G]
def coreClosure (D : Seed G) : Subgroup G :=
  ⨆ q : ambientCore D.z, D.X.map (MulAut.conj (q : G)).toMonoidHom

def localNormalizer (D : Seed G) : Subgroup G :=
  involutionCentralizer D.z ⊓ normalizer (D.X : Set G)

theorem X_le_coreClosure (D : Seed G) : D.X ≤ coreClosure D := by
  have h := le_iSup (fun q : ambientCore D.z =>
    D.X.map (MulAut.conj (q : G)).toMonoidHom) (1 : ambientCore D.z)
  intro x hx
  exact h (mem_map.mpr ⟨x, hx, by simp⟩)

theorem coreClosure_le (D : Seed G) : coreClosure D ≤ involutionCentralizer D.z := by
  apply iSup_le
  intro q
  rintro _ ⟨x, hx, rfl⟩
  exact (involutionCentralizer D.z).mul_mem
    ((involutionCentralizer D.z).mul_mem (ambientCore_le D.z q.property) (D.X_le hx))
    ((involutionCentralizer D.z).inv_mem (ambientCore_le D.z q.property))

/-- The ambient image of the relative normalizer inside H, with its literal maps. -/
theorem localNormalizer_eq_map (D : Seed G) :
    localNormalizer D =
      (normalizer (D.X.subgroupOf (involutionCentralizer D.z) :
        Set (involutionCentralizer D.z))).map (involutionCentralizer D.z).subtype := by
  rw [← subgroupOf_normalizer_eq D.X_le, subgroupOf_map_subtype]
  exact inf_comm _ _

theorem X_le_localNormalizer (D : Seed G) : D.X ≤ localNormalizer D :=
  le_inf D.X_le D.X.le_normalizer

theorem localNormalizer_le_normalizer_coreClosure (D : Seed G) :
    localNormalizer D ≤ normalizer (coreClosure D : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg
  have hgQ : g ∈ normalizer (ambientCore D.z : Set G) :=
    D.localType.normalizer_core.symm ▸ hg.1
  have hmap : (coreClosure D).map (MulAut.conj g).toMonoidHom ≤ coreClosure D := by
    rw [coreClosure, Subgroup.map_iSup]
    apply iSup_le
    intro q
    rw [map_map]
    have hqQ : g * (q : G) * g⁻¹ ∈ ambientCore D.z :=
      (mem_normalizer_iff.mp hgQ _).mp q.property
    let q' : ambientCore D.z := ⟨g * (q : G) * g⁻¹, hqQ⟩
    apply le_trans ?_ (le_iSup (fun r : ambientCore D.z =>
      D.X.map (MulAut.conj (r : G)).toMonoidHom) q')
    rintro _ ⟨x, hx, rfl⟩
    refine mem_map.mpr ⟨g * x * g⁻¹, (mem_normalizer_iff.mp hg.2 x).mp hx, ?_⟩
    change (g * (q : G) * g⁻¹) * (g * x * g⁻¹) *
      (g * (q : G) * g⁻¹)⁻¹ = g * ((q : G) * x * (q : G)⁻¹) * g⁻¹
    group
  intro x hx
  exact hmap (mem_map_of_mem _ hx)

/-- The two outstanding facts about the actual Q-conjugate closure. -/
structure CoreModel (D : Seed G) where
  equiv : coreClosure D ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)
  involution_mem : D.z ∈ coreClosure D

/-- All cubic subgroups of L other than X, in the original ambient group. -/
abbrev OtherCubics (L X : Subgroup G) :=
  {Y : Subgroup G // Y ≤ L ∧ Nat.card Y = 3 ∧ Y ≠ X}

/-- Intrinsic SL₂(3) geometry, still to be proved from the literal matrix model. -/
structure CubicGeometry (L X : Subgroup G) : Prop where
  card : Nat.card (OtherCubics L X) = 3
  generate : ∀ Y : OtherCubics L X, X ⊔ Y.val = L
  transitive : ∀ Y W : OtherCubics L X,
    ∃ x : X, Y.val.map (MulAut.conj (x : G)).toMonoidHom = W.val

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
