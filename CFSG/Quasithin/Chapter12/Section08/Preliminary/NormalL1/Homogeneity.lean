module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Actions
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Coordinates
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.PointMarking
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.SeedRigidity

/-!
# The normal-L₁ homogeneous-module construction

For 3≤n≤5, the ambient natural action induces a marking of the literal
point quotient V/V₁. The seed is simple, and the ambient Sylow subgroup
forces all its conjugation twists to be equivalent. Its orbit generates
the local span, giving an actual finite direct sum of natural seeds.
The action kernel is exactly O₂(L₁); the homogeneous coordinates intertwine
both literal conjugation and the descended L₁/O₂(L₁)-action. The marked
actor remains GL₂(2)′ at n=3.

The J=G₁ application constructs the natural coordinates and their full
linear-group equivariance for n>3, and applies the nonabelian dimension
obstruction. These implications discharge the marking and seed-rigidity
obligations of 12.8.5(1). The higher-rank 12.8.1 setup supplies the ambient
natural marking, and 12.8.4 supplies the elementary quotient; the form and
its radical in the dimension application are the earlier 12.8.8(2) inputs.
Their source discharge stays with the Section08 preliminary assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.5(1), printed p.850 (PDF p.867), and its application in the
proof of Lemma 12.8.8(5), printed p.852 (PDF p.869).
-/

public section

open Subgroup
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
  [IsElementaryAbelian 2 (F.tilde V)]

/-- The natural homogeneous decomposition of source 12.8.5(1), from the
ambient natural marking and the elementary quotient of 12.8.4. The seed
marking, exact action kernel, and equivariant coordinates are all constructed.
The last equation descends those coordinates to the literal quotient actor. -/
theorem homogeneous_natural_decomposition_of_ambient (hn : 3 ≤ n) (hn₁ : n ≤ 5)
    (L : Subgroup G) (hLV : L ≤ normalizer (V : Set G))
    (A : AmbientNaturalMarking L hLV n) {M J : Subgroup G} (hJ : J ∈ F.Hz L M)
    [((F.Li L 1).subgroupOf J).Normal]
    [IsElementaryAbelian 2 (F.tilde (F.UH J))] :
    ∃ D : F.NaturalSeedMarking L hLV,
    ∃ r : ℕ, ∃ e : Additive (F.tilde (F.UH J)) ≃ₗ[ZMod 2] (Fin r → Additive (F.tilde V)),
      ((F.localTildeAction J hJ.2.1).comp
        (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
      (∀ (k : F.Li L 1) u i,
        e (Additive.ofMul (F.localTildeAction J hJ.2.1
          (inclusion (F.Li_one_le_of_mem_Hz hJ) k) u.toMul)) i =
          Additive.ofMul (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
            ((F.Li_le L 1).trans (inf_le_left.trans hLV)) k (e u i).toMul)) ∧
      (∀ (q : F.Li L 1 ⧸ pCore 2 (F.Li L 1)) u i,
        D.coordinates (e (Additive.ofMul (D.quotientSpanAction J hJ.2.1
          (F.Li_one_le_of_mem_Hz hJ) (F.normalizes_Li_one_of_relative_normal hJ)
            q u.toMul)) i) =
          (D.quotientEquiv q).val (D.coordinates (e u i))) := by
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient hn L hLV A
  obtain ⟨r, e, he⟩ := homogeneous_coordinates_of_natural_seed hn hn₁ D hJ
  refine ⟨D, r, e, D.localAction_ker J hJ.2.1 (F.Li_one_le_of_mem_Hz hJ)
    (F.normalizes_Li_one_of_relative_normal hJ), he, ?_⟩
  intro q u i
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  exact (congrArg D.coordinates (he k u i)).trans (D.equivariant k (e u i))

/-- Literal local-action coordinates for the direct sum of natural seeds.
No seed marking, simplicity, or conjugation-twist equivalence is assumed. -/
theorem homogeneous_coordinates_of_ambient_natural (hn : 3 ≤ n) (hn₁ : n ≤ 5)
    (L : Subgroup G) (hLV : L ≤ normalizer (V : Set G))
    (A : AmbientNaturalMarking L hLV n) {M J : Subgroup G} (hJ : J ∈ F.Hz L M)
    [((F.Li L 1).subgroupOf J).Normal]
    [IsElementaryAbelian 2 (F.tilde (F.UH J))] :
    ∃ r : ℕ, ∃ e : Additive (F.tilde (F.UH J)) ≃ₗ[ZMod 2] (Fin r → Additive (F.tilde V)),
      ∀ (k : F.Li L 1) u i,
        e (Additive.ofMul (F.localTildeAction J hJ.2.1
          (inclusion (F.Li_one_le_of_mem_Hz hJ) k) u.toMul)) i =
          Additive.ofMul (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
            ((F.Li_le L 1).trans (inf_le_left.trans hLV)) k (e u i).toMul) := by
  obtain ⟨_, r, e, _, he, _⟩ := F.homogeneous_natural_decomposition_of_ambient hn hn₁ L hLV A hJ
  exact ⟨r, e, he⟩

/-- For the actual J=G₁ consumer and n>3, construct both natural coordinate
maps and all action equations required by the dimension obstruction.
Perfectness makes the marked derived actor surjective onto GL only here. -/
theorem full_linear_coordinates_of_ambient_natural (hn : 3 < n) (hn₁ : n ≤ 5)
    (L : Subgroup G) (hLV : L ≤ normalizer (V : Set G))
    (A : AmbientNaturalMarking L hLV n)
    [((F.Li L 1).subgroupOf F.H).Normal] [IsElementaryAbelian 2 (F.tilde F.U)] :
    ∃ D : F.NaturalSeedMarking L hLV,
    ∃ r : ℕ, ∃ eU : Additive (F.tilde F.U) ≃ₗ[ZMod 2] (Fin r → Fin (n - 1) → ZMod 2),
      Function.Surjective D.naturalActor ∧
      (∀ (k : F.Li L 1) v, D.coordinates (Additive.ofMul
        (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
          ((F.Li_le L 1).trans (inf_le_left.trans hLV)) k v.toMul)) =
            D.naturalActor k (D.coordinates v)) ∧
      (∀ (k : F.Li L 1) u i, eU (Additive.ofMul (F.localTildeAction F.H le_rfl
        ⟨k, (F.Li_le L 1 k.property).2⟩ u.toMul)) i = D.naturalActor k (eU u i)) := by
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient hn.le L hLV A
  have hHK : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (K := F.H)
      ((F.Li_le L 1).trans inf_le_right)).mp inferInstance
  let : IsElementaryAbelian 2 (F.tilde (F.UH F.H)) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.tilde F.U))
  obtain ⟨r, e, he⟩ := F.homogeneous_coordinates_of_seed_intertwiners L F.H hLV le_rfl
    ((F.Li_le L 1).trans inf_le_right) hHK (D.seed_simple hn.le)
    (D.seed_intertwiners hn.le hn₁ F.H le_rfl (F.invariant 1) hHK)
  let eU : Additive (F.tilde F.U) ≃ₗ[ZMod 2] (Fin r → Fin (n - 1) → ZMod 2) :=
    e.trans (LinearEquiv.piCongrRight (fun _ => D.coordinates))
  refine ⟨D, r, eU, D.naturalActor_surjective hn, D.equivariant, ?_⟩
  intro k u i
  exact (congrArg D.coordinates (he k u i)).trans (D.equivariant k (e u i))

/-- The actual nonabelian J=G₁ dimension consumer, with its homogeneous
coordinates and seed marking discharged from the ambient natural action.
The invariant form and its radical are the explicit earlier 12.8.8(2) inputs. -/
theorem nonabelian_exclusion_of_ambient_natural (hn : 3 < n) (hn₁ : n ≤ 5)
    (L : Subgroup G) (hLV : L ≤ normalizer (V : Set G))
    (A : AmbientNaturalMarking L hLV n)
    [((F.Li L 1).subgroupOf F.H).Normal] [IsElementaryAbelian 2 (F.tilde F.U)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (F.tilde F.U)))
    (hB : ∀ (j : F.Li L 1) u v,
      B (Additive.ofMul (F.localTildeAction F.H le_rfl
        ⟨j, (F.Li_le L 1 j.property).2⟩ u.toMul))
        (Additive.ofMul (F.localTildeAction F.H le_rfl
          ⟨j, (F.Li_le L 1 j.property).2⟩ v.toMul)) = B u v)
    (hrad : ∀ v : Additive (F.tilde F.U),
      (∀ u, B u v = 0) ↔ (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU)
    (hnonab : ¬ IsMulCommutative F.U) : False := by
  obtain ⟨D, r, eU, hα, heV, heU⟩ :=
    F.full_linear_coordinates_of_ambient_natural hn hn₁ L hLV A
  exact F.nonabelian_homogeneous_natural_exclusion L hLV hn r D.naturalActor hα
    D.coordinates eU heV heU B hB hrad hnonab

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
