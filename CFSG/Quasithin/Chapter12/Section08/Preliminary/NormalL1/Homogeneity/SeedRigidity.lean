module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Coordinates
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.SeedRigidity.BinaryTwo
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms


/-!
# Sylow-compatible rigidity of the natural seed in dimensions two through four

For n=4,5 the marked L₁/O₂(L₁) is the full binary linear group in dimension
n−1. Its natural action is simple by transitivity on nonzero vectors.
Conjugation by J descends through the characteristic two-core and the marking.
Inner/graph coverage makes the resulting outer image a two-group. The ambient
Sylow subgroup lies in J and preserves V, so its action has linear implementers
and is inner on the marked quotient. The Sylow index forces the outer image
to vanish. Transporting the inner implementers back gives the literal left
conjugation intertwiners required by the homogeneous-coordinate theorem.

For n=3 the actual actor is GL₂(2)′. The separate binary-plane calculation
proves its natural action simple and implements every automorphism, including
inversion. Combining the two arguments gives the seed premises for 3≤n≤5.
The final applications discharge both seed premises in the local decomposition
and in the actual J=G₁ nonabelian dimension obstruction. The supplied natural
marking and earlier elementary-quotient and form inputs remain explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 12.8.5(1),
printed p.850 (PDF p.867), and Lemma 12.8.8(5), printed p.852 (PDF p.869).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n)

/-- Every source local overgroup contains the actual L₁. -/
theorem Li_one_le_of_mem_Hz {L M J : Subgroup G} (hJ : J ∈ F.Hz L M) : F.Li L 1 ≤ J :=
  fun _ hk => hJ.1.2 (Or.inl hk)

/-- The source local family contains the ambient Sylow subgroup. -/
theorem sylow_le_of_mem_Hz {L M J : Subgroup G} (hJ : J ∈ F.Hz L M) : (T : Subgroup G) ≤ J :=
  fun _ ht => hJ.1.2 (Or.inr ht)

/-- Genuine relative normality gives ambient normalization of L₁. -/
theorem normalizes_Li_one_of_relative_normal {L M J : Subgroup G} (hJ : J ∈ F.Hz L M)
    [((F.Li L 1).subgroupOf J).Normal] : J ≤ normalizer (F.Li L 1 : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (F.Li_one_le_of_mem_Hz hJ)).mp inferInstance

variable {F} {L : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}
variable [IsElementaryAbelian 2 (F.tilde V)]

/-- An element preserving V implements its conjugation on the literal seed. -/
theorem seed_intertwiner_of_normalizes {J : Subgroup G} (hJH : J ≤ F.H)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) (j : J)
    (hjV : (j : G) ∈ normalizer (V : Set G)) :
    ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  let S := F.H ⊓ normalizer (V : Set G)
  let a : S := ⟨j, hJH j.property, hjV⟩
  let ρ := Representation.elementaryRepresentation (p := 2)
    (F.tildeAction S V inf_le_left inf_le_right)
  refine ⟨LinearEquiv.ofBijective (ρ a) (Representation.apply_bijective ρ a), ?_⟩
  intro k v
  apply Additive.toMul.injective
  apply Subtype.ext
  change F.tildeProjection ⟨j, hJH j.property⟩ *
      (F.tildeProjection ⟨k, (F.Li_le L 1 k.property).2⟩ * v.toMul *
        (F.tildeProjection ⟨k, (F.Li_le L 1 k.property).2⟩)⁻¹) *
      (F.tildeProjection ⟨j, hJH j.property⟩)⁻¹ =
    F.tildeProjection ⟨(j : G) * k * (j : G)⁻¹, _⟩ *
      (F.tildeProjection ⟨j, hJH j.property⟩ * v.toMul *
        (F.tildeProjection ⟨j, hJH j.property⟩)⁻¹) *
      (F.tildeProjection ⟨(j : G) * k * (j : G)⁻¹, _⟩)⁻¹
  have he : (⟨(j : G) * k * (j : G)⁻¹, _⟩ : F.H) =
      ⟨j, hJH j.property⟩ * ⟨k, (F.Li_le L 1 k.property).2⟩ *
        (⟨j, hJH j.property⟩ : F.H)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv]
  group

namespace NaturalSeedMarking
variable (D : F.NaturalSeedMarking L hLV)
include D

/-- The seed coordinates intertwine the published natural actor. -/
theorem naturalActor_equivariant (k : F.Li L 1) (v : Additive (F.tilde V)) :
    D.coordinates (F.localSeedRepresentation L hLV k v) = D.naturalActor k (D.coordinates v) :=
  D.equivariant k v

/-- The full marked linear actor acts simply on its natural seed. -/
theorem seed_simple_of_gt_three (hn : 3 < n) :
    IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule := by
  let σ := F.localSeedRepresentation L hLV
  let e := σ.asModuleEquiv.trans D.coordinates
  let : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial σ.asModule := e.toEquiv.nontrivial
  rw [isSimpleModule_iff, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · simpa only [hw] using S.zero_mem
  have hev : e v ≠ 0 := fun h => hv0 (e.injective (h.trans e.map_zero.symm))
  have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans e.map_zero.symm))
  obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hev hew
  obtain ⟨k, rfl⟩ := D.naturalActor_surjective hn g
  have hk : (MonoidAlgebra.of (ZMod 2) (F.Li L 1) k) • v = w := by
    apply e.injective
    change D.coordinates (σ.asModuleEquiv (_ • v)) = _
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    exact (D.equivariant k _).trans hg
  exact hk ▸ S.smul_mem _ hv

/-- Above binary dimension two, perfectness identifies the derived actor with GL. -/
noncomputable def fullQuotientEquiv (hn : 3 < n) :
    (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) ≃* BinaryLinear.OuterCyclic.LinearGroup (n - 1) := by
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup (n - 1)) :=
    BinaryLinear.linearGroup_isPerfect (n - 1) (by omega)
  exact D.quotientEquiv.trans (MulEquiv.ofBijective (commutator _).subtype
    ⟨Subtype.val_injective, fun g => ⟨⟨g, Group.IsPerfect.mem_commutator⟩, rfl⟩⟩)

/-- Literal conjugation on L₁ transported through its characteristic quotient. -/
noncomputable def modelConjugation (hn : 3 < n) (J : Subgroup G)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) :
    J →* MulAut (BinaryLinear.OuterCyclic.LinearGroup (n - 1)) :=
  (MulAut.congr (D.fullQuotientEquiv hn)).toMonoidHom.comp
    ((quotientAut (pCore 2 (F.Li L 1))).comp (F.localConjugation L J hJK))

/-- The transported automorphism agrees with the actual left conjugation. -/
theorem modelConjugation_actor (hn : 3 < n) (J : Subgroup G)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) (j : J) (k : F.Li L 1) :
    D.modelConjugation hn J hJK j (D.naturalActor k) =
      D.naturalActor (F.localConjugation L J hJK j k) := by
  change D.fullQuotientEquiv hn (quotientAut (pCore 2 (F.Li L 1))
    (F.localConjugation L J hJK j)
    ((D.fullQuotientEquiv hn).symm (D.fullQuotientEquiv hn
      (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k)))) = _
  rw [MulEquiv.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- A seed intertwiner implements an inner automorphism of its full actor. -/
theorem modelConjugation_inner_of_intertwiner (hn : 3 < n) (J : Subgroup G)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) (j : J)
    (c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V))
    (hc : ∀ k v, c (F.localSeedRepresentation L hLV k v) =
      F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v)) :
    D.modelConjugation hn J hJK j ∈
      MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup (n - 1)) := by
  let a := D.coordinates.symm.trans (c.trans D.coordinates)
  refine ⟨a, ?_⟩
  apply MulEquiv.ext
  intro g
  obtain ⟨k, rfl⟩ := D.naturalActor_surjective hn g
  rw [D.modelConjugation_actor]
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := (c.trans D.coordinates).surjective v
  change D.coordinates (c (D.coordinates.symm
    (D.naturalActor k (D.coordinates (c.symm (D.coordinates.symm
      (D.coordinates (c w)))))))) =
    D.naturalActor (F.localConjugation L J hJK j k) (D.coordinates (c w))
  rw [D.coordinates.symm_apply_apply, c.symm_apply_apply, ← D.naturalActor_equivariant,
    D.coordinates.symm_apply_apply, hc, D.naturalActor_equivariant]

/-- An inner automorphism of the marked actor gives an actual seed intertwiner. -/
theorem intertwiner_of_modelConjugation_inner (hn : 3 < n) (J : Subgroup G)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) (j : J)
    (hj : D.modelConjugation hn J hJK j ∈
      MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup (n - 1))) :
    ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  obtain ⟨a, ha⟩ := hj
  refine ⟨D.coordinates.trans (a.trans D.coordinates.symm), ?_⟩
  intro k v
  apply D.coordinates.injective
  change D.coordinates (D.coordinates.symm (a (D.coordinates
    (F.localSeedRepresentation L hLV k v)))) = _
  rw [D.coordinates.apply_symm_apply, D.naturalActor_equivariant, D.naturalActor_equivariant]
  have he := D.modelConjugation_actor hn J hJK j k
  rw [← ha] at he
  have hv := congrArg (fun g : BinaryLinear.OuterCyclic.LinearGroup (n - 1) =>
    g (a (D.coordinates v))) he
  simpa only [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply] using hv

omit [IsElementaryAbelian 2 (F.tilde V)] D in
private theorem small_outer_two (d : ℕ) (hd₀ : 3 ≤ d) (hd₁ : d ≤ 5) :
    IsPGroup 2 (MulAut.Outer (BinaryLinear.OuterCyclic.LinearGroup d)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup d))
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨g, hg | hg⟩ := BinaryLinear.InvariantNodeActions.smallDimension_inner_graph hd₀ hd₁ a
  · have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    refine ⟨1, ?_⟩
    change (q a) ^ (2 ^ 1) = 1
    rw [hg, hi, one_pow]
  · have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    refine ⟨1, ?_⟩
    change (q a) ^ (2 ^ 1) = 1
    rw [hg, map_mul, hi, mul_one, pow_one, ← map_pow,
      BinaryLinear.OuterCyclic.graphLinear_sq, map_one]

/-- The actual ambient Sylow subgroup excludes the graph automorphism image. -/
theorem seed_intertwiners_of_gt_three [Finite G] (hn : 3 < n) (hn₁ : n ≤ 5)
    (J : Subgroup G) (hJH : J ≤ F.H) (hTJ : (T : Subgroup G) ≤ J)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) :
    ∀ j : J, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup (n - 1)))
  let f := q.comp (D.modelConjugation hn J hJK)
  let S := T.subtype hTJ
  have hker : (S : Subgroup J) ≤ f.ker := by
    intro j hj
    apply (QuotientGroup.eq_one_iff _).mpr
    have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant n
    obtain ⟨c, hc⟩ := seed_intertwiner_of_normalizes (hLV := hLV) hJH hJK j (hTV hj)
    exact D.modelConjugation_inner_of_intertwiner hn J hJK j c hc
  let : Finite f.range := Set.finite_range f |>.to_subtype
  have hrange : IsPGroup 2 f.range := (small_outer_two (n - 1) (by omega) (by omega)).to_subgroup _
  obtain ⟨r, hr⟩ := hrange.exists_card_eq
  have hi : f.ker.index = 2 ^ r := (index_ker f).trans hr
  have hr0 : r = 0 := by
    by_contra hr0
    apply S.not_dvd_index
    apply dvd_trans _ (index_dvd_of_le hker)
    rw [hi]
    exact dvd_pow_self 2 hr0
  have htop : f.ker = ⊤ := index_eq_one.mp (by simpa only [hr0, pow_zero] using hi)
  intro j
  apply D.intertwiner_of_modelConjugation_inner hn J hJK j
  apply (QuotientGroup.eq_one_iff _).mp
  have hj : j ∈ f.ker := htop ▸ (show j ∈ (⊤ : Subgroup J) from mem_top j)
  exact hj

/-- The source local-family and relative-normality hypotheses give the exact
normalizer and two representation premises when n is four or five. -/
theorem seed_premises_of_gt_three [Finite G] (hn : 3 < n) (hn₁ : n ≤ 5)
    {M J : Subgroup G} (hJ : J ∈ F.Hz L M) [((F.Li L 1).subgroupOf J).Normal] :
    ∃ hJK : J ≤ normalizer (F.Li L 1 : Set G),
      IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule ∧
      ∀ j : J, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
        ∀ k v, c (F.localSeedRepresentation L hLV k v) =
          F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  let hJK := F.normalizes_Li_one_of_relative_normal hJ
  exact ⟨hJK, D.seed_simple_of_gt_three hn,
    D.seed_intertwiners_of_gt_three hn hn₁ J hJ.2.1 (F.sylow_le_of_mem_Hz hJ) hJK⟩

/-- The marked natural seed is simple, including the derived binary-plane actor. -/
theorem seed_simple (hn : 3 ≤ n) :
    IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule := by
  by_cases hn3 : n = 3
  · subst n
    exact D.seed_simple_rank_three
  · exact D.seed_simple_of_gt_three (by omega)

/-- Every literal conjugation twist of the natural seed is equivalent to it.
The higher-rank argument uses the actual ambient Sylow subgroup contained in J. -/
theorem seed_intertwiners [Finite G] (hn : 3 ≤ n) (hn₁ : n ≤ 5)
    (J : Subgroup G) (hJH : J ≤ F.H) (hTJ : (T : Subgroup G) ≤ J)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) :
    ∀ j : J, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  by_cases hn3 : n = 3
  · subst n
    exact D.seed_intertwiners_rank_three J hJK
  · exact D.seed_intertwiners_of_gt_three (by omega) hn₁ J hJH hTJ hJK

/-- Source local membership and relative normality supply the normalizer,
simple seed, and all conjugation intertwiners throughout 3≤n≤5. -/
theorem seed_premises [Finite G] (hn : 3 ≤ n) (hn₁ : n ≤ 5)
    {M J : Subgroup G} (hJ : J ∈ F.Hz L M) [((F.Li L 1).subgroupOf J).Normal] :
    ∃ hJK : J ≤ normalizer (F.Li L 1 : Set G),
      IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule ∧
      ∀ j : J, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
        ∀ k v, c (F.localSeedRepresentation L hLV k v) =
          F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  let hJK := F.normalizes_Li_one_of_relative_normal hJ
  exact ⟨hJK, D.seed_simple hn,
    D.seed_intertwiners hn hn₁ J hJ.2.1 (F.sylow_le_of_mem_Hz hJ) hJK⟩

end NaturalSeedMarking
variable [Finite G] [IsElementaryAbelian 2 V]

/-- The homogeneous decomposition in 12.8.5(1) for 3≤n≤5 from the supplied
natural seed marking and earlier elementary-quotient input. No simplicity,
conjugation-intertwiner, or homogeneous-coordinate premise remains. -/
theorem homogeneous_coordinates_of_natural_seed
    (hn : 3 ≤ n) (hn₁ : n ≤ 5) (D : F.NaturalSeedMarking L hLV)
    {M J : Subgroup G} (hJ : J ∈ F.Hz L M) [((F.Li L 1).subgroupOf J).Normal]
    [IsElementaryAbelian 2 (F.tilde (F.UH J))] :
    ∃ r : ℕ, ∃ e : Additive (F.tilde (F.UH J)) ≃ₗ[ZMod 2] (Fin r → Additive (F.tilde V)),
      ∀ (k : F.Li L 1) u i,
        e (Additive.ofMul (F.localTildeAction J hJ.2.1
          (inclusion (F.Li_one_le_of_mem_Hz hJ) k) u.toMul)) i =
          Additive.ofMul (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
            ((F.Li_le L 1).trans (inf_le_left.trans hLV)) k (e u i).toMul) := by
  obtain ⟨hJK, hsimple, htwist⟩ := D.seed_premises hn hn₁ hJ
  exact F.homogeneous_coordinates_of_seed_intertwiners L J hLV hJ.2.1
    (F.Li_one_le_of_mem_Hz hJ) hJK hsimple htwist

/-- Source 12.8.5(1) for n=4,5, with only the marked seed and the earlier
 elementary-quotient hypothesis retained. The seed premises are discharged. -/
theorem homogeneous_coordinates_of_natural_seed_gt_three
    (hn : 3 < n) (hn₁ : n ≤ 5) (D : F.NaturalSeedMarking L hLV)
    {M J : Subgroup G} (hJ : J ∈ F.Hz L M) [((F.Li L 1).subgroupOf J).Normal]
    [IsElementaryAbelian 2 (F.tilde (F.UH J))] :
    ∃ r : ℕ, ∃ e : Additive (F.tilde (F.UH J)) ≃ₗ[ZMod 2] (Fin r → Additive (F.tilde V)),
      ∀ (k : F.Li L 1) u i,
        e (Additive.ofMul (F.localTildeAction J hJ.2.1
          (inclusion (F.Li_one_le_of_mem_Hz hJ) k) u.toMul)) i =
          Additive.ofMul (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
            ((F.Li_le L 1).trans (inf_le_left.trans hLV)) k (e u i).toMul) := by
  obtain ⟨hJK, hsimple, htwist⟩ := D.seed_premises_of_gt_three hn hn₁ hJ
  exact F.homogeneous_coordinates_of_seed_intertwiners L J hLV hJ.2.1
    (F.Li_one_le_of_mem_Hz hJ) hJK hsimple htwist

/-- In the actual J=G₁ dimension consumer, relative normality and the natural
seed marking supply both the simple seed and all conjugation intertwiners. -/
theorem nonabelian_exclusion_of_natural_seed
    (hn : 3 < n) (hn₁ : n ≤ 5) (D : F.NaturalSeedMarking L hLV)
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
  have hHK : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (K := F.H)
      ((F.Li_le L 1).trans inf_le_right)).mp inferInstance
  exact nonabelian_exclusion_of_seed_intertwiners hn D hHK
    (D.seed_simple hn.le)
    (D.seed_intertwiners hn.le hn₁ F.H le_rfl (F.invariant 1) hHK)
    B hB hrad hnonab

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
