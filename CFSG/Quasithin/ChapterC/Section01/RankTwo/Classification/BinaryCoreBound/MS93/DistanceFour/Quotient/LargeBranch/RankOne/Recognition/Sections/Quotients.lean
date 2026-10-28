module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Transport

/-!
# The literal two sections in MS93 (4.6.12)

The first denominator is K = V_alpha intersect Q_c. The second is the
commutator preimage Y of the fixed subgroup C_{K/Z_alpha}(T_beta). Both
contain Z_alpha, and Y is normal in K and preserved by the edge kernel.
In any of the constructed radius modules, the image of Y is exactly the
intersection of the image of K with the actual edge fixed space.

The quotient and section maps below are surjective homomorphisms with
exact relative kernels. They preserve the source denominators before
any rank-one recognition. No assertion about index four or natural
module decomposition is made by these constructions.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(1)--(2), printed p.910; notation on printed p.905.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
open Representation.BinaryOffender
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

namespace LayerModule
variable {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)

/-- A subgroup containing the denominator is recovered from its quotient image. -/
theorem projection_mem_subspace_iff (T : Subgroup (FreeAmalgam R))
    (hZT : Z R (alpha R) ≤ T) (x : S) :
    (d.projection x).toAdd ∈ d.subspace T ↔ (x : FreeAmalgam R) ∈ T := by
  change x ∈ ((T.subgroupOf S).map d.projection).comap d.projection ↔ _
  rw [comap_map_eq_self (show d.projection.ker ≤ T.subgroupOf S by
    rw [d.kernel]; exact fun _ hx => hZT hx)]
  rfl

/-- The actual projection through a subspace image, before any module recognition. -/
noncomputable def quotientMap (T : Subgroup (FreeAmalgam R)) :
    S →* Multiplicative (d.Space ⧸ d.subspace T) :=
  (AddMonoidHom.toMultiplicative (d.subspace T).mkQ.toAddMonoidHom).comp d.projection

/-- The linear quotient projection is onto. -/
theorem quotientMap_surjective (T : Subgroup (FreeAmalgam R)) :
    Function.Surjective (d.quotientMap T) := by
  intro v
  obtain ⟨w, hw⟩ := (d.subspace T).mkQ_surjective v.toAdd
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd w)
  refine ⟨x, ?_⟩
  change Multiplicative.ofAdd ((d.subspace T).mkQ (d.projection x).toAdd) = v
  rw [hx]
  exact congrArg Multiplicative.ofAdd hw

/-- Its relative kernel is exactly T, provided T contains Z_alpha. -/
theorem quotientMap_kernel (T : Subgroup (FreeAmalgam R))
    (hZT : Z R (alpha R) ≤ T) :
    (d.quotientMap T).ker = T.subgroupOf S := by
  ext x
  change (d.subspace T).mkQ (d.projection x).toAdd = 0 ↔ _
  change (d.projection x).toAdd ∈ (d.subspace T).mkQ.ker ↔ _
  rw [Submodule.ker_mkQ]
  exact d.projection_mem_subspace_iff T hZT x

/-- The quotient dimension computes the index of the literal ambient denominator. -/
theorem quotient_relIndex (T : Subgroup (FreeAmalgam R))
    (hZT : Z R (alpha R) ≤ T) :
    T.relIndex S = 2 ^ Module.finrank (ZMod 2) (d.Space ⧸ d.subspace T) := by
  change (T.subgroupOf S).index = _
  rw [← d.quotientMap_kernel T hZT, index_ker,
    MonoidHom.range_eq_top.mpr (d.quotientMap_surjective T), Nat.card_congr (topEquiv).toEquiv]
  change Nat.card (d.Space ⧸ d.subspace T) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- Being fixed in the Z_alpha quotient means that the actual ambient commutator lies in Z_alpha. -/
theorem fixed_iff_commutator_mem (m : M)
    (hn : embedM R m ∈ normalizer S) (x : S) :
    d.representation (source.projection m) (d.projection x).toAdd = (d.projection x).toAdd ↔
      ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ Z R (alpha R) := by
  let y : S := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp hn x).mp x.property⟩
  rw [← d.action m x y rfl]
  have hc : (y * x⁻¹ : S) ∈ d.projection.ker ↔
      ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ Z R (alpha R) := by
    rw [d.kernel]
    rfl
  rw [← hc]
  change (d.projection y).toAdd = (d.projection x).toAdd ↔ d.projection (y * x⁻¹) = 1
  rw [map_mul, map_inv, mul_inv_eq_one]
  exact Multiplicative.toAdd.injective.eq_iff.symm

/-- Restrict the original projection to the actual image of a subgroup. -/
noncomputable def subspaceMap (T : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    T →* Multiplicative (d.subspace T) where
  toFun x := Multiplicative.ofAdd ⟨(d.projection (inclusion hT x)).toAdd,
    (d.mem_subspace_iff T _).mpr ⟨inclusion hT x, x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_one (d.projection.comp (inclusion hT)))
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul (d.projection.comp (inclusion hT)) x y)

/-- No extra image-surjectivity hypothesis is needed for restriction. -/
theorem subspaceMap_surjective (T : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    Function.Surjective (d.subspaceMap T hT) := by
  intro v
  obtain ⟨x, hx, he⟩ := (d.mem_subspace_iff T v.toAdd).mp v.toAdd.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- The literal projection T → (T/Z_alpha)/(N/Z_alpha). -/
noncomputable def sectionMap (T N : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    T →* Multiplicative ((d.subspace T) ⧸
      (d.subspace N).comap (d.subspace T).subtype) :=
  (AddMonoidHom.toMultiplicative
    ((d.subspace N).comap (d.subspace T).subtype).mkQ.toAddMonoidHom).comp
      (d.subspaceMap T hT)

/-- The second section map is also onto its actual linear quotient. -/
theorem sectionMap_surjective (T N : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    Function.Surjective (d.sectionMap T N hT) := by
  intro v
  obtain ⟨w, hw⟩ := ((d.subspace N).comap (d.subspace T).subtype).mkQ_surjective v.toAdd
  obtain ⟨x, hx⟩ := d.subspaceMap_surjective T hT (Multiplicative.ofAdd w)
  refine ⟨x, ?_⟩
  change Multiplicative.ofAdd
    (((d.subspace N).comap (d.subspace T).subtype).mkQ
      (d.subspaceMap T hT x).toAdd) = v
  rw [hx]
  exact congrArg Multiplicative.ofAdd hw

/-- The second section keeps the exact relative kernel N ∩ T. -/
theorem sectionMap_kernel (T N : Subgroup (FreeAmalgam R)) (hT : T ≤ S)
    (hZN : Z R (alpha R) ≤ N) :
    (d.sectionMap T N hT).ker = N.subgroupOf T := by
  ext x
  change (d.subspaceMap T hT x).toAdd ∈
    ((d.subspace N).comap (d.subspace T).subtype).mkQ.ker ↔ _
  rw [Submodule.ker_mkQ]
  exact d.projection_mem_subspace_iff N hZN (inclusion hT x)

end LayerModule

namespace Sections

/-- The literal first denominator of (4.6.12)(1). -/
noncomputable def intersection (c : Vertex R) : Subgroup (FreeAmalgam R) := V R (alpha R) ⊓ Q R c

/-- The ambient inverse image of C_{K/Z_alpha}(T_beta), as on printed p.910. -/
noncomputable def fixedPreimage (c : Vertex R) : Subgroup (FreeAmalgam R) :=
  commutatorPreimage (intersection c) (Q R (beta R)) (Z R (alpha R))

variable (common : CommonFacts R source geometry)

include common in
/-- Z_alpha is contained in the first denominator, using the strict critical-radius bound. -/
theorem Z_le_intersection {c : Vertex R}
    (hd : (cosetGraph R).dist (alpha R) c = 2) : Z R (alpha R) ≤ intersection c := by
  refine le_inf (Z_le_VBall R (alpha R) 2) ?_
  rw [← common.X_eq_Z (alpha R) rfl]
  apply common.X_bound (alpha R) rfl c (distance_two_color rfl hd)
  rw [hd, geometry.distance_constant (alpha R) rfl]
  exact common.large_distance

/-- The edge kernel normalizes K, since it fixes both vertices. -/
theorem edge_normalizes_intersection {c : Vertex R} (hbc : Adjacent R (beta R) c) :
    Q R (beta R) ≤ normalizer (intersection c) := by
  apply le_normalizer_inf
  · exact (show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans
      (DistanceEight.V_normalized R _)
  · exact (show Q R (beta R) ≤ stabilizer R c from fun _ hx => hx.2 _ hbc).trans
      (Q_normalized R c)

include common in
/-- The second denominator still contains the literal Z_alpha. -/
theorem Z_le_fixedPreimage {c : Vertex R}
    (hd : (cosetGraph R).dist (alpha R) c = 2) : Z R (alpha R) ≤ fixedPreimage c := by
  apply le_commutatorPreimage (Z_le_intersection common hd)
  exact le_normalizer_iff_commutator_le_left.mp
    ((show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Z_normalized R _))

include common in
/-- The edge action preserves the fixed-point preimage. -/
theorem edge_normalizes_fixedPreimage {c : Vertex R} (hbc : Adjacent R (beta R) c) :
    Q R (beta R) ≤ normalizer (fixedPreimage c) := by
  exact commutatorPreimage_normalized _ _ _ _
    (inf_le_left.trans ((geometry.V_local (alpha R) rfl common.large_distance).trans
      (Z_normalized R _))) (edge_normalizes_intersection hbc)
    (Q R (beta R)).le_normalizer
    ((show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Z_normalized R _))

include common in
/-- Normality of Y is relative to K, inside the finite local configuration. -/
theorem fixedPreimage_normal [Finite M] {c : Vertex R} (hbc : Adjacent R (beta R) c) :
    ((fixedPreimage c).subgroupOf (intersection c)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (commutatorPreimage_le _ _ _)).mpr
  exact (inf_le_left.trans ((Flags.V_le_Q geometry common.large_distance _ rfl).trans
    (Q_le_adjacent_h R rfl (base_adjacent R)))).trans
      (edge_normalizes_fixedPreimage common hbc)

variable [Finite M] (d : LayerModule source (V R (alpha R)))

include common in
/-- The second denominator is the inverse image of the actual edge fixed space. -/
theorem fixedPreimage_eq_lifted_fixed (c : Vertex R) :
    fixedPreimage c =
      ((intersection c).subgroupOf (V R (alpha R)) ⊓
        ((fixedSpace d.representation (R.map source.projection)).toAddSubgroup.toSubgroup).comap
          d.projection).map (V R (alpha R)).subtype := by
  let F := ((fixedSpace d.representation (R.map source.projection)).toAddSubgroup.toSubgroup).comap
    d.projection
  let D := (intersection c).subgroupOf (V R (alpha R)) ⊓ F
  have hm (m : M) : embedM R m ∈ normalizer (V R (alpha R)) := by
    apply DistanceEight.V_normalized R (alpha R)
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  have hQZ : intersection c ≤ normalizer (Z R (alpha R)) :=
    inf_le_left.trans ((geometry.V_local (alpha R) rfl common.large_distance).trans
      (Z_normalized R _))
  apply le_antisymm
  · intro x hx
    have hxK := commutatorPreimage_le _ _ _ hx
    refine ⟨⟨x, hxK.1⟩, ⟨hxK, ?_⟩, rfl⟩
    change (d.projection ⟨x, hxK.1⟩).toAdd ∈ fixedSpace d.representation (R.map source.projection)
    rintro ⟨g, hg⟩
    obtain ⟨m, hmR, rfl⟩ := hg
    apply (d.fixed_iff_commutator_mem m (hm m) _).mpr
    have hc := commutator_commutatorPreimage_le (intersection c) (Q R (beta R))
      (Z R (alpha R)) hQZ
    rw [commutator_comm] at hc
    apply hc (commutator_mem_commutator _ hx)
    rw [Q_beta R]
    exact mem_map_of_mem _ hmR
  · change D.map (V R (alpha R)).subtype ≤ _
    apply le_commutatorPreimage
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · rw [commutator_comm]
      apply commutator_le.mpr
      intro t ht x hx
      rw [Q_beta R] at ht
      obtain ⟨m, hmR, rfl⟩ := ht
      obtain ⟨x, hx, rfl⟩ := hx
      apply (d.fixed_iff_commutator_mem m (hm m) x).mp
      exact hx.2 ⟨source.projection m, mem_map_of_mem _ hmR⟩

include common in
/-- Membership in Y is exactly membership in K together with fixation modulo Z_alpha. -/
theorem mem_fixedPreimage_iff (c : Vertex R) (x : V R (alpha R)) :
    (x : FreeAmalgam R) ∈ fixedPreimage c ↔
      (x : FreeAmalgam R) ∈ intersection c ∧
        (d.projection x).toAdd ∈ fixedSpace d.representation (R.map source.projection) := by
  rw [fixedPreimage_eq_lifted_fixed common d c]
  exact mem_map_iff_mem (V R (alpha R)).subtype_injective

include common in
/-- The literal tilde Y equals C_{K/Z_alpha}(T_beta) in the radius quotient. -/
theorem fixedPreimage_subspace (c : Vertex R) :
    d.subspace (fixedPreimage c) = d.subspace (intersection c) ⊓
      fixedSpace d.representation (R.map source.projection) := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff (fixedPreimage c) v).mp hv
    obtain ⟨hxK, hxF⟩ := (mem_fixedPreimage_iff common d c x).mp hx
    exact ⟨(d.mem_subspace_iff (intersection c) _).mpr ⟨x, hxK, rfl⟩, hxF⟩
  · rintro ⟨hvK, hvF⟩
    obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff (intersection c) v).mp hvK
    exact (d.mem_subspace_iff (fixedPreimage c) _).mpr
      ⟨x, (mem_fixedPreimage_iff common d c x).mpr ⟨hx, hvF⟩, rfl⟩

end Sections
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
