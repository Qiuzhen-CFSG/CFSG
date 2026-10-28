module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.PointCentralizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Intersections
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.PairNormalizer


/-!
# Pair-plane normalizer estimates in the original J4 source data

The original Todd embedding identifies pure second-class subgroups with
pair subspaces. Their marked normalizer quotient is exactly the native
pair-vector/subspace stabilizer under the unchanged Todd projection.
It has two-rank at most four, and its involutions fix 128 elements of the
original E. The exact earlier intersection premise bounds normalizers of
proper overgroups of the pair plane inside C_G(t).

These are the numerical and normalizer barriers preceding the first fixed-
coset argument. They do not assert either fixed-coset conclusion or full
centralizer containment.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(a),(b),(d), p.602.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- Coordinates on an actual subgroup under the original Todd embedding. -/
noncomputable def toddSubspace (P : PointData z) (U : Subgroup G) :
    Submodule (ZMod 2) Cocode :=
  AddSubgroup.toZModSubmodule 2 (U.comap P.vectorEmbedding).toAddSubgroup'

theorem toddSubspace_card (P : PointData z) (U : Subgroup G) (hUE : U ≤ P.E) :
    Nat.card (toddSubspace P U) = Nat.card U := by
  let f : toddSubspace P U → U := fun v =>
    ⟨P.vectorEmbedding (Multiplicative.ofAdd v.val),v.property⟩
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨v,hv⟩ := hUE u.property
    have hw : v.toAdd ∈ toddSubspace P U := by
      change P.vectorEmbedding v ∈ U
      rw [hv]
      exact u.property
    exact ⟨⟨v.toAdd,hw⟩,Subtype.ext hv⟩
  have hi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (P.vectorEmbedding_injective (congrArg (fun x : U => (x : G)) he))
  exact Nat.card_congr (Equiv.ofBijective f ⟨hi,hf⟩)

theorem toddSubspace_pairs (a : LocalData h) (U : Subgroup G)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) :
    ∀ v ∈ toddSubspace a.P U, v ≠ 0 → ∃ B : PointPair, v = pairVector B := by
  intro v hv hv0
  have hne : a.P.vectorEmbedding (Multiplicative.ofAdd v) ≠ 1 := by
    intro he
    exact hv0 (congrArg Multiplicative.toAdd
      (a.P.vectorEmbedding_injective (he.trans (map_one _).symm)))
  obtain ⟨m,hm,he⟩ := hp _ hv hne
  rw [second,vector_conj a.P ⟨m,hm⟩,pairVector_equivariant] at he
  exact ⟨_,(congrArg Multiplicative.toAdd (a.P.vectorEmbedding_injective he)).symm⟩

/-- The normalizer inside the original second centralizer C_M(t). -/
noncomputable abbrev pairNormalizer (a : LocalData h) (U : Subgroup G) : Subgroup G :=
  normalizer (U : Set G) ⊓ secondCentralizer a

/-- Restriction of the same Todd projection, without changing the ambient embedding. -/
noncomputable def pairNormalizerProjection (a : LocalData h) (U : Subgroup G) :
    pairNormalizer a U →* M24 :=
  a.P.projection.comp (inclusion (show pairNormalizer a U ≤ a.P.M from
    inf_le_right.trans inf_le_right))

theorem pairNormalizerProjection_ker (a : LocalData h) (U : Subgroup G) :
    (pairNormalizerProjection a U).ker = a.P.E.subgroupOf (pairNormalizer a U) := by
  ext m
  change a.P.projection ⟨m.val,m.property.2.2⟩ = 1 ↔ _
  change (⟨m.val,m.property.2.2⟩ : a.P.M) ∈ a.P.projection.ker ↔ _
  rw [a.P.projection_ker]
  rfl

instance pairNormalizer_radical_normal (a : LocalData h) (U : Subgroup G) :
    (a.P.E.subgroupOf (pairNormalizer a U)).Normal := by
  rw [←pairNormalizerProjection_ker a U]
  infer_instance

/-- The quotient uses the original radical and the actual restricted projection. -/
noncomputable def pairNormalizerQuotientEquiv (a : LocalData h) (U : Subgroup G) :
    (pairNormalizer a U ⧸ a.P.E.subgroupOf (pairNormalizer a U)) ≃*
      (pairNormalizerProjection a U).range :=
  (QuotientGroup.quotientMulEquivOfEq (pairNormalizerProjection_ker a U).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem pairNormalizerQuotientEquiv_mk (a : LocalData h) (U : Subgroup G)
    (m : pairNormalizer a U) :
    (pairNormalizerQuotientEquiv a U (QuotientGroup.mk' _ m) : M24) =
      pairNormalizerProjection a U m := rfl

/-- Literal normalizer transport through the original Todd coordinates. -/
theorem pairNormalizerProjection_range_le (a : LocalData h) (U : Subgroup G) :
    (pairNormalizerProjection a U).range ≤
      cocodeVectorStabilizer cocodeRepresentation (pairVector ⟨{0,1},by decide⟩) ⊓
        subspaceStabilizer cocodeRepresentation (toddSubspace a.P U) := by
  rintro g ⟨m,rfl⟩
  refine ⟨(second_centralizer_iff a ⟨m.val,m.property.2.2⟩).mp m.property.2.1,?_⟩
  intro v
  change a.P.vectorEmbedding
    (Multiplicative.ofAdd (cocodeRepresentation (a.P.projection ⟨m.val,m.property.2.2⟩) v)) ∈ U ↔
      a.P.vectorEmbedding (Multiplicative.ofAdd v) ∈ U
  rw [←vector_conj a.P ⟨m.val,m.property.2.2⟩]
  exact (mem_normalizer_iff.mp m.property.1 _).symm

/-- The numerical part of AS91 (6.3)(b), on the literal original quotient. -/
theorem pairNormalizer_quotient_rank_le_four (a : LocalData h) (U : Subgroup G)
    (hUE : U ≤ a.P.E) (ht : second a ∈ U) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) :
    primeRank 2 (pairNormalizer a U ⧸ a.P.E.subgroupOf (pairNormalizer a U)) ≤ 4 := by
  rw [primeRank_equiv 2 (pairNormalizerQuotientEquiv a U)]
  have hr := primeRank_le_of_injective 2
    (inclusion (pairNormalizerProjection_range_le a U))
    (inclusion_injective (pairNormalizerProjection_range_le a U))
  apply hr.trans
  exact MathieuCode.J4Fusion.pair_plane_stabilizer_rank_le_four
    (toddSubspace a.P U) (toddSubspace_pairs a U hp) ⟨{0,1},by decide⟩ ht
    (by rw [toddSubspace_card a.P U hUE]; exact hc)

/-- The same projected involutions have fixed rank seven in the original Todd coordinates. -/
theorem pairNormalizer_involution_fixed_finrank (a : LocalData h) (U : Subgroup G)
    (hUE : U ≤ a.P.E) (ht : second a ∈ U) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u)
    (s : M24) (hs : s ∈ (pairNormalizerProjection a U).range) (ho : orderOf s = 2) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (zpowers s)) = 7 :=
  MathieuCode.J4Fusion.pair_plane_involution_fixed_finrank
    (toddSubspace a.P U) (toddSubspace_pairs a U hp) ⟨{0,1},by decide⟩ ht
    (by rw [toddSubspace_card a.P U hUE]; exact hc)
    s (pairNormalizerProjection_range_le a U hs) ho

/-- A pure second-class subgroup larger than a line has exactly four elements. -/
theorem pair_subgroup_card_eq_four (a : LocalData h) (U : Subgroup G)
    (hUE : U ≤ a.P.E) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) :
    Nat.card U = 4 := by
  have hr := MathieuCode.J4Fusion.pair_space_finrank_le_two
    (toddSubspace a.P U) (toddSubspace_pairs a U hp)
  have hcard : Nat.card U = 2 ^ Module.finrank (ZMod 2) (toddSubspace a.P U) := by
    rw [←toddSubspace_card a.P U hUE,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hl : ¬ Module.finrank (ZMod 2) (toddSubspace a.P U) ≤ 1 := by
    intro hh
    have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    rw [←hcard] at hb
    norm_num at hb
    omega
  rw [hcard,show Module.finrank (ZMod 2) (toddSubspace a.P U) = 2 by omega]
  decide

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The image is the whole marked native stabilizer, not merely an abstract
subgroup of the same rank. -/
theorem pairNormalizerProjection_range (a : LocalData h) (U : Subgroup G)
    (hUE : U ≤ a.P.E) :
    (pairNormalizerProjection a U).range =
      cocodeVectorStabilizer cocodeRepresentation (pairVector ⟨{0,1},by decide⟩) ⊓
        subspaceStabilizer cocodeRepresentation (toddSubspace a.P U) := by
  apply le_antisymm (pairNormalizerProjection_range_le a U)
  intro g hg
  obtain ⟨m,hm⟩ := a.projection_surjective g
  have hc : (m : G) ∈ centralizer (second a) :=
    (second_centralizer_iff a m).mpr (hm ▸ hg.1)
  have hn : (m : G) ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      obtain ⟨v,hv⟩ := hUE hu
      rw [←hv]
      change MulAut.conj (m : G) (a.P.vectorEmbedding (Multiplicative.ofAdd v.toAdd)) ∈ U
      rw [vector_conj a.P m,hm]
      exact (hg.2 _).mpr (by change a.P.vectorEmbedding v ∈ U; rw [hv]; exact hu)
    · rw [card_map_of_injective (MulAut.conj (m : G)).injective]
  exact ⟨⟨m,hn,hc,m.property⟩,hm⟩

/-- The whole original E lies in this relative normalizer whenever U ≤ E. -/
theorem E_le_pairNormalizer (a : LocalData h) (U : Subgroup G) (hUE : U ≤ a.P.E) :
    a.P.E ≤ pairNormalizer a U := by
  let := a.P.E_elementary
  intro e he
  have hec : e ∈ Subgroup.centralizer (U : Set G) := by
    intro u hu
    exact setLike_mul_comm (hUE hu) he
  refine ⟨Subgroup.centralizer_le_normalizer _ hec,?_,a.P.E_le he⟩
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm he (second_mem a))

/-- Source (6.3)(d) forces a large subgroup of E to have
no escaping normalizer inside I=C_G(t). This is the first barrier in the
printed fixed-coset argument. -/
theorem large_second_subgroup_normalizer_le (a : LocalData h) (hi : MarkerIntersection a)
    (V : Subgroup G) (hVE : V ≤ a.P.E) (hc : 4 < Nat.card V) :
    normalizer (V : Set G) ⊓ centralizer (second a) ≤ a.P.M := by
  intro g hg
  by_contra hgm
  have hVg : V ≤ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hVE ?_
    have he := mem_normalizer_iff_map_conj_eq.mp hg.1
    rw [←he]
    exact map_mono hVE
  have hb := (card_le_of_le hVg).trans
    (centralizer_intersection_card_le_four a hi g hg.2 hgm)
  omega

/-- The literal first step after (6.3)(d): every proper overgroup of the
chosen pure pair plane in E has normalizer in I contained in I ∩ M. -/
theorem strict_pair_overgroup_normalizer_le (a : LocalData h) (hi : MarkerIntersection a)
    (U V : Subgroup G) (hVE : V ≤ a.P.E) (hUV : U < V) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) :
    normalizer (V : Set G) ⊓ centralizer (second a) ≤ secondCentralizer a := by
  have hcard := pair_subgroup_card_eq_four a U (hUV.le.trans hVE) hc hp
  have hlarge : 4 < Nat.card V := by
    by_contra hn
    have he := eq_of_le_of_card_ge hUV.le (by omega : Nat.card V ≤ Nat.card U)
    exact hUV.ne he
  exact le_inf inf_le_right (large_second_subgroup_normalizer_le a hi V hVE hlarge)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

private theorem vector_centralizes_iff (P : PointData z) (m : P.M) (v : Cocode) :
    P.vectorEmbedding (Multiplicative.ofAdd v) ∈ centralizer (m : G) ↔
      cocodeRepresentation (P.projection m) v = v := by
  have hh := vector_conj P m v
  constructor
  · intro hv
    have he : MulAut.conj (m : G) (P.vectorEmbedding (Multiplicative.ofAdd v)) =
        P.vectorEmbedding (Multiplicative.ofAdd v) :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hv).symm
    exact congrArg Multiplicative.toAdd (P.vectorEmbedding_injective (hh.symm.trans he))
  · intro hv
    rw [hv] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Fixed spaces under the literal Todd projection count actual elements
of the original ambient radical centralizer. -/
theorem todd_centralizer_card (P : PointData z) (m : P.M) :
    Nat.card (P.E ⊓ centralizer (m : G) : Subgroup G) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (zpowers (P.projection m))) := by
  have he : toddSubspace P (P.E ⊓ centralizer (m : G)) =
      fixedSpace cocodeRepresentation (zpowers (P.projection m)) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change (P.vectorEmbedding (Multiplicative.ofAdd v) ∈ P.E ∧
      P.vectorEmbedding (Multiplicative.ofAdd v) ∈ centralizer (m : G)) ↔ _
    rw [and_iff_right ⟨_,rfl⟩]
    exact vector_centralizes_iff P m v
  rw [←toddSubspace_card P _ inf_le_left,he,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]

/-- AS91 (6.3)(a), with the fixed ranks transported to C_E(m). -/
theorem todd_involution_centralizer_card (a : LocalData h) (m : a.P.M)
    (ho : orderOf (a.P.projection m) = 2) :
    Nat.card (a.P.E ⊓ centralizer (m : G) : Subgroup G) = 128 ∨
    Nat.card (a.P.E ⊓ centralizer (m : G) : Subgroup G) = 64 := by
  rw [todd_centralizer_card]
  rcases MathieuCode.J4Fusion.involution_fixed_finrank (a.P.projection m) ho with he | he
  · rw [he]; exact Or.inl rfl
  · rw [he]; exact Or.inr rfl

/-- The source's strict inequality 2+4<7 uses this same C_E(m),
not an unrelated native fixed-space dimension. -/
theorem pairNormalizer_involution_centralizer_card (a : LocalData h) (U : Subgroup G)
    (hUE : U ≤ a.P.E) (ht : second a ∈ U) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u)
    (m : pairNormalizer a U) (ho : orderOf (pairNormalizerProjection a U m) = 2) :
    Nat.card (a.P.E ⊓ centralizer (m : G) : Subgroup G) = 128 := by
  rw [todd_centralizer_card a.P ⟨m.val,m.property.2.2⟩]
  have hf := pairNormalizer_involution_fixed_finrank a U hUE ht hc hp
    _ ⟨m,rfl⟩ ho
  change Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation
    (zpowers (a.P.projection ⟨m.val,m.property.2.2⟩))) = 7 at hf
  rw [hf]
  decide

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
