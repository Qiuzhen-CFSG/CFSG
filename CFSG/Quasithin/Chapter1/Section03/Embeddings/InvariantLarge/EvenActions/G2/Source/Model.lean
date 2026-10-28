module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Intrinsic
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry


/-!
# Standard Sylow normalizers and torus placement for the G₂ source action

The two intrinsic root subgroups of the standard unipotent group force its
normalizer to preserve the standard flag. The geometric flag stabilizer is
exactly the Borel. Consequently an automorphism preserving the unipotent group
has a Borel inner factor whenever universal inner–field coverage is supplied.

An odd-prime subgroup of the Borel can be conjugated into the split torus:
the torus has power-of-two index in the Borel, so a Sylow subgroup of the torus
is already Sylow in the Borel. This gives the simultaneous alignment needed
by the p-subgroup case of A.3.15(5), without a general Cartan-conjugacy theorem.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.50–51
and p.511. The octonion geometry is from the licensed ATLAS imports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.SylowParabolicInvariance
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.LieAutomorphismExtensions
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {E : Type*} [Field E] [CharP E 2]

theorem normalizer_unipotent :
    normalizer (unipotent (K := E) : Set (Model E)) = borel := by
  apply le_antisymm
  · intro g hg
    have hm := mem_normalizer_iff_map_conj_eq.mp hg
    have ha := map_eq_of_centralInvolutions unipotent highestRoot
      highestRoot_iff_centralInvolution (MulAut.conj g) hm
    have hb := map_eq_of_secondCentralInvolutions unipotent longRootLocal
      longRootLocal_iff_secondCentralInvolution (MulAut.conj g) hm
    have hga : g ∈ parabolic₁ := by
      rw [← normalizer_highestRoot]
      exact mem_normalizer_iff_map_conj_eq.mpr ha
    have hgb : g ∈ parabolic₂ := by
      rw [← normalizer_longRootLocal]
      exact mem_normalizer_iff_map_conj_eq.mpr hb
    rw [← standardFlag_stabilizer]
    constructor
    · rwa [parabolic₂, parabolic_eq_pointStabilizer] at hgb
    · rwa [shortParabolic_eq_lineStabilizer] at hga
  · apply sup_le le_normalizer
    exact le_normalizer_iff.mpr (fun _ ht _ hu => torus_normalizes_unipotent ht hu)

omit [CharP E 2] in
theorem field_map_unipotent (σ : E ≃+* E) :
    (unipotent (K := E)).map (fieldEquiv σ).toMonoidHom = unipotent := by
  ext g
  simp only [mem_map, unipotent_eq_range]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨σ ∘ t, (long_field_unipotentProduct σ t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨unipotentProduct (σ.symm ∘ t), ⟨_, rfl⟩, ?_⟩
    change fieldEquiv σ (unipotentProduct (σ.symm ∘ t)) = _
    rw [long_field_unipotentProduct]
    congr 1
    funext i
    exact σ.apply_symm_apply _

theorem borel_field_of_preserves_unipotent
    (hcover : Function.Surjective (semilinearAction (F := E)))
    (a : MulAut (Model E)) (ha : unipotent.map a.toMonoidHom = unipotent) :
    ∃ (d : Model E) (σ : E ≃+* E), d ∈ borel ∧ a = MulAut.conj d * fieldEquiv σ := by
  obtain ⟨z, rfl⟩ := hcover a
  refine ⟨z.left, z.right, ?_, rfl⟩
  rw [← normalizer_unipotent]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change unipotent.map ((MulAut.conj z.left).toMonoidHom.comp
    (fieldEquiv z.right).toMonoidHom) = unipotent at ha
  rwa [← map_map, field_map_unipotent] at ha
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source

open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem conjugate_pSubgroup_into (H B : Subgroup G)
    (hH : ¬ p ∣ H.index) (hB : IsPGroup p B) :
    ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := H)
  have hm : ¬ p ∣ ((P : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hH
  let Q : Sylow p G := (P.isPGroup'.map H.subtype).toSylow hm
  obtain ⟨R, hR⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R Q
  refine ⟨g, ?_⟩
  have hmap : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup hg
  exact (map_mono hR).trans (hmap ▸ map_subtype_le (P : Subgroup H))

variable {E : Type*} [Field E] [Finite E] [CharP E 2]

omit [CharP E 2] in
theorem torus_index_in_borel :
    ((splitTorus (K := E)).subgroupOf borel).index = Nat.card E ^ 6 := by
  have hc := ((splitTorus (K := E)).subgroupOf borel).card_mul_index
  have ht : Nat.card ((splitTorus (K := E)).subgroupOf borel) = Nat.card (splitTorus (K := E)) :=
    Nat.card_congr (subgroupOfEquivOfLe (show splitTorus (K := E) ≤ borel from le_sup_right)).toEquiv
  rw [ht, card_splitTorus, card_borel] at hc
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.sub_pos_of_lt Finite.one_lt_card) 2)
    (hc.trans (Nat.mul_comm _ _))

theorem conjugate_borel_pSubgroup_into_torus (B : Subgroup (Model E))
    (hB : IsPGroup p B) (hp : p ≠ 2) (hBb : B ≤ borel) :
    ∃ g ∈ borel (K := E), B.map (MulAut.conj g).toMonoidHom ≤ splitTorus := by
  have hnot : ¬ p ∣ 2 := by
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  have hind : ¬ p ∣ ((splitTorus (K := E)).subgroupOf borel).index := by
    rw [torus_index_in_borel]
    obtain ⟨n, _, hn⟩ := field_card (F := E)
    rw [hn]
    intro h
    exact hnot (Nat.Prime.dvd_of_dvd_pow Fact.out (Nat.Prime.dvd_of_dvd_pow Fact.out h))
  have hPB : IsPGroup p (B.subgroupOf borel) :=
    hB.of_injective (subgroupOfEquivOfLe hBb).toMonoidHom (subgroupOfEquivOfLe hBb).injective
  obtain ⟨g, hg⟩ := conjugate_pSubgroup_into (splitTorus.subgroupOf borel)
    (B.subgroupOf borel) hind hPB
  refine ⟨g, g.property, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show (⟨b, hBb hb⟩ : borel (K := E)) ∈ B.subgroupOf borel from hb))
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
