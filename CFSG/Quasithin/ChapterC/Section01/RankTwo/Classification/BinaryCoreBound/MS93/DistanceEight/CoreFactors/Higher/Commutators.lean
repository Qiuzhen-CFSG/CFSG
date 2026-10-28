module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Layers
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The central orbit commutator in MS93 (4.5.4)(i)

The preceding (4.5.1)(i) identifies the commutator of the two radius-two
groups. Its value lies in H_a, which is central in G_a by (4.4). Thus local
conjugation fixes that commutator pointwise. The commutator preimage then
passes the same bound to the whole conjugate span; the identity conjugate
gives the reverse inclusion.

The earlier equality is an explicit source premise, produced independently
by the early-layer argument. No fixed-factor or core-center equality is used.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.896 and 898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

private theorem seed_le_span {G : Type*} [Group G] (A P : Subgroup G) :
    A ≤ conjugatesIn A P := by
  have h := le_iSup (fun g : P => rightConjugate A g) (1 : P)
  have he : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  simpa only [Subgroup.coe_one, rightConjugate, he, Subgroup.map_id,
    conjugatesIn] using h

private theorem central_subgroup_normalized {G : Type*} [Group G]
    {C P : Subgroup G} (hC : C ≤ (center P).map P.subtype) : P ≤ normalizer C := by
  apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
  rintro x hx y hy
  obtain ⟨z, hz, rfl⟩ := hC hx
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)

private theorem central_commutator_span {G : Type*} [Group G]
    (A B P : Subgroup G) (hA : P ≤ normalizer A) (hB : B ≤ P)
    (hC : ⁅A, B⁆ ≤ (center P).map P.subtype) :
    ⁅A, conjugatesIn B P⁆ = ⁅A, B⁆ := by
  have hn := central_subgroup_normalized hC
  apply le_antisymm
  · rw [commutator_comm]
    apply (commutator_mono (show conjugatesIn B P ≤
      commutatorPreimage P A ⁅A, B⁆ from ?_) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hn)
    apply iSup_le
    intro g
    apply le_commutatorPreimage
    · exact (map_mono hB).trans
        (mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer (P.inv_mem g.property))).le
    · have hAm := mem_normalizer_iff_map_conj_eq.mp (hA (P.inv_mem g.property))
      have hCm := mem_normalizer_iff_map_conj_eq.mp (hn (P.inv_mem g.property))
      change ⁅B.map (MulAut.conj (g : G)⁻¹).toMonoidHom, A⁆ ≤ ⁅A, B⁆
      rw [commutator_comm]
      simpa only [map_commutator, hAm, MulEquiv.toMonoidHom_eq_coe] using hCm.le
  · exact commutator_mono le_rfl (seed_le_span B P)

/-- MS93 (4.5.4)(i), from the literal preceding (4.5.1)(i).
The span is taken under the actual local stabilizer, with right conjugation. -/
theorem radius_orbit_commutator (earlier : Earlier R geometry)
    {a d : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (hda : (cosetGraph R).dist d a ≤ 4)
    (hcomm : ⁅V R a, V R d⁆ = H R a ⊓ H R d) :
    ⁅V R a, conjugatesIn (V R d) (stabilizer R a)⁆ = H R a ⊓ H R d := by
  have hlocal : V R d ≤ stabilizer R a :=
    (V_le_Q_of_dist_add_two_lt R hd (by rw [earlier.distance]; omega)).trans
      (fun _ hx => hx.1)
  have hcentral : ⁅V R a, V R d⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype := by
    rw [hcomm]
    exact inf_le_left.trans (H_le_localCenter_of_central R a (earlier.centrality a ha))
  exact (central_commutator_span _ _ _ (V_normalized R a) hlocal hcentral).trans hcomm

/-- The same calculation bounds the smaller Z-orbit used in (4.5.4)(ii). -/
theorem radius_Z_orbit_commutator_le (earlier : Earlier R geometry)
    {a d : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (hda : (cosetGraph R).dist d a ≤ 4)
    (hcomm : ⁅V R a, V R d⁆ = H R a ⊓ H R d) :
    ⁅V R a, conjugatesIn (Z R d) (stabilizer R a)⁆ ≤ H R a ⊓ H R d := by
  have hspan : conjugatesIn (Z R d) (stabilizer R a) ≤
      conjugatesIn (V R d) (stabilizer R a) :=
    iSup_mono fun _ => map_mono (Z_le_VBall R d 2)
  exact (commutator_mono le_rfl hspan).trans
    (radius_orbit_commutator earlier ha hd hda hcomm).le

private theorem span_le_of_normalized {G : Type*} [Group G]
    {A P N : Subgroup G} (hA : A ≤ N) (hN : P ≤ normalizer N) :
    conjugatesIn A P ≤ N := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hN (P.inv_mem g.property))).le

/-- The last paragraph of (4.5.5) reduces the derived-group bound to pairs
of conjugate generators. The premise is the local path calculation, not
the derived-group bound itself. -/
theorem hatSix_derived_le_of_conjugate_bounds
    {a c d e : Vertex R}
    (hlocal : hatW R c d e ≤ stabilizer R a)
    (hpairs : ∀ g : stabilizer R a,
      ⁅hatW R c d e, rightConjugate (hatW R c d e) g⁆ ≤ hatV R a c) :
    ⁅hatSix R a c d e, hatSix R a c d e⁆ ≤ hatV R a c := by
  let P := stabilizer R a
  let A := hatW R c d e
  let N := hatV R a c
  let S := hatSix R a c d e
  have hPN : P ≤ normalizer N := hatV_normalized R a c
  have hPS : P ≤ normalizer S := hatSix_normalized R a c d e
  have hAS : ⁅A, S⁆ ≤ N := by
    rw [commutator_comm]
    apply (commutator_mono (show S ≤ commutatorPreimage P A N from ?_) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hPN)
    apply iSup_le
    intro g
    apply le_commutatorPreimage
    · exact (map_mono hlocal).trans
        (mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer (P.inv_mem g.property))).le
    · simpa only [commutator_comm] using hpairs g
  have hAC : A ≤ commutatorPreimage P S N := le_commutatorPreimage hlocal hAS
  have hPC : P ≤ normalizer (commutatorPreimage P S N) :=
    commutatorPreimage_normalized P S N P hPN P.le_normalizer hPS hPN
  exact (commutator_mono (span_le_of_normalized hAC hPC) le_rfl).trans
    (commutator_commutatorPreimage_le P S N hPN)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
