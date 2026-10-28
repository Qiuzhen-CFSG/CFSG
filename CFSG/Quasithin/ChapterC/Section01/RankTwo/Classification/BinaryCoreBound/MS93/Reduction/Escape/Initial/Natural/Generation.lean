module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# Moving generation from the full natural section

For vertices a,d at distance two, the conjugates of Z_d under G_a contain
Z_a: the common edge supplies one omega-center and local transitivity
supplies all its conjugates. This is a statement inside the actual amalgam.

A normal subgroup containing the kernel of a natural factor is either the
kernel or the entire factor. Applying this to D[J,L], where D=N[H,Q], and
using the triple commutator and p-perfect commutator idempotence shows that
any normal J containing N which is not fixed modulo N contains [H,L].
Thus (4.3.1)(iii), with its actual natural coordinates, implies all of (iv).
No natural-section existence theorem is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iv), pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

/-- Every subgroup occurs as the identity conjugate in its local normal closure. -/
theorem conjugatesIn_contains {G : Type*} [Group G] (A K : Subgroup G) :
    A ≤ NormalizerTransfer.conjugatesIn A K := by
  have h := le_iSup (fun g : K => NormalizerTransfer.rightConjugate A g) 1
  intro x hx
  apply h
  exact ⟨x, hx, by simp⟩

/-- The common edge and local transitivity put Z_a in the local closure of Z_d. -/
theorem Z_le_conjugatesIn_of_dist_two (a d : Vertex R) (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) :
    Z R a ≤ NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R a) := by
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R a d hd
  have had : color R d = false := (color_eq_of_dist_even R d a (by
    rw [SimpleGraph.dist_comm, hd]; decide)).trans ha
  have htd : edgeOmega R t ≤ Z R d := by
    rw [Z, if_pos had]
    exact le_iSup_of_le t (le_iSup_of_le hdt le_rfl)
  rw [Z, if_pos ha]
  apply iSup_le
  intro u
  apply iSup_le
  intro hau
  obtain ⟨g, hg, hgu⟩ := stabilizer_transitive_neighbors R a hat hau
  rw [← hgu, edgeOmega_act]
  exact (map_mono htd).trans
    (le_iSup (fun k : stabilizer R a => NormalizerTransfer.rightConjugate (Z R d) k)
      ⟨g, hg⟩)

/-- Irreducibility with the intrinsic kernel retained, proved from natural coordinates. -/
theorem naturalFactor_dichotomy {A : Type*} [Group A] {π : A →* SL}
    {H N : Subgroup A} (n : RankOnePairing.NaturalFactor π ⊤ H N)
    (hπ : Function.Surjective π) (J : Subgroup A) [J.Normal]
    (hNJ : N ≤ J) (hJH : J ≤ H) : J = N ∨ J = H := by
  let K := (J.subgroupOf H).map n.coordinates
  let T : Subrepresentation BinaryLinearThree.W := {
    toSubmodule := {
      carrier := {v | Multiplicative.ofAdd v ∈ K}
      zero_mem' := K.one_mem
      add_mem' := fun hx hy => K.mul_mem hx hy
      smul_mem' := by
        intro c v hv
        fin_cases c
        · change Multiplicative.ofAdd ((0 : ZMod 2) • v) ∈ K
          rw [zero_smul]
          exact K.one_mem
        · change Multiplicative.ofAdd ((1 : ZMod 2) • v) ∈ K
          rw [one_smul]
          exact hv }
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨x, hx, he⟩ := hv
      obtain ⟨l, hl⟩ := hπ (n.marking.symm g)
      let y : H := ⟨l * (x : A) * l⁻¹,
        le_normalizer_iff.mp n.normalized l (mem_top _) x x.property⟩
      refine ⟨y, (inferInstance : J.Normal).conj_mem x hx l, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [n.action l (mem_top _) x y rfl, hl, n.marking.apply_symm_apply, he]
      rfl }
  let : Representation.IsIrreducible BinaryLinearThree.W :=
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  rcases eq_bot_or_eq_top T with hT | hT
  · left
    apply le_antisymm _ hNJ
    intro x hx
    let xH : H := ⟨x, hJH hx⟩
    have hc : (n.coordinates xH).toAdd ∈ T := ⟨xH, hx, rfl⟩
    rw [hT] at hc
    have hk : xH ∈ n.coordinates.ker := by
      exact Multiplicative.toAdd.injective hc
    rwa [n.kernel] at hk
  · right
    apply le_antisymm hJH
    intro x hx
    let xH : H := ⟨x, hx⟩
    have hc : (n.coordinates xH).toAdd ∈ T := by rw [hT]; trivial
    obtain ⟨y, hy, he⟩ := hc
    change n.coordinates y = n.coordinates xH at he
    have hk : xH * y⁻¹ ∈ n.coordinates.ker := by
      change n.coordinates (xH * y⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [n.kernel] at hk
    have hh := J.mul_mem (hNJ hk) hy
    change (x * (y : A)⁻¹) * (y : A) ∈ J at hh
    simpa only [inv_mul_cancel_right] using hh

private theorem commutator_sup_le {A : Type*} [Group A]
    {X Y L N : Subgroup A} [N.Normal]
    (hx : ⁅X, L⁆ ≤ N) (hy : ⁅Y, L⁆ ≤ N) : ⁅X ⊔ Y, L⁆ ≤ N := by
  have hh : X ⊔ Y ≤ commutatorPreimage ⊤ L N :=
    sup_le (le_commutatorPreimage le_top hx) (le_commutatorPreimage le_top hy)
  exact (commutator_mono hh le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ L N le_normalizer_of_normal)

/-- Lift a nonfixed normal subgroup across the radical of a single natural section. -/
theorem moving_le_of_normal_not_fixed {A : Type*} [Group A] [Finite A]
    {π : A →* SL} {Q L H N : Subgroup A} [L.Normal]
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H)
    (J : Subgroup A) [J.Normal] (hNJ : N ≤ J) (hJH : J ≤ H)
    (hne : letI := s.normal_kernel; ¬ J ≤ centralizerModulo H L N) :
    ⁅H, L⁆ ≤ J := by
  let := s.normal_group
  let := s.normal_kernel
  let := s.radical_normal
  let D := radicalPreimage Q H N
  let W := movingPreimage Q H N
  have hDW : D ≤ W := le_sup_left
  have hHW : ⁅H, L⁆ ≤ W := (commutator_mono le_rfl le_top).trans le_sup_right
  have hDL : ⁅D, L⁆ ≤ N :=
    commutator_sup_le (commutator_le_left _ _) s.triple_le
  have hfull : ⁅⁅H, L⁆, L⁆ = ⁅H, L⁆ :=
    commutator_isPPerfect_idempotent L H hL hH le_normalizer_of_normal
  have hfullJ : ⁅⁅J, L⁆, L⁆ = ⁅J, L⁆ :=
    commutator_isPPerfect_idempotent L J hL (hH.to_le hJH) le_normalizer_of_normal
  let K := D ⊔ ⁅J, L⁆
  have hKW : K ≤ W := sup_le hDW ((commutator_mono hJH le_rfl).trans hHW)
  rcases naturalFactor_dichotomy s.natural s.projection_surjective K le_sup_left hKW with he | he
  · exfalso
    apply hne
    have hED : ⁅J, L⁆ ≤ D := (show ⁅J, L⁆ ≤ K from le_sup_right).trans he.le
    have hEN : ⁅J, L⁆ ≤ N := by
      rw [← hfullJ]
      exact (commutator_mono hED le_rfl).trans hDL
    intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨hJH hx, fun l hl =>
      (commutator_comm J L ▸ hEN) (commutator_mem_commutator hl hx)⟩
  · have hHJ : ⁅H, L⁆ ≤ D ⊔ J := hHW.trans
      (he.symm.le.trans (sup_le_sup_left (commutator_le_left _ _) D))
    rw [← hfull]
    exact (commutator_mono hHJ le_rfl).trans
      (commutator_sup_le (hDL.trans hNJ) (commutator_le_left _ _))

/-- Source (4.3.1)(iv), conditional only on the preceding natural-section output. -/
theorem moving_generation_of_naturalSection {L : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a))
    (d : Vertex R) (hd : d ∈ movingNeighbors geometry a) :
    Vcirc R a ≤ NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R a) := by
  let S := stabilizer R a
  let J := NormalizerTransfer.conjugatesIn (Z R d) S
  have hZdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm]; exact hd.1.le) le_rfl)
  have hJV : J ≤ V R a := by
    apply iSup_le
    intro g
    exact (map_mono hZdV).trans
      (mem_normalizer_iff_map_conj_eq.mp ((V_normalized a) (S.inv_mem g.property))).le
  have hZJ : Z R a ≤ J := Z_le_conjugatesIn_of_dist_two a d ha hd.1
  let : Finite S := finite_stabilizer R a
  let : (J.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (NormalizerTransfer.conjugatesIn_normalized _ _)
  have hne : letI := s.module_section.normal_kernel
      ¬ J.subgroupOf S ≤ centralizerModulo ((V R a).subgroupOf S)
        (pResidual 2 S) ((Z R a).subgroupOf S) := by
    intro h
    apply hd.2
    intro z hz
    have hzJ : z ∈ J := conjugatesIn_contains (Z R d) S hz
    exact ⟨⟨z, s.local_group (hJV hzJ)⟩, h hzJ, rfl⟩
  have hnative := moving_le_of_normal_not_fixed s.module_section
    (isPPerfect_pResidual 2) ((source.V_isPGroup geometry hb a ha).comap_subtype)
    (J.subgroupOf S) (comap_mono hZJ) (comap_mono hJV) hne
  have hmap := map_mono (f := S.subtype) hnative
  rw [map_commutator, map_subgroupOf_eq_of_le s.local_group,
    map_subgroupOf_eq_of_le (hJV.trans s.local_group)] at hmap
  exact hmap

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
