module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Reduction

/-!
# Exact reductions for the MS93 displacement cardinalities

The displacement [Z_c, V_alpha] lies in Z_alpha and in the known edge
four-group [Z_c, Q_beta]. The index-two inclusion Z_beta ≤ Z_c makes
commutation by every x outside Z_beta have this same image. Its commutator
homomorphism has kernel the centralizer of Z_c in V_alpha, which the source
centralizer equality identifies with V_alpha intersected with Q_c. This
proves the exact relative-index formula without assuming any displacement
cardinality or finiteness of the free amalgam.

The flag triple bound also normalizes [A, V_alpha](Z_alpha ∩ Z(G_alpha))
for every A in V_beta. We apply it both to Z_c and to its cyclic sublayers.
The remaining order-four and disjointness calculation requires the marked
natural representation, and is not asserted by these reductions.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the first paragraph of (4.6.9), printed p.908. The central commutator
homomorphism follows the argument in `Theory.GroupTheory.CentralIndexTwoCommutatorSupplement`,
without imposing finiteness on the ambient group.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

/-- The two actor cosets have the same displacement image, and the kernel
of commutation by an outside element is the full actor centralizer. -/
private theorem index_two_displacement {G : Type*} [Group G]
    (V A C : Subgroup G)
    (hcentral : C ≤ centralizer (V : Set G))
    (hindex : C.relIndex A = 2)
    (hcommV : ⁅V, A⁆ ≤ V)
    (hcomm : ⁅V, A⁆ ≤ centralizer (V : Set G))
    (x : G) (hx : x ∈ A) (hxC : x ∉ C) :
    ⁅zpowers x, V⁆ = ⁅A, V⁆ ∧
    (centralizer (A : Set G)).relIndex V = Nat.card (⁅A, V⁆ : Subgroup G) := by
  have hvalue (v : G) (hv : v ∈ V) : ⁅v, x⁆ ∈ ⁅V, A⁆ :=
    commutator_mem_commutator hv hx
  let f : V →* G := {
    toFun := fun v => ⁅(v : G), x⁆
    map_one' := by simp
    map_mul' := by
      intro v w
      change ⁅(v : G) * (w : G), x⁆ = ⁅(v : G), x⁆ * ⁅(w : G), x⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hvw : (v : G) * ⁅(w : G), x⁆ = ⁅(w : G), x⁆ * v :=
        hcomm (hvalue w w.property) v v.property
      have hcc : ⁅(w : G), x⁆ * ⁅(v : G), x⁆ =
          ⁅(v : G), x⁆ * ⁅(w : G), x⁆ :=
        hcomm (hvalue v v.property) _ (hcommV (hvalue w w.property))
      rw [hvw, mul_inv_cancel_right, hcc] }
  have hsame (v : G) (hv : v ∈ V) (a : G) (ha : a ∈ A) (haC : a ∉ C) :
      ⁅v, a⁆ = ⁅v, x⁆ := by
    have hfactor : x⁻¹ * a ∈ C :=
      (C.subgroupOf A).mul_mem_iff_of_index_two hindex
        (a := ⟨x⁻¹, A.inv_mem hx⟩) (b := ⟨a, ha⟩) |>.mpr (by
          simp only [mem_subgroupOf, inv_mem_iff, hxC, haC])
    have hzero : ⁅v, x⁻¹ * a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcentral hfactor v hv)
    have hh := commutatorElement_mul_right_eq_mul_conj v x (x⁻¹ * a)
    simpa only [mul_inv_cancel_left, hzero, mul_one, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hrange : f.range = ⁅V, A⁆ := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hvalue v v.property
    · apply commutator_le.mpr
      intro v hv a ha
      by_cases haC : a ∈ C
      · have hone : ⁅v, a⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hcentral haC v hv)
        rw [hone]
        exact f.range.one_mem
      exact ⟨⟨v, hv⟩, (hsame v hv a ha haC).symm⟩
  constructor
  · rw [commutator_comm (zpowers x), commutator_comm A]
    apply le_antisymm (commutator_mono le_rfl (zpowers_le.mpr hx))
    rw [← hrange]
    rintro _ ⟨v, rfl⟩
    exact commutator_mem_commutator v.property (mem_zpowers x)
  · have hker : f.ker = (centralizer (A : Set G)).subgroupOf V := by
      ext v
      change ⁅(v : G), x⁆ = 1 ↔ (v : G) ∈ centralizer (A : Set G)
      constructor
      · intro hv a ha
        apply Eq.symm
        apply commutatorElement_eq_one_iff_mul_comm.mp
        by_cases haC : a ∈ C
        · exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hcentral haC v v.property)
        · exact (hsame v v.property a ha haC).trans hv
      · intro hv
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hv x hx).symm
    change ((centralizer (A : Set G)).subgroupOf V).index = _
    rw [← hker, index_ker, hrange, commutator_comm V]

variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem edge_generator_color {c : Vertex R} (hbc : Adjacent R (beta R) c) :
    color R c = false := by
  have hh := adjacent_color_ne R hbc
  have hb : color R (beta R) = true := rfl
  cases he : color R c <;> simp_all

/-- The displacement is bounded by the known four-group at the far end of the edge. -/
theorem displacement_le_edge [Finite M] (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (c : Vertex R) :
    ⁅Z R c, V R (alpha R)⁆ ≤ ⁅Z R c, Q R (beta R)⁆ :=
  commutator_mono le_rfl ((V_le_Q geometry hlarge _ rfl).trans
    (Q_le_adjacent_h R rfl (base_adjacent R)))

/-- The edge four-group bounds the displacement before the natural-action calculation. -/
theorem displacement_card_le_four [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (c : Vertex R) (hbc : Adjacent R (beta R) c) :
    Nat.card (⁅Z R c, V R (alpha R)⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  have he := early.edge_commutator_card c (beta R) (edge_generator_color hbc)
    (adjacent_symm R hbc)
  let : Finite (⁅Z R c, Q R (beta R)⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [he]; decide)
  exact (card_le_of_le (displacement_le_edge geometry hlarge c)).trans_eq he

/-- The literal centralizer kernel and all nonidentity edge cosets give the same displacement. -/
theorem cyclic_displacement_and_kernel_index [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (c : Vertex R)
    (hac : (cosetGraph R).dist (alpha R) c = 2)
    (hbc : Adjacent R (beta R) c)
    (x : FreeAmalgam R) (hx : x ∈ Z R c) (hxout : x ∉ Z R (beta R)) :
    ⁅zpowers x, V R (alpha R)⁆ = ⁅Z R c, V R (alpha R)⁆ ∧
    (Q R c).relIndex (V R (alpha R)) =
      Nat.card (⁅Z R c, V R (alpha R)⁆ : Subgroup (FreeAmalgam R)) := by
  have hc := edge_generator_color hbc
  have hVQ := V_le_Q geometry common.large_distance (alpha R) rfl
  have hZcV : Z R c ≤ V R (alpha R) :=
    le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hac]) le_rfl)
  have hcentral : Z R (beta R) ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) :=
    ((edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ rfl))).trans
      (centralizer_le hVQ)
  have hcomm : ⁅V R (alpha R), Z R c⁆ ≤
      (center (V R (alpha R))).map (V R (alpha R)).subtype :=
    (commutator_mono le_rfl (hZcV.trans hVQ)).trans (early.commutator_central _ rfl)
  have hCV : (center (V R (alpha R))).map (V R (alpha R)).subtype ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    rintro z ⟨z, hz, rfl⟩ v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v, hv⟩)
  obtain ⟨hcyclic, hindex⟩ := index_two_displacement (V R (alpha R)) (Z R c)
    (Z R (beta R)) hcentral
    (early.edge_Z_index c (beta R) hc (adjacent_symm R hbc))
    (hcomm.trans (map_subtype_le _)) (hcomm.trans hCV) x hx hxout
  refine ⟨hcyclic, ?_⟩
  have hkernel : (Q R c).subgroupOf (V R (alpha R)) =
      (centralizer (Z R c : Set (FreeAmalgam R))).subgroupOf (V R (alpha R)) := by
    rw [← common.centralizer c (beta R) hc (adjacent_symm R hbc)]
    ext v
    exact and_iff_right ((hVQ.trans (Q_le_adjacent_h R rfl (base_adjacent R))) v.property)
  change ((Q R c).subgroupOf (V R (alpha R))).index = _
  rw [hkernel]
  exact hindex

/-- Normalization modulo the literal central denominator is inherited by displacement. -/
theorem flag_normalizes_displacement_sup_denominator [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ V R (beta R)) :
    flagResidual source i ≤ normalizer
      ((⁅A, V R (alpha R)⁆ ⊔ (centralDenominator (alpha R)).map
        (stabilizer R (alpha R)).subtype : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let V₀ := V R (alpha R)
  let N := (centralDenominator (alpha R)).map (stabilizer R (alpha R)).subtype
  let D := ⁅A, V₀⁆
  let K := D ⊔ N
  have hV := geometry.V_local (alpha R) rfl hlarge
  have hAV : A ≤ V₀ := hA.trans (edgeRadius_le_radius _ _ rfl (base_adjacent R))
  have hNC : N ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
    rw [show N = (centralDenominator (alpha R)).map
      (stabilizer R (alpha R)).subtype from rfl, centralDenominator_map]
    rintro z ⟨_, z, hz, rfl⟩ v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v, hv⟩)
  have hNV : N ≤ centralizer (V₀ : Set (FreeAmalgam R)) :=
    hNC.trans (centralizer_le hV)
  have hNK : V₀ ≤ normalizer (K : Set (FreeAmalgam R)) := by
    intro v hv
    rw [mem_normalizer_iff_map_conj_eq]
    change (D ⊔ N).map (MulAut.conj v).toMonoidHom = D ⊔ N
    have hDm := mem_normalizer_iff_map_conj_eq.mp
      (normalizer_commutator_ge_right A V₀ hv)
    have hNm := mem_normalizer_iff_map_conj_eq.mp
      ((le_centralizer_iff.mp hNV).trans (Subgroup.centralizer_le_normalizer _) hv)
    change D.map (MulAut.conj v).toMonoidHom = D at hDm
    change N.map (MulAut.conj v).toMonoidHom = N at hNm
    rw [Subgroup.map_sup, hDm, hNm]
  have hBK : ⁅Bzero geometry (alpha R), V₀⁆ ≤ K := by
    have hh := ((le_Bzero_iff geometry (alpha R) hV _).mp le_rfl).2
    rw [← centralDenominator_map] at hh
    exact hh.trans le_sup_right
  have hsup : A ⊔ Bzero geometry (alpha R) ≤ commutatorPreimage V₀ V₀ K :=
    sup_le (le_commutatorPreimage hAV le_sup_left)
      (le_commutatorPreimage (Bzero_le_radius geometry _) hBK)
  have hbound : ⁅A ⊔ Bzero geometry (alpha R), V₀⁆ ≤ K :=
    (commutator_mono hsup le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hNK)
  have hnorm := flag_normalizes_sup_Bzero source geometry hlarge early i hkernel htriple A hA
  apply le_normalizer_iff.mpr
  intro g hg z hz
  have hm : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    change (D ⊔ N).map (MulAut.conj g).toMonoidHom ≤ D ⊔ N
    rw [Subgroup.map_sup]
    apply sup_le
    · change (⁅A, V₀⁆).map (MulAut.conj g).toMonoidHom ≤ K
      rw [map_commutator]
      have hgG := (flagResidual_le source i).trans (flagParabolic_le source i) hg
      have hVm := mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized R _ hgG)
      change (V₀.map (MulAut.conj g).toMonoidHom) = V₀ at hVm
      rw [hVm]
      apply le_trans (commutator_mono ?_ le_rfl) hbound
      exact (map_mono (show A ≤ A ⊔ Bzero geometry (alpha R) from le_sup_left)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (hnorm hg))
    · rintro _ ⟨n, hn, rfl⟩
      have hgG := (flagResidual_le source i).trans (flagParabolic_le source i) hg
      have he : (MulAut.conj g) n = n := by
        change g * n * g⁻¹ = n
        rw [hNC hn g hgG, mul_inv_cancel_right]
      exact mem_sup_right (by change (MulAut.conj g) n ∈ N; rwa [he])
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hz)

/-- All displacements lie in the original Z-layer, before its derived equality is known. -/
theorem displacement_le_Z [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (c : Vertex R) (hac : (cosetGraph R).dist (alpha R) c = 2) :
    ⁅Z R c, V R (alpha R)⁆ ≤ Z R (alpha R) := by
  have hZcV : Z R c ≤ V R (alpha R) :=
    le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hac]) le_rfl)
  exact (commutator_mono hZcV (V_le_Q geometry hlarge _ rfl)).trans
    (early.commutator_le_Z _ rfl)

/-- The centralizer kernel gives the exact index even before the order-four argument. -/
theorem displacement_index_eq_card [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (c : Vertex R)
    (hac : (cosetGraph R).dist (alpha R) c = 2)
    (hbc : Adjacent R (beta R) c) :
    (Q R c).relIndex (V R (alpha R)) =
      Nat.card (⁅Z R c, V R (alpha R)⁆ : Subgroup (FreeAmalgam R)) := by
  have hnot : ¬ Z R c ≤ Z R (beta R) := by
    intro hle
    have hone := relIndex_eq_one.mpr hle
    rw [early.edge_Z_index c (beta R) (edge_generator_color hbc)
      (adjacent_symm R hbc)] at hone
    omega
  obtain ⟨x, hx, hxout⟩ := SetLike.not_le_iff_exists.mp hnot
  exact (cyclic_displacement_and_kernel_index source geometry common early c hac hbc
    x hx hxout).2

/-- Both applications of source normalization, to the full edge layer and each cyclic layer. -/
theorem flag_normalizes_full_and_cyclic_displacement [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (c : Vertex R) (hbc : Adjacent R (beta R) c) :
    flagResidual source i ≤ normalizer
      ((⁅Z R c, V R (alpha R)⁆ ⊔ (centralDenominator (alpha R)).map
        (stabilizer R (alpha R)).subtype : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
    ∀ x ∈ Z R c, flagResidual source i ≤ normalizer
      ((⁅zpowers x, V R (alpha R)⁆ ⊔ (centralDenominator (alpha R)).map
        (stabilizer R (alpha R)).subtype : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hZc : Z R c ≤ V R (beta R) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le c (le_iSup_of_le hbc le_rfl)
  exact ⟨flag_normalizes_displacement_sup_denominator source geometry hlarge early i
    hkernel htriple (Z R c) hZc,
    fun x hx => flag_normalizes_displacement_sup_denominator source geometry hlarge early i
      hkernel htriple (zpowers x) ((zpowers_le.mpr hx).trans hZc)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
