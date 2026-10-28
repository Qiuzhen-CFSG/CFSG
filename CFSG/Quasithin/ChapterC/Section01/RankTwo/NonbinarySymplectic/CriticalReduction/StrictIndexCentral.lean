module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexTerminal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Action

/-!
# The whole strict-index commutator lies in the fixed core

An actor in Q_alpha fixing Z_alpha' intersect Q_alpha has endpoint
displacement in the critical commutator. If this failed, the large-image
exclusion and reciprocal index comparison would make the critical image
a full root; the existing fixed-root calculation then contradicts failure.
This applies at the original nonbinary degree with the complete cover.

Apply this to the literal orbit span from StrictIndexTerminal. Joining it
with Z_alpha gives a subgroup normalized by the selected centralizer and
by Z_alpha', hence by their generated vertex stabilizer. The simple
quotient action puts that normal radius subgroup in B_alpha. Its original
seed is then entirely in B_alpha, so the defining centralizer T₀ fixes
that seed and H is trivial, contradicting the selected moving element.
Thus the noncentral-H alternative is excluded and the full H lies in
D_alpha = C_Qalpha(Ltilde_alpha).

This closes the first branch of (5.9). The central-H branch, strict moving
index, later terminal exclusions and distance-two replacement still remain.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and (5.9), printed pp.866--867 and920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison

/-- The source fixed-intersection displacement bound, with both large and root critical-image alternatives discharged. -/
theorem Input.replacement_critical_fixed_intersection_displacement
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYZ : Y ≤ stabilizer d.radical z) (hYQ : Y ≤ Q d.radical a)
    (hfix : Y ≤ centralizer ((Z d.radical z ⊓ Q d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical z,Y⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
  by_contra hbad
  have hcentral : Y ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)))).trans
      (centralizer_le (critical_commutator_le_start_seed path))
  obtain ⟨hz,ha⟩ := h.replacement_small_critical_indices_eq_field d path hb
    (h.replacement_critical_index_lt_square_of_escape d path hb Y hYZ hcentral hbad)
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAut : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card E.Carrier := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE]),E.card_eq,hE]
    exact n.lt_two_pow_self
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (hz.trans hFc.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hcent := (h.replacement_component_image_structure d).2.2.2.2
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor_of_field path hb hCa hFl
    s e he hcent j hj hjr δ hδ hδcard (ha.trans hFc.symm) hAut
  exact hbad (critical_seed_displacement_le_of_fixed_intersection path hb hCa hFl
    s e he hcent j hj hjr κ hκC hconj β hAZ hβmark hβ hd hβcard Y hYZ hfix)


/-- The noncentral-H countercase is impossible on the actual two-step path. -/
theorem Input.replacement_strict_index_kernel_central
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    kernelCommutator geometry a (path.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  by_contra hD
  obtain ⟨_,_,_,g,hg,x,hx,hat,hct,hT,hmap,hZW,hWV,hQC,hCN,hgen,
      _,_,hxW,hm,_,hWQ,hzero,_⟩ :=
    h.replacement_strict_index_noncentral_terminal d path hb hsmall hD
  let c := act d.radical g⁻¹ (path.walk.getVert 2)
  let x₁ := g*x*g⁻¹
  let C₀ := stabilizer d.radical a ⊓ centralizer ({x₁} : Set (FreeAmalgam d.radical))
  let W := conjugateSpanBy (Z d.radical c) C₀
  let J := W ⊔ Z d.radical a
  have hWz : W ≤ stabilizer d.radical z :=
    (le_inf hWV hWQ).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hWQa : W ≤ Q d.radical a := hWV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hWS : W ≤ stabilizer d.radical a := hWQa.trans (fun _ hv => hv.1)
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hWfix : W ≤ centralizer ((Z d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (commutator_eq_bot_iff_le_centralizer.mp hzero).trans (centralizer_le (fun _ hv => mem_sup_right hv))
  have hWend : ⁅W,Z d.radical z⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact (h.replacement_critical_fixed_intersection_displacement d path (by omega)
      W hWz hWQa hWfix).trans (critical_commutator_le_start_seed path)
  have hJC : C₀ ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf hCN (inf_le_left.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJz : Z d.radical z ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    normalizes_sup_of_displacement _ _ _ (hzS.trans (Z_normalized d.radical a)) hWend
  have hJn : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hJC hJz
  have hJV : J ≤ V d.radical a := sup_le hWV (Z_le_VBall d.radical a 2)
  have hJend : ⁅J,Z d.radical z⁆ ≤ Z d.radical a :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) W (Z d.radical a)
      (Z d.radical z) (Z d.radical a) (Z_normalized d.radical a) hWS
      (Z_le_stabilizer d.radical a) hWend
      (le_normalizer_iff_commutator_le_left.mp (hzS.trans (Z_normalized d.radical a)))
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    apply map_injective (stabilizer d.radical a).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1)]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hzQ := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
    z path.end_color path.critical).2
  have hJB := normal_radius_le_B_of_kernel_escape geometry (by omega) path.start_color f hf hk
    (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a path.start_color)
    J (Z d.radical z) hJV hJn hzS hzQ hJend
  have hUB : U d.radical c ≤ B d.radical a (geometry.Z_normal a) :=
    (U_le_Z c).trans (hZW.trans (le_sup_left.trans hJB))
  have hHbot : kernelCommutator geometry a c=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    change Q d.radical a ⊓ centralizer ((U d.radical c ⊓ B d.radical a (geometry.Z_normal a) : Subgroup _) : Set _) ≤ _
    rw [inf_eq_left.mpr hUB]
    exact inf_le_right
  have hxH : x₁ ∈ kernelCommutator geometry a c := by
    rw [←hmap]
    exact ⟨x,hx,rfl⟩
  have hxone : x₁=1 := mem_bot.mp (hHbot ▸ hxH)
  apply hm
  change x₁ ∈ _
  rw [hxone]
  exact one_mem _

/-- The complete literal H lies in the source fixed core D_alpha. -/
theorem Input.replacement_strict_index_kernel_le_fixedCore
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    kernelCommutator geometry a (path.walk.getVert 2) ≤ fixedCore d.radical a := by
  have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hHV := (h.replacement_field_index_kernel_commutator_le_edge_seed d geometry hb.le
    path.start_color hat hct hsmall).trans
      ((adjacent_Z_le d.radical path.start_color hat).trans (Z_le_VBall d.radical a 2))
  exact le_inf (hHV.trans (geometry.V_le_Q (by omega) a path.start_color))
    ((h.replacement_strict_index_kernel_central d path hb hsmall).trans
      (centralizer_le (Ltilde_le_stabilizer a)))


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
