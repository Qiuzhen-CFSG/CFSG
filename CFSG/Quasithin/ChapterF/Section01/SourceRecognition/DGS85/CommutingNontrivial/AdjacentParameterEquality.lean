module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathOmegaActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalitySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCatalogueSquare
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualSquareBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalBranch
public import Theory.SpecificGroups.SU3.SylowOmegaIndex
public import Theory.SpecificGroups.Suzuki.SylowOmegaIndex

/-!
# Equality of the adjacent parameters in DGS 8.7

Starting naturality implies the commuting-intersection condition of 8.6.
Choose a moving terminal neighbor. Its natural plane gives a lower bound
by its field order, while the commuting intersection bounds that index by
the full opposite actor. The path omega theorem identifies this actor's
order with the actual beta quotient-Sylow omega order.

The opposite centralizer product estimate and 8.5's residual nonnaturality
then give the reverse inequality. Linear, Suzuki and both unitary rows use
their proved residual square bounds; the small beta parameters follow from
the natural field's minimum order. The full path actor supplies the unitary
size premise even when the starting natural field has order two.

Conjugation transports the moving parameter back to alpha. Both final
Sylows are arbitrary original local Sylows, and every quotient map remains
the literal map modulo the vertex core.
Source: DGS, *Groups and Graphs* (1985), 8.6--8.7, printed pp.139--140.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem natural_center_not_dihedral
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    (v : Vertex (family P))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v)) :
    ¬ Nonempty ((d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5) := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := source_natural_center_linear_quotient h d v hnat
  rintro ⟨ed⟩
  have hc : Nat.card SL(2,F) = 10 := (Nat.card_congr e.toEquiv).symm.trans
    ((Nat.card_congr ed.toEquiv).trans (by rw [DihedralGroup.nat_card]))
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup] at hc
  have hp : 2 ≤ Nat.card F := Finite.one_lt_card
  have hs : 1 ≤ Nat.card F ^ 2 := by nlinarith
  have hsub := Nat.sub_add_cancel hs
  by_cases htwo : Nat.card F = 2
  · norm_num [htwo] at hc
  · have hthree : 3 ≤ Nat.card F := by omega
    nlinarith

private theorem natural_fixed_lower {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] (A : Subgroup SL(2,F)) (hne : A ≠ ⊥) :
    Nat.card F ≤ Nat.card ((Fin 2 → F) ⧸
      fixedSpace (SL2NaturalOffenders.NoStrong.natural (F := F)) A) := by
  exact SL2NaturalOffenders.marked_field_card_le_fixed_quotient (MulEquiv.refl SL(2,F))
    (SL2NaturalOffenders.NoStrong.natural (F := F))
    (LinearEquiv.refl (ZMod 2) (Fin 2 → F)) (fun _ _ => rfl) hne

private theorem natural_center_parameter_le_index
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    (v : Vertex (family P))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v))
    (A : Subgroup G) (hAL : A ≤ d.localGroup v) (hAQ : ¬ A ≤ Q (family P) v)
    (R : Sylow 2 (d.localGroup v)) :
    Nat.card (omegaCenterIn ((R : Subgroup (d.localGroup v)).map
      (QuotientGroup.mk' (pCore 2 (d.localGroup v))))) ≤
      (centralizer (A : Set G)).relIndex (Z (family P) v) := by
  let := finite_endpoints h
  obtain ⟨F,_,_,_,π,hπ,hker,⟨c⟩⟩ := hnat
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let : Finite (Z (family P) v) := Finite.of_injective (inclusion (Z_le_stabilizer _ _)) (inclusion_injective _)
  have hcore : (Q (family P) v).subgroupOf L = pCore 2 L := by
    rw [←localGroup_core_eq (family P) d v]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let e : (L ⧸ pCore 2 L) ≃* SL(2,F) :=
    (QuotientGroup.quotientMulEquivOfEq (hker.trans hcore).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hn : (A.subgroupOf L).map π ≠ ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [hker] at hh
    exact hAQ (fun x hx => hh (show (⟨x,hAL hx⟩ : L) ∈ A.subgroupOf L from hx))
  have hlo : Nat.card F ≤ Nat.card ((Fin 2 → F) ⧸
      fixedSpace (SL2NaturalOffenders.NoStrong.natural (F := F)) ((A.subgroupOf L).map π)) :=
    natural_fixed_lower _ hn
  have hup := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index
    (SL2NaturalOffenders.NoStrong.natural (F := F)) π c A
  exact (linear_marking_quotient_sylow_omega_card e R).le.trans (hlo.trans hup)

variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

/-- In the natural-start branch, the full opposite actor has the original
beta quotient omega-center order, including all unitary parameters. -/
theorem reduced_natural_start_opposite_omega_index
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ, IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a') (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a)) :
    ∃ R : Sylow 2 (graphLocalGroup Γ beta),
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn
        ((R : Subgroup (graphLocalGroup Γ beta)).map (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  obtain ⟨_,_,_,_,mid,ham,hdm,_,_⟩ := source_critical_geometry ht d hc hab hd hb hcomm
  change (graph Γ).dist beta mid + 1 = (graph Γ).dist beta a' at hdm
  change (graph Γ).Adj a' mid at ham
  have hdist : (graph Γ).dist beta a' = 2 := by omega
  have hbm : (graph Γ).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have hba : beta ≠ a' := by intro he; rw [he,SimpleGraph.dist_self] at hdist; omega
  have hat : a.type = mid.type :=
    (Bool.eq_not_of_ne hab.1).trans (Bool.eq_not_of_ne hbm.1.symm).symm
  have hnatmid := source_natural_center_of_type ht d hat hnat
  have hnd := natural_center_not_dihedral ht d mid hnatmid
  have hAQ : V Γ a' 1 ≤ Q Γ mid := V_le_Q_of_dist_add_lt_b Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) a' mid 1
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr ham]; omega) (d.kernel_sylow mid)
  have hAL : V Γ a' 1 ≤ d.localGroup beta := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) a' beta hb (by rw [SimpleGraph.dist_comm]; exact hd.le)
  let : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow a' (by omega)
  have hesc := reduced_reciprocal_escape h (Reduction.reduced_graph_core_obstruction h)
    models hc hab hd hb hcomm hne
  obtain ⟨R,hR⟩ := source_path_normalized_omega_image ht (Reduction.reduced_borel_core_sylow h)
    d hbm ham hba (models beta) (models mid) hnd (V Γ a' 1) hAL hAQ hesc
    (stabilizer_normalizes_V Γ a' 1)
  refine ⟨R,?_⟩
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex (d.localGroup beta)
    (Q Γ beta) (V Γ a' 1) (QuotientGroup.mk' (pCore 2 (d.localGroup beta)))
    (local_quotient_kernel Γ d beta (MulEquiv.refl _)) hAL
  rw [hR] at hi
  exact hi.symm

private theorem omega_card_equiv {D E : Type*} [Group D] [Finite D] [Group E]
    (e : D ≃* E) (T : Sylow 2 D) :
    Nat.card (omegaCenterIn (T : Subgroup D)) =
      Nat.card (omegaCenterIn (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup E)) := by
  change Nat.card (omegaCenterIn (T : Subgroup D)) =
    Nat.card (omegaCenterIn ((T : Subgroup D).map e.toMonoidHom))
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
  exact (card_map_of_injective (K := omegaCenterIn (T : Subgroup D))
    (f := e.toMonoidHom) e.injective).symm

/-- The adjacent parameters in DGS 8.7 agree in the natural-start branch.
Both are the omega orders of the literal original quotient Sylows. -/
theorem reduced_natural_start_adjacent_parameter_equality
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ, IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a') (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a))
    (Rα : Sylow 2 (graphLocalGroup Γ a)) (Rβ : Sylow 2 (graphLocalGroup Γ beta)) :
    Nat.card (omegaCenterIn ((Rα : Subgroup (graphLocalGroup Γ a)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ a))))) =
    Nat.card (omegaCenterIn ((Rβ : Subgroup (graphLocalGroup Γ beta)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : ∀ v : Vertex Γ, Finite (graphLocalGroup Γ v) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  have hinter := reduced_natural_start_intersection_commutes h
    (Reduction.reduced_graph_core_obstruction h) models hc hab hd hb hcomm hne hnat
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor Γ (fun v => (source_Z_Q_U ht v).1) beta a' hne
  have hodd : Odd ((graph Γ).dist a a') := by rw [hc.1,hb3]; decide
  have hna : a.type ≠ a'.type := (odd_dist_iff Γ ht.generate a a').mp hodd
  have hwa : w.val.type = a.type :=
    (Bool.eq_not_of_ne w.property.1.symm).trans (Bool.eq_not_of_ne hna).symm
  have hnatw := source_natural_center_of_type ht d hwa.symm hnat
  let R : Sylow 2 (graphLocalGroup Γ w.val) := default
  let T : Sylow 2 (graphLocalGroup Γ a') := default
  obtain ⟨U,hactor⟩ := reduced_natural_start_opposite_omega_index h models hc hab hd hb hcomm hne hnat
  let Rq := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ w.val)))
  let Tq := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ a')))
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  let qR := Nat.card (omegaCenterIn Rq.toSubgroup)
  let qβ := Nat.card (omegaCenterIn Uq.toSubgroup)
  change (Q Γ beta).relIndex (V Γ a' 1) = qβ at hactor
  let A := V Γ beta 1 ⊓ Q Γ a'
  let : IsElementaryAbelian 2 (V Γ beta 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) beta (by omega)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAL : A ≤ d.localGroup w.val := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.1
  have hAQ : ¬ A ≤ Q Γ w.val := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.2.2.1
  let : Finite (d.localGroup w.val) := inferInstanceAs (Finite (graphLocalGroup Γ w.val))
  let : Finite A := Finite.of_injective (inclusion hAL) (inclusion_injective _)
  have hidx2 : 2 ≤ (Q Γ w.val).relIndex A := by
    have h0 := ((Q Γ w.val).subgroupOf A).index_ne_zero_of_finite
    have h1 : (Q Γ w.val).relIndex A ≠ 1 := fun he => hAQ (relIndex_eq_one.mp he)
    change (Q Γ w.val).relIndex A ≠ 0 at h0
    omega
  have hR2 : 2 ≤ qR := hidx2.trans
    (source_elementary_core_index_le_omega ht d w.val (models w.val) A hAL R)
  have hRB : qR ≤ qβ := (natural_center_parameter_le_index ht d w.val hnatw A hAL hAQ R).trans
    ((source_commuting_intersection_fixed_index_le ht hb w hinter).trans_eq hactor)
  have hEQ : ¬ Z Γ w.val ≤ Q Γ beta := by
    intro hZ
    exact hm (bot_unique ((commutator_mono le_rfl
      (le_inf (Z_neighbor_le_V Γ w.property) hZ)).trans hinter.le))
  obtain ⟨_,_,_,_,_,_,hparameters⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hTU : Nat.card (omegaCenterIn Tq.toSubgroup) = qβ := hparameters Tq Uq
  have hup := source_opposite_centralizer_index_le_omega_product ht
    (Reduction.reduced_borel_core_sylow h) d models hc hab hd hb hcomm w hm R T
  change (centralizer (Z Γ w.val : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) ≤
    Nat.card (omegaCenterIn Tq.toSubgroup) * qR at hup
  rw [hTU] at hup
  have close (q : ℕ) (hq : qβ ≤ q)
      (hlo : q^2 ≤ (centralizer (Z Γ w.val : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1)) :
      qR = qβ := by
    have hh := hlo.trans hup
    nlinarith only [hh,hq,hRB,hR2]
  have hqeq : qR = qβ := by
    cases models beta with
    | linear n hn hi =>
      obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hi
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      let e := e₀.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
      have hqF : qβ = Nat.card F := linear_marking_quotient_sylow_omega_card e U
      by_cases hn1 : 1 < n
      · apply close (Nat.card F) hqF.le
        exact reduced_critical_nonnatural_residual_square h hc hab hd hb hcomm
          (Reduction.reduced_graph_core_obstruction h a beta hab) hn1 hF e (hactor.trans hqF)
          (Z Γ w.val) (Z_neighbor_le_V Γ w.property) hEQ
          (reduced_natural_residual_exclusion_of_catalogue h models hc hab hd hb hcomm hne hn hF e)
      · have he : n = 1 := by omega
        have hq2 : qβ = 2 := by simpa only [he,pow_one] using hqF.trans hF
        omega
    | suzuki m hi =>
      have hq : qβ = 2^(2*m+1) := (omega_card_equiv hi.some Uq).trans
        (suzukiSylow_omegaCenter_card_index m _).1
      exact close _ hq.le (reduced_critical_suzuki_residual_square h hc hab hd hb hcomm m hi.some
        (Z Γ w.val) (Z_neighbor_le_V Γ w.property) hEQ)
    | dihedral hi =>
      let S := Uq.mapSurjective (f := hi.some.toMonoidHom) hi.some.surjective
      have hS : Nat.card S = 2 := by
        rw [S.card_eq_multiplicity,DihedralGroup.nat_card]
        decide +kernel
      have hq : qβ ≤ 2 := ((omega_card_equiv hi.some Uq).le.trans
        (card_le_of_le (map_subtype_le _))).trans_eq hS
      omega
    | projective_unitary n hn hi =>
      obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
      have hq : qβ = 2^n := (omega_card_equiv e Uq).trans
        (HermitianForm.SylowOmegaIndex.projective J hn hK hconj _).1
      by_cases hn2 : 2 ≤ n
      · apply close (2^n) hq.le
        have hl : 4 ≤ (Q Γ beta).relIndex (V Γ a' 1) := by
          rw [hactor,hq]
          exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn2
        exact reduced_critical_unitary_residual_square h hc hab hd hb hcomm hn2
          (Or.inl ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨e⟩⟩) hl
          (Z Γ w.val) (Z_neighbor_le_V Γ w.property) hEQ
      · have he : n = 1 := by omega
        norm_num only [he,pow_one] at hq
        omega
    | special_unitary n hn hi =>
      obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
      have hq : qβ = 2^n := (omega_card_equiv e Uq).trans
        (HermitianForm.SylowOmegaIndex.special J hn hK hconj _).1
      by_cases hn2 : 2 ≤ n
      · apply close (2^n) hq.le
        have hl : 4 ≤ (Q Γ beta).relIndex (V Γ a' 1) := by
          rw [hactor,hq]
          exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn2
        exact reduced_critical_unitary_residual_square h hc hab hd hb hcomm hn2
          (Or.inr ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨e⟩⟩) hl
          (Z Γ w.val) (Z_neighbor_le_V Γ w.property) hEQ
      · have he : n = 1 := by omega
        norm_num only [he,pow_one] at hq
        omega
  let Rαq := Rα.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ a)))
  let Rβq := Rβ.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ a w.val).mpr hwa.symm
  obtain ⟨_,_,_,_,hα⟩ := local_quotient_parameter_transport ht g hg
  obtain ⟨_,_,_,_,hβ⟩ := local_quotient_parameter_transport ht (1 : Reduction.G₀ L S₀)
    (show (1 : Reduction.G₀ L S₀) • beta = beta from one_smul _ beta)
  exact (hα Rαq Rq).trans
    (hqeq.trans (hβ Uq Rβq))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
