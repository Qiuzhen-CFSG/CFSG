module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSNaturalCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionGeometry

/-!
# The literal reciprocal span on the original quintic critical path

The constructed critical three-path produces an actual conjugator in X.
Its quintic span lies in the full middle core but escapes the full original
quintic core.  The two spans contain the original four-plane, and their
intersection is normalized by the original whole Sylow subgroup.
No supplied path, conjugated indices, or Suzuki parameter is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open CommutingNontrivial
open CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conjugate_subtype (J : Subgroup G) (W : Subgroup J) (g : J) :
    (W.map (MulAut.conj g).toMonoidHom).map J.subtype =
      (W.map J.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

/-- A conjugate span on the actual critical path retains both full cores,
the original plane and normalization by the whole original Sylow. -/
theorem source_quintic_critical_span_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let UH := conjugateSpanBy (localModule T M) H
    ∃ g ∈ X,
      let Ustar := UH.map (MulAut.conj g).toMonoidHom
      Ustar ≤ X.pCoreIn 2 ∧ ¬ Ustar ≤ H.pCoreIn 2 ∧
        localModule T M ≤ UH ⊓ Ustar ∧
        (T : Subgroup G) ≤ normalizer (UH ⊓ Ustar : Set G) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  let m := base F true
  let UH := conjugateSpanBy (localModule T M) H
  obtain ⟨hF,_,_,_,_,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  have hQymap : (Q F y).map J.subtype = H.pCoreIn 2 := (hmaps false).2
  have hQmmap : (Q F m).map J.subtype = X.pCoreIn 2 := (hmaps true).2
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple hF)
  have hZ := fun v => (source_Z_Q_U (Reduction.reduced_triple hF) v).1
  have hQU := fun v => (source_Z_Q_U (Reduction.reduced_triple hF) v).2
  have hb : 2 < b F := by
    have hh := (source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi).1
    change b F = 3 at hh
    omega
  obtain ⟨a,x,_,_,hax,hxm,_,_,hc,_,_,_⟩ :=
    source_quintic_dgs_critical_path hG T hempty hM hu hmany hcard e H hH hi
  change (graph F).Adj a x at hax
  change (graph F).Adj x m at hxm
  change IsCriticalPair F a y at hc
  have hmy : (graph F).Adj m y :=
    ⟨by change (true : Bool) ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩
  obtain ⟨g,hgm,hgy⟩ := locally_transitive F hmy hxm.symm
  have hgX : (g : G) ∈ X := by
    apply (hmaps true).1.le
    apply mem_map_of_mem J.subtype
    have hh : g ∈ stabilizer F (base F true) := hgm
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hh
  obtain ⟨_,hspan,_⟩ := source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi
  change (V F y 1).map J.subtype = UH at hspan
  let Ustar := UH.map (MulAut.conj (g : G)).toMonoidHom
  have hUx : (V F x 1).map J.subtype = Ustar := by
    rw [←hgy,V_translate,map_conjugate_subtype,hspan]
  have hUQ : Ustar ≤ X.pCoreIn 2 := by
    rw [←hUx,←hQmmap]
    exact map_mono (V_le_neighbor_Q F (Reduction.reduced_triple hF).generate hZ
      (Reduction.reduced_kernel_sylow hF) hb hxm)
  have hUne : ¬ Ustar ≤ H.pCoreIn 2 := by
    intro hh
    have hxQ : V F x 1 ≤ Q F y := by
      apply (map_le_map_iff_of_injective J.subtype_injective).mp
      rw [hUx,hQymap]
      exact hh
    have hZa : Z F a ≤ V F x 1 :=
      le_iSup_of_le a (le_iSup_of_le ((mem_ball_one F x a).mpr (Or.inl hax.symm)) le_rfl)
    exact hc.2 (hZa.trans (hxQ.trans (hQU y)))
  obtain ⟨hZy,hZm⟩ := source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi
  change (Z F y).map J.subtype = centralInvolutions T at hZy
  change (Z F m).map J.subtype = localModule T M at hZm
  have hmI : Z F m ≤ V F y 1 ⊓ V F x 1 := le_inf
    (le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F y m).mpr (Or.inl hmy.symm)) le_rfl))
    (le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F x m).mpr (Or.inl hxm)) le_rfl))
  have hIMap : (V F y 1 ⊓ V F x 1).map J.subtype = UH ⊓ Ustar := by
    rw [map_inf _ _ _ J.subtype_injective,hspan,hUx]
  have hVI : localModule T M ≤ UH ⊓ Ustar := by
    rw [←hZm,←hIMap]
    exact map_mono hmI
  have hzy : Z F y ≤ Z F m := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hZy,hZm]
    exact le_conjugateSpanBy _ _
  have hcomm : ⁅V F y 1,Q F y⁆ ≤ Z F y := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,hspan,hQymap,hZy]
    exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2.le
  have hQyN : Q F y ≤ normalizer (V F y 1 ⊓ V F x 1 : Set J) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono inf_le_left le_rfl).trans hcomm).trans (hzy.trans hmI))
  have hQmN : Q F m ≤ normalizer (V F y 1 ⊓ V F x 1 : Set J) :=
    (le_inf (((hQU m).trans ((ballKernel_one_le_edge F hmy).trans inf_le_right)).trans
      (CommutingNontrivial.stabilizer_normalizes_V F y 1))
      (((hQU m).trans ((ballKernel_one_le_edge F hxm.symm).trans inf_le_right)).trans
        (CommutingNontrivial.stabilizer_normalizes_V F x 1))).trans inf_normalizer_le_normalizer_inf
  have hTmap : (Q F y ⊔ Q F m).map J.subtype = (T : Subgroup G) := by
    rw [Subgroup.map_sup,hQymap,hQmmap]
    exact (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).1
  have hTN := (map_mono (f := J.subtype) (sup_le hQyN hQmN)).trans
    ((V F y 1 ⊓ V F x 1).le_normalizer_map J.subtype)
  rw [hTmap,hIMap] at hTN
  exact ⟨g,hgX,hUQ,hUne,hVI,hTN⟩

end CFSG.Quasithin.Chapter14.Section06
