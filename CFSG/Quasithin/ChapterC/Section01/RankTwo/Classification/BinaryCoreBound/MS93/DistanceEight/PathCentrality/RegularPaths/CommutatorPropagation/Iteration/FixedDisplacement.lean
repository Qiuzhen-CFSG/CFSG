module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Six
public import Theory.GroupTheory.CommutatorPreimage

/-!
# A proper natural displacement bound forces centralization

If a subgroup of Q_c displaces V_c only into a proper subgroup of U_c,
(4.4.1)(ii) forces the displacement into D_c. Otherwise it would cover Z_c
modulo D_c, contradicting the proper natural bound and the disjointness of
U_c from D_c. Their trivial intersection then kills the displacement.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(ii) applied in the
last paragraph of (4.4.4), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

private theorem not_Z_le_proper_natural_sup_fixed [Finite M]
    (common : CommonFacts R source geometry) {c : Vertex R} (hc : color R c = false)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ U R c) (hne : K ≠ U R c) :
    ¬ Z R c ≤ K ⊔ fixedCore R c := by
  intro h
  apply hne
  apply le_antisymm hK
  intro u hu
  have hmem := h (U_le_Z R c hu)
  rw [← SetLike.mem_coe, join_fixedCore_eq_mul R K
    (hK.trans ((U_le_Z R c).trans (Z_le_stabilizer R c)))] at hmem
  obtain ⟨k, hk, d, hd, heq⟩ := hmem
  have hdU : d ∈ U R c := by
    have hh := (U R c).mul_mem ((U R c).inv_mem (hK hk)) hu
    rw [← heq, inv_mul_cancel_left] at hh
    exact hh
  have hd1 : d = 1 := by
    have hd' : d ∈ U R c ⊓ centralizer (Ltilde R c : Set (FreeAmalgam R)) := ⟨hdU, hd.2⟩
    rw [Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc] at hd'
    exact hd'
  change k * d = u at heq
  rw [hd1, mul_one] at heq
  rwa [← heq]

/-- If a local actor displaces the radius group only into a proper subgroup
of the natural summand, (4.4.1)(ii) forces that displacement into D. -/
theorem radius_displacement_le_fixed [Finite M]
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    {c : Vertex R} (hc : color R c = false)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c)
    (hK : K ≤ U R c) (hne : K ≠ U R c)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ ≤ fixedCore R c := by
  have hQn : Q R c ≤ normalizer (fixedCore R c : Set (FreeAmalgam R)) :=
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)
  suffices hV : V R c ≤ commutatorPreimage (Q R c) A (fixedCore R c) from
    (commutator_mono hV le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQn)
  apply (V_le_iff R hc _).mpr
  intro d hd hdist
  have hdQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    exact lt_of_le_of_lt hdist common.large_distance
  apply le_commutatorPreimage hdQ
  by_cases hdc : d = c
  · subst d
    exact (commutator_mono le_rfl hA).trans_eq (geometry.centralizes c hc) |>.trans bot_le
  have hdist2 : (cosetGraph R).dist d c = 2 := by
    have hpos := (cosetGraph_connected R).pos_dist_of_ne hdc
    have hnot1 : (cosetGraph R).dist d c ≠ 1 := by
      intro h1
      have hadj := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact adjacent_color_ne R hadj (hd.trans hc.symm)
    omega
  by_cases hinit : ⁅Z R d, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl hA).trans hinit
  apply commutator_le.mpr
  intro z hz x hx
  have hxQ := hA hx
  have hs : ⁅localZSpan R d c, zpowers x⁆ ≤ fixedCore R c := by
    by_contra hn
    have hh := (hlocal d c hd hc hdist2 hinit).2 x hxQ hn
    apply not_Z_le_proper_natural_sup_fixed common hc hK hne
    apply hh.trans
    apply sup_le_sup_right
    rw [commutator_comm]
    exact (commutator_mono (localZSpan_le_V R hdist2.le) (zpowers_le.mpr hx)).trans hbound
  exact hs (commutator_mem_commutator (Z_le_localZSpan R d c hz) (mem_zpowers x))

/-- A proper natural bound actually kills the displacement, since U and D
have trivial intersection. -/
theorem radius_displacement_eq_bot [Finite M]
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    {c : Vertex R} (hc : color R c = false)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c)
    (hK : K ≤ U R c) (hne : K ≠ U R c)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc]
  exact le_inf (hbound.trans hK)
    ((radius_displacement_le_fixed common hlocal hc hA hK hne hbound).trans inf_le_right)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
