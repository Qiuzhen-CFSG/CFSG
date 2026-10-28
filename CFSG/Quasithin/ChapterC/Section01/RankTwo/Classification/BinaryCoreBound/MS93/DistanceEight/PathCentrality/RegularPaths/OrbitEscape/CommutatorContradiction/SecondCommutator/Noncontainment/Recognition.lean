module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Faithfulness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Lift
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Noncontainment.SmallDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Radical
public import Theory.ElementaryAbelian.Quotient

/-!
# The critical hyperplane and the full radius natural section

Assume R₂ = [Z_(a+2), V_delta intersect Q_a] lies in Z_delta D_delta,
and that its literal hyperplane has index two in V_delta. The existing
small-displacement estimate on V_delta/(Z_delta D_delta), duality, and
idempotence of the two-residual commutator give the triple bound
[V_delta,Q_delta,Ltilde_delta] ≤ Z_delta.

The fixed-core quotient alone does not force a split natural section.
To recognize the actual radius head V_delta/(Z_delta[V_delta,Q_delta]),
retain the original critical subgroups. If R₂ escapes Z_delta, its order
is four. Its literal conjugation invariance puts it in U_(a+2)^g, and
the nonzero conjugate commutator together with the critical line fills R₂.
Since Z_(a+2)^g lies in Q_delta, this gives
R₂ ≤ Z_delta[V_delta,Q_delta]; the other case is immediate.

An involution of the actual Z_(a+2) outside Q_delta therefore fixes the
literal hyperplane modulo this radical preimage. The index-two estimate
bounds its entire head displacement by two. The faithful SL₃(2) head
action now has an intrinsic fixed/moving splitting and equivariant natural
coordinates. Lifting them constructs every NaturalSectionAt clause with
the original quotient maps, kernel Q_delta and relative normalities.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893; the expanded c(U) notation is on p.881,
and the binary representation alternatives are (1.4)--(1.5), pp.842--843.
-/

public section

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
open Escape.Initial.Natural.Triple

private theorem remove_fixed_error {G : Type*} [Group G] [Finite G]
    (H N D : Subgroup G) [H.Normal] [N.Normal]
    (hp : IsPGroup 2 H) (hD : D ≤ centralizer (pResidual 2 G : Set G))
    (h : ⁅H, pResidual 2 G⁆ ≤ N ⊔ D) : ⁅H, pResidual 2 G⁆ ≤ N := by
  have hpre : N ⊔ D ≤ commutatorPreimage ⊤ (pResidual 2 G) N := by
    apply sup_le
    · exact le_commutatorPreimage le_top (commutator_le_left N _)
    · exact le_commutatorPreimage le_top
        ((commutator_eq_bot_iff_le_centralizer.mpr hD).le.trans bot_le)
  rw [← commutator_isPPerfect_idempotent (pResidual 2 G) H
    (isPPerfect_pResidual 2) hp le_normalizer_of_normal]
  exact (commutator_mono (h.trans hpre) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

private theorem triple_of_small_fixed_quotient {G : Type*} [Group G] [Finite G]
    (H N Q D : Subgroup G) [H.Normal] [N.Normal] [Q.Normal] [D.Normal]
    [IsElementaryAbelian 2 H]
    (π : G →* SL) (hsurj : Function.Surjective π) (hker : π.ker = Q)
    (hp : IsPGroup 2 Q) (hD : D ≤ centralizer (pResidual 2 G : Set G))
    (hn : ¬ ⁅H, pResidual 2 G⁆ ≤ N ⊔ ⁅H, Q⁆)
    (x : G) (hx : x ∉ Q)
    (hsmall : (N ⊔ D).relIndex ⁅H, zpowers x⁆ ≤ 2) :
    ⁅⁅H, Q⁆, pResidual 2 G⁆ ≤ N := by
  let B := N ⊔ D
  let ρ := (sectionRepresentation H B).dual
  have hne : (zpowers x).map π ≠ ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he (mem_zpowers x)
    rw [hker] at hh
    exact hx hh
  have hnf : ¬ Representation.BinaryOffender.fixedSpace ρ π.ker ≤
      Representation.BinaryOffender.fixedSpace ρ (pResidual 2 G) := by
    intro he
    rw [hker] at he
    have hb := commutator_le_sup_of_dual_fixedSpace_le H B Q (pResidual 2 G) he
    have hb' : ⁅H, pResidual 2 G⁆ ≤ (N ⊔ ⁅H, Q⁆) ⊔ D := by
      simpa only [B, sup_assoc, sup_left_comm, sup_comm] using hb
    exact hn (remove_fixed_error H (N ⊔ ⁅H, Q⁆) D
      (IsElementaryAbelian.isPGroup 2 H) hD hb')
  have hf := moving_le_fixed_of_fixedSpace_not_le π hsurj (hker ▸ hp)
    (zpowers x) hne ρ (dual_fixedCodim_le_one H B (zpowers x) hsmall) hnf
  rw [hker] at hf
  have ht := triple_le_of_dual_fixed H B Q (pResidual 2 G) hf
  exact remove_fixed_error ⁅H, Q⁆ N D
    ((IsElementaryAbelian.isPGroup 2 H).to_le (commutator_le_left H Q)) hD ht

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem radius_triple_of_small_fixed_displacement
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {v : Vertex R} (hv : color R v = false)
    (x : stabilizer R v) (hx : (x : FreeAmalgam R) ∉ Q R v)
    (hsmall : (Z R v ⊔ fixedCore R v).relIndex
      ⁅V R v, zpowers (x : FreeAmalgam R)⁆ ≤ 2) :
    ⁅⁅V R v, Q R v⁆, Ltilde R v⁆ ≤ Z R v := by
  let S := stabilizer R v
  let H := (V R v).subgroupOf S
  let N := (Z R v).subgroupOf S
  let Q₀ := (Q R v).subgroupOf S
  let D := (fixedCore R v).subgroupOf S
  let := finite_stabilizer R v
  let : H.Normal := Escape.Initial.Natural.radius_normal v
  let : N.Normal := geometry.Z_normal v
  let : Q₀.Normal := Q_normal R v
  let : D.Normal := fixedCore_normal R v
  have hVS : V R v ≤ S := (geometry.V_le_Q (by omega) v hv).trans (fun _ hy => hy.1)
  let := V_elementary_of_four_lt R hv hb
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.subgroupOf hVS
  obtain ⟨π, hπ, hk⟩ := Escape.Initial.Natural.exists_localProjection source v hv
  have hp : IsPGroup 2 Q₀ :=
    (Q_isPGroup R source.two_group source.core_le v hv).comap_subtype
  have hD : D ≤ centralizer (pResidual 2 S : Set S) := by
    intro d hd l hl
    apply Subtype.ext
    exact hd.2 l ((pResidual 2 S).mem_map_of_mem S.subtype hl)
  have hn : ¬ ⁅H, pResidual 2 S⁆ ≤ N ⊔ ⁅H, Q₀⁆ := by
    intro he
    have hm := map_mono (f := S.subtype) he
    rw [Subgroup.map_sup, map_commutator, map_commutator,
      map_subgroupOf_eq_of_le hVS,
      map_subgroupOf_eq_of_le (Z_le_stabilizer R v),
      map_subgroupOf_eq_of_le (show Q R v ≤ S from fun _ hy => hy.1)] at hm
    exact radius_head_moving source geometry (by omega) (moduleFacts common) v hv hm
  have hi := relIndex_map_map_of_injective (N ⊔ D) ⁅H, zpowers x⁆ S.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (Z_le_stabilizer R v),
    map_subgroupOf_eq_of_le (show fixedCore R v ≤ S from fun _ hy => hy.1.1),
    map_commutator, map_subgroupOf_eq_of_le hVS, MonoidHom.map_zpowers] at hi
  have ht := triple_of_small_fixed_quotient H N Q₀ D π hπ hk hp hD hn x hx
    (hi.symm ▸ hsmall)
  have hm := map_mono (f := S.subtype) ht
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hVS,
    map_subgroupOf_eq_of_le (show Q R v ≤ S from fun _ hy => hy.1),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R v)] at hm
  exact hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Escape.Initial.Natural Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The actual conjugate critical subgroup removes the fixed-core error on the head. -/
theorem secondCommutator_le_delta_radical
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥) :
    s.secondCommutator ≤ Z R s.delta ⊔ ⁅V R s.delta, Q R s.delta⁆ := by
  by_cases hZ : s.secondCommutator ≤ Z R s.delta
  · exact hZ.trans le_sup_left
  have hcard := s.secondCommutator_card_four_of_not_le_delta_Z hb common hZ
  have hmap := s.secondCommutator_map_eq_of_not_le_delta_Z hb common hlocal hZ
  have hnatural := s.secondCommutator_le_conjugate_natural_of_map_eq hb common hmap
  have hbound := s.conjugate_commutator_le_second_of_natural hb common hcard hnatural
  rw [s.secondCommutator_eq_critical_sup_conjugate hb common hlocal hmove hbound]
  apply sup_le_sup (s.critical_commutator_le_delta_Z hb)
  rw [commutator_comm]
  exact commutator_mono le_rfl (s.conjugateSecond_Z_le_delta_kernel hb)

/-- The representation argument on the literal radius quotient needs the
actual radical containment. This separates that input from its local-control
producer, allowing the same marked recognition proof on critical prefixes. -/
theorem radius_naturalSection_of_secondCommutator_le_and_radical
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry)
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hR₂ : s.secondCommutator ≤ Z R s.delta ⊔ ⁅V R s.delta, Q R s.delta⁆)
    (hcontain : s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta) :
    Nonempty (Escape.NaturalSectionAt s.delta (V R s.delta) (Z R s.delta)) := by
  obtain ⟨x, hxZ, hxQ, htwo, hsmall⟩ :=
    s.small_fixed_displacement_of_secondCommutator_le hb common hindex hcontain
  have htriple := radius_triple_of_small_fixed_displacement common hb s.delta_color x hxQ hsmall
  let S := stabilizer R s.delta
  let H := localRadius s.delta
  let N := Escape.Initial.Natural.Splitting.localZ s.delta
  let Q₀ := Escape.Initial.Natural.Splitting.localKernel s.delta
  let B := localRadical s.delta
  let K := (V R s.delta ⊓ Q R a).subgroupOf S
  let π := localProjection source s.delta s.delta_color
  let ρ := radiusHeadAction source geometry s.delta s.delta_color
  let := finite_stabilizer R s.delta
  let := geometry.Z_normal s.delta
  let := radiusHead_elementary source geometry (by omega) (moduleFacts common)
    s.delta s.delta_color
  have hHS : V R s.delta ≤ S :=
    (geometry.V_le_Q (by omega) s.delta s.delta_color).trans (fun _ hy => hy.1)
  have hBH : B ≤ H := sup_le (fun _ hy => Z_le_VBall R s.delta 2 hy)
    (commutator_le_left H Q₀)
  have hKN : ⁅K, zpowers x⁆ ≤ B := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le (inf_le_left.trans hHS),
      MonoidHom.map_zpowers]
    have hmapB : B.map S.subtype = Z R s.delta ⊔ ⁅V R s.delta, Q R s.delta⁆ := by
      change (N ⊔ ⁅H, Q₀⁆).map S.subtype = _
      rw [Subgroup.map_sup, map_commutator,
        map_subgroupOf_eq_of_le (Z_le_stabilizer R s.delta),
        map_subgroupOf_eq_of_le hHS,
        map_subgroupOf_eq_of_le (show Q R s.delta ≤ S from fun _ hy => hy.1)]
    have hc : ⁅V R s.delta ⊓ Q R a, zpowers (x : FreeAmalgam R)⁆ ≤ s.secondCommutator := by
      rw [commutator_comm]
      exact commutator_mono (zpowers_le.mpr hxZ) le_rfl
    rw [hmapB]
    exact hc.trans hR₂
  have hderived : ⁅H, H⁆ ≤ B := by
    let := s.radius_elementary hb
    let := IsElementaryAbelian.subgroupOf (p := 2) hHS
    have hcomm : ⁅H, H⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    rw [hcomm]
    exact bot_le
  have hidx : K.relIndex H = 2 := by
    rw [← relIndex_map_map_of_injective K H S.subtype_injective,
      map_subgroupOf_eq_of_le (inf_le_left.trans hHS), map_subgroupOf_eq_of_le hHS,
      inf_relIndex_left, hindex]
  have hdisp := quotient_commutator_relIndex_le_mul_of_restriction
    H K B B (comap_mono inf_le_left) hBH hBH inferInstance hderived
    x (by rw [normalizer_eq_top]; trivial) hKN
  rw [relIndex_self, mul_one, hidx, relIndex_sup_right] at hdisp
  have hπx : π x ≠ 1 := by
    intro he
    have hk : x ∈ π.ker := he
    rw [localProjection_kernel] at hk
    exact hxQ hk
  have hhead : HasSmallInvolution ρ := by
    refine ⟨π x, hπx, by rw [← map_pow, htwo, map_one], ?_⟩
    have hmap : (zpowers x).map (ρ.comp π) = zpowers (ρ (π x)) :=
      MonoidHom.map_zpowers _ _
    rw [← hmap]
    change Nat.card (commutatorAction ((zpowers x).map
      ((headAction H N Q₀ π (localProjection_surjective source s.delta s.delta_color)
        (localProjection_kernel source s.delta s.delta_color)).comp π))
      (H ⧸ (Escape.radicalPreimage Q₀ H N).subgroupOf H)) ≤ 2
    rw [headAction_comp, quotientAction_displacement_card]
    exact hdisp
  obtain ⟨split⟩ := naturalActionSplitting_of_small_involution ρ
    (radiusHeadAction_injective_of_triple source geometry (by omega) (moduleFacts common)
      s.delta s.delta_color htriple) hhead
  obtain ⟨sectionAt⟩ := singleNaturalSection_of_head_splitting H N Q₀
    (pResidual 2 S) π (localProjection_surjective source s.delta s.delta_color)
    (localProjection_kernel source s.delta s.delta_color)
    (fun _ hy => Z_le_VBall R s.delta 2 hy)
    (elementary_radius_quotient source geometry (by omega) (moduleFacts common)
      s.delta s.delta_color)
    (local_triple geometry (by omega) s.delta s.delta_color htriple) split
  exact ⟨{
    local_group := hHS
    kernel_le := Z_le_VBall R s.delta 2
    projection := π
    module_section := sectionAt }⟩

/-- The full source representation implication on the literal radius quotient. -/
theorem radius_naturalSection_of_secondCommutator_le
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hcontain : s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta) :
    Nonempty (Escape.NaturalSectionAt s.delta (V R s.delta) (Z R s.delta)) :=
  s.radius_naturalSection_of_secondCommutator_le_and_radical hb common hindex
    (s.secondCommutator_le_delta_radical hb common hlocal hmove) hcontain
end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
