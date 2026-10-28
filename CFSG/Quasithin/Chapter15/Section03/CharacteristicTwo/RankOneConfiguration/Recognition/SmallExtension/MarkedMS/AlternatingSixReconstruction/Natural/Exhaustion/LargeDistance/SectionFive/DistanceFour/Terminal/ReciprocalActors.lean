module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalSpans
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalQuotient

/-!
# Elementary reciprocal actors in the actual local quotient

The reciprocal span has elementary quotient by the opposite core: its
squares lie in its derived subgroup, and full-radius fixedness places that
derived subgroup in the seed. Its literal local-quotient image therefore
has the prescribed elementary structure and relative-index order. A
nonabelian span gives a nontrivial actor because containment in the seed
core would make every generating conjugate centralize the whole span.

Source: MS93 (5.12)(2), printed p.926. The factorization consumer uses
these actors on the literal moved Baumann quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include h in
private theorem reciprocal_span_sq_mem_derived
    (_hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (x : localZSpan d.radical a c) :
    (x : FreeAmalgam d.radical)^2 ∈ ⁅localZSpan d.radical a c,localZSpan d.radical a c⁆ := by
  let P := localZSpan d.radical a c
  let D := _root_.commutator P
  let q := QuotientGroup.mk' D
  let : IsMulCommutative (P ⧸ D) := Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let K := ((powMonoidHom 2).comp q).ker
  have hPK : P ≤ K.map P.subtype := by
    apply iSup_le
    intro g z hz
    have hzP : z ∈ P := (le_iSup (fun k : stabilizer d.radical c =>
      Z d.radical (act d.radical k a)) g) hz
    let zP : P := ⟨z,hzP⟩
    refine ⟨zP,?_,rfl⟩
    change q zP ^ 2 = 1
    rw [←map_pow]
    have hp : zP^2 = 1 := by
      apply Subtype.ext
      let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d)
        (act d.radical g a) ((action_preserves_color d.radical g a).trans ha)
      exact elemPow_eq_one_of_isElementaryAbelian z hz
    rw [hp,map_one]
  obtain ⟨y,hy,hyx⟩ := hPK x.property
  have he : y = x := Subtype.ext hyx
  subst y
  have hx : q x^2 = 1 := hy
  have hxD : x^2 ∈ D := (QuotientGroup.eq_one_iff _).mp (by
    change q (x^2) = 1
    rw [map_pow]
    exact hx)
  rw [←map_subtype_commutator]
  exact mem_map_of_mem P.subtype hxD

theorem reciprocal_actor_kernel_normal
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2) :
    ((Q d.radical a).subgroupOf (localZSpan d.radical a c)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((localZSpan_le_Q d.radical hc hd.le hb).trans
      ((Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm,hd])).trans
        (Q_normalized d.radical a)))

include h in
theorem reciprocal_actor_quotient_elementary_of_radius_fixed
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2)
    (hfixedC : ⁅V d.radical c,Q d.radical c⁆ ≤ fixedCore d.radical c) :
    letI := reciprocal_actor_kernel_normal (h := h) hb ha hc hd
    IsElementaryAbelian 2 ((localZSpan d.radical a c) ⧸
      (Q d.radical a).subgroupOf (localZSpan d.radical a c)) := by
  let := reciprocal_actor_kernel_normal (h := h) hb ha hc hd
  let P := localZSpan d.radical a c
  let N := (Q d.radical a).subgroupOf P
  have hbound : ⁅P,P⁆ ≤ Q d.radical a :=
    ((commutator_mono le_rfl (localZSpan_le_Q d.radical hc hd.le hb)).trans
      (reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb hc ha
        (by rwa [SimpleGraph.dist_comm]) hfixedC).2).trans
      ((Z_le_VBall d.radical a 2).trans (V_le_Q d.radical ha hb))
  have hp (x : P ⧸ N) : x^2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (hbound (reciprocal_span_sq_mem_derived (h := h) hb ha x))
  let : IsMulCommutative (P ⧸ N) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun v => orderOf_dvd_of_pow_eq_one (hp v)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

/-- The reciprocal span has its literal elementary image in the local
quotient; its order is the opposite-core relative index. -/
theorem reciprocal_actor_image_data_of_radius_fixed
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2)
    (hfixedC : ⁅V d.radical c,Q d.radical c⁆ ≤ fixedCore d.radical c) :
    letI := Q_normal d.radical a
    let A := ((localZSpan d.radical a c).subgroupOf (stabilizer d.radical a)).map
      (QuotientGroup.mk' ((Q d.radical a).subgroupOf (stabilizer d.radical a)))
    IsElementaryAbelian 2 A ∧ Nat.card A = (Q d.radical a).relIndex (localZSpan d.radical a c) ∧
      (A = ⊥ ↔ localZSpan d.radical a c ≤ Q d.radical a) := by
  let := Q_normal d.radical a
  let := reciprocal_actor_kernel_normal (h := h) hb ha hc hd
  let := reciprocal_actor_quotient_elementary_of_radius_fixed (h := h) hb ha hc hd hfixedC
  let H := stabilizer d.radical a
  let P := localZSpan d.radical a c
  let N := (Q d.radical a).subgroupOf P
  let π := QuotientGroup.mk' ((Q d.radical a).subgroupOf H)
  let A := (P.subgroupOf H).map π
  have hPH : P ≤ H := (localZSpan_le_Q d.radical hc hd.le hb).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm,hd]))
  let f : P →* A := {
    toFun x := ⟨π ⟨x,hPH x.property⟩,⟨⟨x,hPH x.property⟩,x.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_one π
    map_mul' x y := by
      apply Subtype.ext
      exact map_mul π (⟨x,hPH x.property⟩ : H) (⟨y,hPH y.property⟩ : H) }
  have hf : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hk : f.ker = N := by
    ext x
    change f x = 1 ↔ (x : FreeAmalgam d.radical) ∈ Q d.radical a
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (⟨x,hPH x.property⟩ : H)
  have hEA : IsElementaryAbelian 2 A := by
    let fbar : P ⧸ N →* A := QuotientGroup.lift N f hk.ge
    exact IsElementaryAbelian.of_surjective fbar
      (QuotientGroup.lift_surjective_of_surjective N f hf hk.ge)
  have hcard : Nat.card A = (Q d.radical a).relIndex P := by
    have he := (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm
    rw [hk] at he
    exact he
  refine ⟨hEA,hcard,?_⟩
  constructor
  · intro he x hx
    have hxA : π ⟨x,hPH hx⟩ ∈ A := ⟨⟨x,hPH hx⟩,hx,rfl⟩
    have hxone : π ⟨x,hPH hx⟩ = 1 := by
      change A = ⊥ at he
      rw [he] at hxA
      exact hxA
    exact (QuotientGroup.eq_one_iff (⟨x,hPH hx⟩ : H)).mp hxone
  · intro hPQ
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr (hPQ hx)

/-- A nonabelian orbit span cannot lie in its seed vertex core: otherwise
all its generating conjugates centralize the whole span. -/
theorem reciprocal_nonabelian_span_not_le_seed_core
    {a c : Vertex d.radical} (hc : color d.radical c = false)
    (hnon : ⁅localZSpan d.radical c a,localZSpan d.radical c a⁆ ≠ ⊥) :
    ¬ localZSpan d.radical c a ≤ Q d.radical c := by
  intro hPQ
  let P := localZSpan d.radical c a
  have hZC : Z d.radical c ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hc)).trans
      (centralizer_le hPQ)
  have hnC : stabilizer d.radical a ≤
      normalizer (centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    (localZSpan_normalized d.radical c a).trans (normalizer_le_normalizer_centralizer P)
  apply hnon
  apply commutator_eq_bot_iff_le_centralizer.mpr
  conv_lhs => rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  exact (map_mono hZC).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (hnC ((stabilizer d.radical a).inv_mem g.property)))


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
