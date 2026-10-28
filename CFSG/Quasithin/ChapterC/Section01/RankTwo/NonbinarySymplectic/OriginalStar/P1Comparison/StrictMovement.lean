module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEquality
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting
import all Theory.SpecificGroups.SymplecticFour.PointSupplement

/-!
# Strict movement by the original point-core intersection

The original edge radical has cubic image at both endpoints. Its image at
the first endpoint centralizes the selected long root. The point radical
there has index at most q in the edge radical, since the remaining quotient
is a two-subgroup of SL₂(q). Consequently the point-core intersection has
image larger than q at the opposite endpoint. Symplectic displacement
bounds then force its movement on the opposite natural cover to exceed q.

Source: MS93 (3.7), printed pp.876--877. The full point-core preimage and the
original edge radical are retained.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit

private theorem point_core_index_bound
    {G E : Type*} [Group G] [Field E] [Finite E] [CharP E 2]
    (κ : G →* Sp E) (T : Subgroup G) (hT : IsPGroup 2 T)
    (hc : T.map κ ≤ centralizer (RootSubgroup.group (F := E) 0 : Set (Sp E))) :
    (pointRadicalAmbient.comap κ).relIndex T ≤ Nat.card E := by
  have hlocal : T.map κ ≤ pointLocal := by
    rwa [RootNormalizerResidual.centralizer_zero_eq] at hc
  let α : T →* pointLocal := (κ.comp T.subtype).codRestrict pointLocal
    (fun x => hlocal (mem_map_of_mem κ x.property))
  let φ := pointQuotient.comp α
  have hk : φ.ker=(pointRadicalAmbient.comap κ).subgroupOf T := by
    ext x
    change pointQuotient (α x)=1 ↔ κ x ∈ pointRadicalAmbient
    change α x ∈ pointQuotient.ker ↔ _
    rw [pointQuotient_ker]
    exact (mem_map_iff_mem pointLocal.subtype_injective).symm
  change ((pointRadicalAmbient.comap κ).subgroupOf T).index ≤ _
  rw [←hk,index_ker]
  exact PointSupplement.rankOne_pgroup_card φ.range (hT.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)

private theorem actor_gt_field_of_cubic
    {G : Type*} [Group G] (Q P T : Subgroup G) [Finite T]
    (q : ℕ) (hq : 1<q) (hT : Q.relIndex T=q^3)
    (hP : P.relIndex T≤q) : q<Q.relIndex (P⊓T) := by
  have he := relIndex_inf_mul_relIndex Q P T
  have hlo := relIndex_le_of_le_left (show Q⊓P≤Q from inf_le_left)
    (show (Q⊓P).relIndex T≠0 from index_ne_zero_of_finite)
  rw [hT,←he] at hlo
  by_contra! hs
  have hle : q^3≤q^2 := hlo.trans (by simpa only [pow_two] using Nat.mul_le_mul hs hP)
  exact (Nat.pow_lt_pow_right hq (by decide : 2<3)).not_ge hle

private theorem cover_commutator_gt_field
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : Function.Surjective p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := E))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    [Finite (⁅A,U⁆ : Subgroup G)]
    (hlarge : Nat.card E<Nat.card (((commutator (Sp E)).subtype.comp β).range)) :
    Nat.card E<Nat.card (⁅A,U⁆ : Subgroup G) := by
  let α := (commutator (Sp E)).subtype.comp β
  let D := displacementSpace α.range
  choose w hw hm using fun v : D => natural_displacement_lifts U A j hjr β σ hact p hp v.val v.property
  let f : D → (⁅A,U⁆ : Subgroup G) := fun v => ⟨j (Multiplicative.ofAdd (w v)),hm v⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : w x=w y := Multiplicative.ofAdd.injective (hj (congrArg Subtype.val he))
    exact Subtype.ext ((hw x).symm.trans ((congrArg p hh).trans (hw y)))
  have hd := Nat.card_le_card_of_injective f hf
  rw [Module.natCard_eq_pow_finrank (K := E)] at hd
  by_contra! hs
  have hdim : Module.finrank E D≤1 := by
    have hh : Nat.card E^Module.finrank E D≤Nat.card E^1 := by simpa using hd.trans hs
    exact (Nat.pow_le_pow_iff_right (show 1<Nat.card E from Finite.one_lt_card)).mp hh
  have ha := card_actor_le_displacement_dimension α.range
  have hpow : (Module.finrank E D)^2≤1 := by nlinarith
  have hb := Nat.pow_le_pow_right (show 0<Nat.card E from Nat.card_pos) hpow
  exact hlarge.not_ge (ha.trans (by simpa only [pow_one] using hb))

variable {H F E : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable [Field E] [Finite E] [CharP E 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

/-- The marked point-core intersection has index at most q in the original
edge radical, for every retained long-root marking. -/
theorem original_point_core_edge_index
    (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E)
    (hroot : ((Z R z).subgroupOf (stabilizer R a)).map
      ((MulAut.conj u).toMonoidHom.comp κ)=RootSubgroup.group 0) :
    (markedPointCore R κ u).relIndex (Q R t)≤Nat.card E := by
  let S := stabilizer R a
  let ψ := (MulAut.conj u).toMonoidHom.comp κ
  have hTS : Q R t≤S := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hZS : Z R z≤S := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hψk : ψ.ker=(Q R a).subgroupOf S := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj u).injective,hκ]
  have hc : ((Q R t).subgroupOf S).map ψ ≤
      centralizer (RootSubgroup.group (F := E) 0 : Set (Sp E)) := by
    rw [←hroot]
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    have hm := original_nonsylow_critical_edge_commutator_le h hinner hnsyl path hb hat hzt
      (commutator_mem_commutator hy hx)
    have hk : ⁅y,x⁆∈ψ.ker := hψk.symm ▸ hm
    have he : ψ ⁅y,x⁆=1 := hk
    rw [map_commutatorElement] at he
    exact (commutatorElement_eq_one_iff_commute.mp he).eq
  have hp : IsPGroup 2 (Q R t) := by
    obtain ⟨v,⟨hav,htv⟩ | ⟨hav,htv⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
    · have ht : hVertex R v=act R v (beta R) := by simp [beta,act_hVertex]
      rw [htv,ht,Q_act,Q_beta]
      exact (h.radical.isPGroup.map _).map _
    · have hh := path.start_color
      rw [hav] at hh
      cases hh
  have hi := point_core_index_bound ψ ((Q R t).subgroupOf S) hp.comap_subtype hc
  rw [←relIndex_subgroupOf hTS,markedPointCore,subgroupOf_map_subtype_eq]
  exact hi

/-- The literal point-core intersection moves more than q elements of the
opposite original critical center. Its large actor image follows from both
cubic edge quotients, and movement is lifted through the full natural cover. -/
theorem original_point_core_strict_movement
    (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E)
    (hE : Nat.card E=2^n)
    (hroot : ((Z R z).subgroupOf (stabilizer R a)).map
      ((MulAut.conj u).toMonoidHom.comp κ)=RootSubgroup.group 0) :
    2^n<Nat.card (⁅Z R z,markedPointCore R κ u⊓Q R t⁆ : Subgroup (FreeAmalgam R)) := by
  let J := markedPointCore R κ u⊓Q R t
  have hTS : Q R t≤stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hJS : J≤stabilizer R z := inf_le_right.trans hTS
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective (inclusion hTS) (inclusion_injective _)
  have hindex := original_point_core_edge_index h hinner hnsyl path hb hat hzt κ hκ u hroot
  rw [hE] at hindex
  have hlarge : 2^n<(Q R z).relIndex J := actor_gt_field_of_cubic (Q R z)
    (markedPointCore R κ u) (Q R t) (2^n)
    (one_lt_pow₀ (by decide) (by have := h.nonbinary; omega))
    (original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt) hindex
  obtain ⟨cv⟩ := exists_ambient_cover h path.end_color
  let s := originalMovedSection h
  let β : J →* L (K := cv.field.Carrier) := cv.equiv.groupEquiv.toMonoidHom.comp
    ((cv.quotient.comp (inclusion hJS)).codRestrict
      (K.map (QuotientGroup.mk' (pCore 2 H)))
      (fun _ => (original_component_eq_top hinner).symm.le (mem_top _)))
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp β
  have hα : α=(coverQuotient h hinner cv).comp (inclusion hJS) := by
    apply MonoidHom.ext
    intro x
    exact (coverQuotient_apply h hinner cv (inclusion hJS x)).symm
  have hαk : α.ker=(Q R z).subgroupOf J := by
    rw [hα,←MonoidHom.comap_ker,coverQuotient_kernel,comap_inclusion_subgroupOf]
  have hαlarge : Nat.card cv.field.Carrier<Nat.card α.range := by
    rw [←index_ker,hαk,cv.field.card_eq,cv.degree]
    exact hlarge
  have hact (x : J) (w : s.space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd (MovedSection.coverAction s cv.equiv (β x) w))=
        x.val*cv.embedding (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change cv.embedding (Multiplicative.ofAdd (s.space.toRepresentation
      (cv.equiv.groupEquiv.symm (cv.equiv.groupEquiv _)) w))=_
    rw [cv.equiv.groupEquiv.symm_apply_apply]
    exact cv.conjugation (inclusion hJS x) w
  have hUS : U R z≤stabilizer R z := (U_le_Z z).trans (Z_le_stabilizer R z)
  have hZJS : ⁅Z R z,J⁆≤stabilizer R z :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le (Z_le_stabilizer R z) hJS)
  have hJUS : ⁅J,U R z⁆≤stabilizer R z :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hJS hUS)
  let : Finite (⁅J,U R z⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hJUS) (inclusion_injective _)
  let : Finite (⁅Z R z,J⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hZJS) (inclusion_injective _)
  have hm := cover_commutator_gt_field (MovedSection.coverAction s cv.equiv)
    (MovedSection.coverProjection s cv.equiv) cv.cover.1 (U R z) J
    cv.embedding cv.injective cv.range_eq β hact hαlarge
  rw [cv.field.card_eq,cv.degree] at hm
  apply hm.trans_le
  apply card_le_of_le
  rw [commutator_comm]
  exact commutator_mono (U_le_Z z) le_rfl

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
