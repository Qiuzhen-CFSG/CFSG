module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourMarkedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEquality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourComparison

/-!
# Equality of the original complete fixed attachments

Every subgroup of the opposite critical image avoids rank-one displacement:
its fixed hyperplane would otherwise have an escaping centralizer. The
plane-coordinate calculation therefore represents each common-displacement
element outside the second attachment as an individual commutator. Such
a value in the first attachment is trivial, giving containment and then
equality. Combining the large-image and field-sized branches proves the
attachment equality for every original nonsylow distance-two critical pair.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875.
The original radical, quotient marking and complete fixed attachments are
retained. Internal imports reuse generic cover and subgroup calculations;
no saturation premise for a characteristic replacement is used.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

/-- Every subgroup of the opposite critical image avoids rank-one displacement
when the complete attachments differ; its hypothetical fixed hyperplane
would contradict the proved nonescaping centralizer comparison. -/
theorem original_source_four_large_no_rank_one_subactor
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (A : Subgroup (FreeAmalgam R)) (hAZ : A ≤ Z R a)
    (hAT : A ≤ Q R t) :
    Module.finrank cv.field.Carrier (displacementSpace
      (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hAT)).range) ≠ 1 := by
  intro hd
  have hi := plane_cover_full_fixed_index h hshort hinner g hb path.end_color hzt cv A hAT
  rw [hd,pow_one] at hi
  obtain ⟨P,B,hm,hP,hpoint,hX⟩ :=
    plane_cover_dual_marked_hyperplane h hshort hinner g hb path.end_color hzt cv A hAT hi
  have hn := original_source_four_large_marked_centralizer_le h hshort hinner hnsyl g hb path hat hzt
    hcritical hne P B hm
  have hAQ : A ≤ Q R z := by
    intro x hx
    apply hn
    refine ⟨hAZ hx,?_⟩
    intro u hu
    have hu' : u ∈ Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) := hu
    exact ((hX.le hu').2 x hx).symm
  let α := ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hAT)
  have hz : displacementSpace α.range=⊥ := SaturatedDistanceTwo.displacement_eq_bot_of_image_one α (fun b => by
    change inclusion hAT b ∈ ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).ker
    rw [cv.actor_kernel]
    exact hAQ b.property)
  change Module.finrank cv.field.Carrier (displacementSpace α.range)=1 at hd
  rw [hz,finrank_bot] at hd
  omega

private theorem large_actor_geometry
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (hZaT : Z R a ≤ Q R t) :
    let γ := ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hZaT)
    Nat.card γ.range=Nat.card cv.field.Carrier^2 ∧
      ∀ x ∈ γ.range, Module.finrank cv.field.Carrier (displacementSpace (zpowers x)) ≠ 1 := by
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  let γ := α.comp (inclusion hZaT)
  have hc : Nat.card γ.range=Nat.card cv.field.Carrier^2 := by
    have hidx := (original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical).2.2.1
    have hcard : Nat.card γ.range=(Q R z).relIndex (Z R a) := by
      dsimp only [γ,α]
      rw [←index_ker,←MonoidHom.comap_ker,cv.actor_kernel,comap_inclusion_subgroupOf]
      rfl
    rw [hcard,hidx,cv.field.card_eq,cv.degree]
  have hn : ∀ x ∈ γ.range,
      Module.finrank cv.field.Carrier (displacementSpace (zpowers x)) ≠ 1 := by
    rintro x ⟨y,rfl⟩
    have hcy := SaturatedDistanceTwo.cyclic_image (Q R t) α y.val (hZaT y.property)
    have hno := original_source_four_large_no_rank_one_subactor h hshort hinner hnsyl g hb path hat hzt
      hcritical hne cv (zpowers y.val) (zpowers_le.mpr y.property) (zpowers_le.mpr (hZaT y.property))
    intro he
    apply hno
    exact (congrArg (fun J : Subgroup (Sp cv.field.Carrier) =>
      Module.finrank cv.field.Carrier (displacementSpace J)) hcy).trans he
  exact ⟨hc,hn⟩

/-- In the large unequal-attachment branch, every element of the common
displacement outside the second complete attachment is an individual
commutator of the original full Z-layers. -/
theorem original_source_four_large_unequal_values
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (b : FreeAmalgam R) (hbR : b ∈ ⁅Z R a,Z R z⁆)
    (hbA : b ∉ U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
    ∃ x ∈ Z R a, ∃ y ∈ Z R z, ⁅x,y⁆=b := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  obtain ⟨⟨cv⟩,_⟩ := original_source_four_large_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical
  have hZaT : Z R a ≤ Q R t :=
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)).trans (Q_le_adjacent_h R ht hat)
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  let β := cv.actor.comp (inclusion hZaT)
  let γ := α.comp (inclusion hZaT)
  obtain ⟨k,hk⟩ := cv.plane_image
  have hJ : γ.range.map (MulAut.conj k).toMonoidHom ≤ planeRadicalAmbient := by
    have hle : γ.range ≤ α.range := by
      rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZaT x,rfl⟩
    exact (map_mono hle).trans_eq hk
  obtain ⟨hc,hn⟩ := large_actor_geometry h hshort hinner hnsyl g hb path hat hzt hcritical hne cv hZaT
  let p := MovedSection.coverProjection (originalMovedSection h) cv.equiv
  have hker : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro x ⟨hx,hxC⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact ⟨w,(cv.kernel _).mpr hxC,rfl⟩
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hCz := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have hCa := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have hCU : Z R t ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (hCz.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmove : ⁅Z R a,Z R z⁆ ≤ ⁅Z R a,U R z⁆ := by
    apply commutator_le.mpr
    intro x hx y hy
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt,
      ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hy
    obtain ⟨u,hu,v,hv,rfl⟩ := hy
    have hcomm : Commute x v := (Z R a).le_centralizer (hCa hv) x hx
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hcomm]
    simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hx hu
  have hF : 2 < Nat.card cv.field.Carrier := by
    rw [cv.field.card_eq,cv.degree]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  obtain ⟨x,hx,w,hw⟩ := SaturatedDistanceTwo.marked_embedded_plane_values hF p cv.cover cv.embedding
    (Z R a) β (fun x w => cv.actor_conjugation (inclusion hZaT x) w) k hJ hc hn b
    (by rw [cv.range_eq]; exact hmove hbR) (by rwa [hker])
  exact ⟨x,hx,cv.embedding (Multiplicative.ofAdd w),U_le_Z z (cv.range_eq ▸ ⟨_,rfl⟩),hw⟩

/-- The nonescaping comparison completes source (4) at critical index q squared. -/
theorem original_source_four_large_fixed_attachments
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  classical
  by_contra hne
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let B := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  have hAB : A ≤ B := by
    intro b hbA
    by_contra hbB
    have hgeom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
    have hbR : b ∈ ⁅Z R a,Z R z⁆ := hgeom.2.2.2.2.2.2 (mem_sup_left hbA)
    obtain ⟨x,hx,y,hy,he⟩ := original_source_four_large_unequal_values h hshort hinner hnsyl g hb path hat hzt hcritical hne b hbR hbB
    have heinv : ⁅y,x⁆=b⁻¹ := by rw [←commutatorElement_inv,he]
    have hone := original_critical_full_value_in_fixed_eq_one h hshort hinner path hb hat hzt y hy x hx
      (by rw [heinv]; exact (centralizer _).inv_mem hbA.2)
    have hb1 : b=1 := by rw [heinv] at hone; exact inv_eq_one.mp hone
    exact hbB (hb1 ▸ one_mem B)
  let := finite_Z R z
  let : Finite B := Finite.of_injective
    (inclusion (show B ≤ Z R z from inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  have hcard := original_source_four_large_attachment_card_eq h hshort hinner hnsyl g hb path hat hzt hcritical
  exact hne (Subgroup.eq_of_le_of_card_ge hAB hcard.ge)


/-- MS93 (3.7)(4): the two complete fixed attachments agree for every
critical pair of the original nonsylow radical at distance two, at the original field degree. -/
theorem original_source_four_fixed_attachments
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  by_cases hc : (2^n)^2 ≤ (Q R z).relIndex (Z R a)
  · exact original_source_four_large_fixed_attachments h hshort hinner hnsyl g hb path hat hzt hc
  · obtain ⟨he,_⟩ := h.original_small_critical_indices_eq_field path (by omega)
      (by rw [h.field_card]; exact lt_of_not_ge hc)
    exact original_source_four_of_field_critical h hshort hinner hnsyl g hb path hat hzt
      (he.trans h.field_card)


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
