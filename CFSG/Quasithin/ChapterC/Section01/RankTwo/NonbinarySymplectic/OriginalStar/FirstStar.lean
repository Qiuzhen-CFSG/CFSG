module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.FirstStar
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedIndex

/-!
# First star comparison for the original radical

An escaping full-Sylow seed forces field-sized critical images and then a
field-sized action on the full endpoint intersection. The same elementary
intersection normalizes that seed, so its action has order at most the field
degree. This contradiction gives the first star comparison, with the original
radical, original graph, coefficient field and full cover kernels.

The internal import reuses the generic elementary seed-action calculation
within this source family. No characteristic-minimum or saturation premise is
introduced. Source: MS93 (3.3)--(3.4), printed pp.867--869.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- Reciprocal critical indices below q² are both q on the original graph. -/
theorem Input.original_small_critical_indices_eq_field
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hsmall : (Q R z).relIndex (Z R a) < Nat.card F ^ 2) :
    (Q R z).relIndex (Z R a) = Nat.card F ∧
      (Q R a).relIndex (Z R z) = Nat.card F := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := (QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm
  let C := K.map q
  let : C.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _) hk) (K.map q)
  obtain ⟨Fe,hFe,ee,hee,je,hje,hjre,κe,hκe,hκeQ,hκeC,hκeL,hψe,hsemie,hconje,hproje,hkere⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  obtain ⟨Fa,hFa,ea,hea,ja,hja,hjra,κa,hκa,hκaQ,hκaC,hκaL,hψa,hsemia,hconja,hproja,hkera⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFec : Nat.card Fe.Carrier = Nat.card F := by rw [Fe.card_eq,hFe,h.field_card]
  have hFac : Nat.card Fa.Carrier = Nat.card F := by rw [Fa.card_eq,hFa,h.field_card]
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δe : Z R a →* (H ⧸ pCore 2 H) := κe.comp (inclusion hAZ)
  let δa : Z R z →* (H ⧸ pCore 2 H) := κa.comp (inclusion hZA)
  have hδecard : Nat.card δe.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κe hκeQ
  have hδacard : Nat.card δa.range = (Q R a).relIndex (Z R z) :=
    quotient_image_card _ _ _ hZA κa hκaQ
  have hδek := restricted_kernel_of_mapped_centralizer (Z R a) (stabilizer R z)
    (Z R z) hAZ κe hκeC
  have hδak := restricted_kernel_of_mapped_centralizer (Z R z) (stabilizer R a)
    (Z R a) hZA κa hκaC
  have hδe : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      je (Multiplicative.ofAdd (s.space.toRepresentation (δe x) v)) =
        (x : FreeAmalgam R) * je (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconje (inclusion hAZ x) v
  have hδa : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      ja (Multiplicative.ofAdd (s.space.toRepresentation (δa x) v)) =
        (x : FreeAmalgam R) * ja (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconja (inclusion hZA x) v
  obtain ⟨πe,hπes,hπe,hπea⟩ := exists_equivariant_embedded_projection
    (U R z) (Z R a) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ee) je hje hjre
    (MovedSection.coverProjection s ee).toLinearMap hee.1
    (MovedSection.coverProjection_ambient s ee) δe hδe
  obtain ⟨πa,hπas,hπa,hπaa⟩ := exists_equivariant_embedded_projection
    (U R a) (Z R z) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ea) ja hja hjra
    (MovedSection.coverProjection s ea).toLinearMap hea.1
    (MovedSection.coverProjection_ambient s ea) δa hδa
  have hedge := MSCentralOrbit.edgeCentralizerCondition R
    (h.radical.isPGroup) (h.radical.twoCore_le) (h.omegaOrbit_centralizer)
  have hcent := (h.component_image_structure).2.2.2.2
  have hFlarge : 2 < Nat.card F := by
    rw [h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
  have hindices := h.original_critical_indices_ge_field path hb
  have hAutE : Nat.card (Fe.Carrier ≃+* Fe.Carrier) = n :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card Fe.Carrier = 2 ^ n by rw [Fe.card_eq,hFe])
  have hAutA : Nat.card (Fa.Carrier ≃+* Fa.Carrier) = n :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card Fa.Carrier = 2 ^ n by rw [Fa.card_eq,hFa])
  let rev : CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry hedge a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  obtain ⟨βe,hβec,hβem,hβe⟩ := critical_inner_model_actor_of_ringAut_card_lt path hb
    (by omega : 2 < Nat.card Fe.Carrier) s ee hee hcent je hje hjre δe hδe (by omega)
  obtain ⟨βa,hβac,hβam,hβa⟩ := critical_inner_model_actor_of_ringAut_card_lt rev hb
    (by omega : 2 < Nat.card Fa.Carrier) s ea hea hcent ja hja hjra δa hδa (by omega)
  let αe : Z R a →* Theory.SpecificGroups.SymplecticFour.Sp Fe.Carrier :=
    (commutator (Theory.SpecificGroups.SymplecticFour.Sp Fe.Carrier)).subtype.comp βe
  let αa : Z R z →* Theory.SpecificGroups.SymplecticFour.Sp Fa.Carrier :=
    (commutator (Theory.SpecificGroups.SymplecticFour.Sp Fa.Carrier)).subtype.comp βa
  have hαek : αe.ker=δe.ker := inner_model_kernel_eq s ee δe βe hβem
  have hαak : αa.ker=δa.ker := inner_model_kernel_eq s ea δa βa hβam
  have hαec : Nat.card αe.range=Nat.card δe.range := by rw [←index_ker,←index_ker,hαek]
  have hαac : Nat.card αa.range=Nat.card δa.range := by rw [←index_ker,←index_ker,hαak]
  have hacte : ∀ (x : Z R a) (u : U R z),
      πe ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path x.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (αe x • (πe u).toAdd) := by
    intro x u
    rw [hπea,ambient_marking_inner_apply s ee δe βe hβem]
    rfl
  have hacta : ∀ (x : Z R z) (u : U R a),
      πa ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path x.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (αa x • (πa u).toAdd) := by
    intro x u
    rw [hπaa,ambient_marking_inner_apply s ea δa βa hβam]
    rfl
  have hh := critical_small_inner_actor_card_field_of_fields
    path hb hedge (hFec.trans hFac.symm) πe hπes πa hπas αe αa
    (hαek.trans hδek) (hαak.trans hδak) hacte hacta (by rwa [hαec,hδecard,hFec])
  exact ⟨by rw [←hδecard,←hαec]; exact hh.1.trans hFec,
    by rw [←hδacard,←hαac]; exact hh.2.1.trans hFec⟩


/-- An actual escaping actor excludes the large critical image on the original graph. -/
theorem Input.original_critical_index_lt_square_of_escape
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ :
      Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅Z R a,Z R z⁆) :
    (Q R z).relIndex (Z R a) < Nat.card F ^ 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hFc : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hcard : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hAut : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card δ.range := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE]),hcard]
    have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
    exact hdeg.trans_le (h.original_critical_indices_ge_field path hb).1
  have hcent := (h.component_image_structure).2.2.2.2
  obtain ⟨β,hβcard,hβmark,hβ⟩ := critical_inner_model_actor_of_ringAut_card_lt
    path hb hFl s e he hcent j hj hjr δ hδ hAut
  apply Nat.lt_of_not_ge
  intro hlarge
  exact critical_large_actor_excluded_of_escape path hb Y hYZ hFl s e he hcent
    j hj hjr κ hκC hκL hconj β hβmark hker hcentral hbad
    (by rwa [hβcard,hcard,hFc])

/-- Seed-join escape forces both literal critical indices to equal the field size. -/
theorem Input.original_critical_indices_eq_field_of_seed_escape
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z) (hYQ : Y ≤ Q R a)
    (hn : ¬ Z R z ≤ normalizer ((Y ⊔ Z R a :
      Subgroup (FreeAmalgam R)) : Set _)) :
    (Q R z).relIndex (Z R a) = Nat.card F ∧
      (Q R a).relIndex (Z R z) = Nat.card F := by
  have hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ :
      Subgroup (FreeAmalgam R)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color)))).trans
      (centralizer_le (critical_commutator_le_start_seed path))
  exact h.original_small_critical_indices_eq_field path hb
    (h.original_critical_index_lt_square_of_escape path hb Y hYZ hcentral
      (critical_escape_of_seed_join_nonnormalization path Y hn))


/-- Every endpoint actor containing an escaping seed has fixed index at least q
on the full critical intersection. All natural-action and root premises are constructed. -/
theorem Input.original_seed_actor_centralizer_index_ge_field
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z) (hYQ : Y ≤ Q R a)
    (hn : ¬ Z R z ≤ normalizer ((Y ⊔ Z R a :
      Subgroup (FreeAmalgam R)) : Set _))
    (D : Subgroup (FreeAmalgam R)) (hYD : Y ≤ D) (hDZ : D ≤ stabilizer R z) :
    Nat.card F ≤ (centralizer (D : Set (FreeAmalgam R))).relIndex
      (Z R z ⊓ Q R a) := by
  obtain ⟨hz,ha⟩ := h.original_critical_indices_eq_field_of_seed_escape path hb Y hYZ hYQ hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hFc : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAut : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card E.Carrier := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE]),E.card_eq,hE]
    exact n.lt_two_pow_self
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (hz.trans hFc.symm)
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := C_eq_Q R (h.radical.isPGroup)
    (h.radical.twoCore_le) (h.omegaOrbit_centralizer) a path.start_color
  have hcent := (h.component_image_structure).2.2.2.2
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor_of_field path hb hCa hFl
    s e he hcent j hj hjr δ hδ hδcard (ha.trans hFc.symm) hAut
  have hmove : ¬ Y ≤ centralizer ((Z R z ⊓ Q R a :
      Subgroup (FreeAmalgam R)) : Set _) := by
    intro hfix
    exact critical_escape_of_seed_join_nonnormalization path Y hn
      (critical_seed_displacement_le_of_fixed_intersection path hb hCa hFl
        s e he hcent j hj hjr κ hκC hconj β hAZ hβmark hβ hd hβcard Y hYZ hfix)
  rw [←hFc]
  exact field_card_le_critical_intersection_centralizer_index path hb hCa hFl
    s e he hsemi hcent j hj hjr κ hκC hconj β hAZ hβmark hβ hd hβcard
    D hDZ (fun hfix => hmove (hYD.trans hfix))



theorem Input.original_exists_critical_escape
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {a u t e : Vertex R} (ha : color R a = false)
    (hu : color R u = false)
    (hat : Adjacent R a t) (hut : Adjacent R u t)
    (hcrit : CriticalPair R a e (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hYU : Y ≤ U R u)
    (hcard : Nat.card Y ≤ Nat.card F ^ 2)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a)
    (hYn : Q R t ≤ normalizer (Y : Set (FreeAmalgam R))) :
    ∃ g ∈ stabilizer R a,
      ¬ Z R e ≤ normalizer
        ((Y ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hstr := h.component_image_structure
  let : ((pResidual 2 H).map q).Normal := by
    rw [h.residual_eq]
    exact hstr.2.1
  let : IsSimpleGroup ((pResidual 2 H).map q) := by
    rw [h.residual_eq]
    exact hstr.2.2.1
  let : IsQuasisimple ((pResidual 2 H).map q) := by
    rw [h.residual_eq]
    exact hstr.2.2.2.1
  have hcent : centralizer ((pResidual 2 H).map q : Set (H ⧸ pCore 2 H)) = ⊥ := by
    rw [h.residual_eq]
    exact hstr.2.2.2.2
  have hgen : pResidual 2 H ⊔ R = ⊤ := by
    rw [h.residual_eq]
    apply top_unique
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := h.product x
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hcardS : Nat.card ((pResidual 2 H).map q) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F) := by
    rw [h.residual_eq]
    exact h.component_image_card_sp
  exact exists_critical_escape_of_bad_symplectic_seed R
    (h.radical.isPGroup) (h.radical.twoCore_le) hgen q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcent
    (by have := h.nonbinary; omega) h.field_card hcardS geometry hb
    (MSCentralOrbit.edgeCentralizerCondition R (h.radical.isPGroup)
      (h.radical.twoCore_le) (h.omegaOrbit_centralizer))
    ha hu hat hut hcrit Y hYU hcard hbad hYn


theorem Input.original_bad_star_critical_seed
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hbad : ¬ ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ ≤ Z R (alpha R)) :
    ∃ d t : Vertex R, ∃ P' : Sylow 2 (Ltilde R d),
      color R d=false ∧ Adjacent R (alpha R) t ∧ Adjacent R d t ∧
      Q R t ≤ normalizer (componentSylowSeed R d P' : Set (FreeAmalgam R)) ∧
      componentSylowSeed R d P' ≤ sourceStarAlpha R Y ∧
      ¬ Z R z ≤ normalizer ((componentSylowSeed R d P' ⊔ Z R (alpha R) :
        Subgroup (FreeAmalgam R)) : Set _) := by
  obtain ⟨g,hH,hbadSeed⟩ := exists_bad_transported_seed R Y hbad
  let A := ((Y.map (embedS R)).map (MulAut.conj (hH : FreeAmalgam R)).toMonoidHom).map
    (MulAut.conj (g : FreeAmalgam R)).toMonoidHom
  let d := act R (g : FreeAmalgam R)⁻¹ (act R (hH : FreeAmalgam R)⁻¹ (alpha R))
  let t := act R (g : FreeAmalgam R)⁻¹ (beta R)
  obtain ⟨P',hP',hn'⟩ := transported_seed_is_componentSylowSeed R Y P hY hn g hH
  have hA : A=componentSylowSeed R d P' := hP'
  have hd : color R d=false := by simp only [d,action_preserves_color]; rfl
  have hAU : A ≤ U R d := hA.le.trans inf_le_left
  have hAn : Q R t ≤ normalizer (A : Set (FreeAmalgam R)) := by rw [hA]; exact hn'
  have hcard : Nat.card A ≤ Nat.card F ^ 2 := by
    rw [hA]
    exact OriginalStar.componentSylowSeed_card_le h hd P'
  have hAstar : A ≤ sourceStarAlpha R Y := by
    have hbeta : (starSpan R Y).map (embedS R) =
        (⨆ k : Hbar R, (Y.map (embedS R)).map (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) ⊔
          Z R (beta R) := by
      simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
    have hYbeta : (Y.map (embedS R)).map (MulAut.conj (hH : FreeAmalgam R)).toMonoidHom ≤
        (starSpan R Y).map (embedS R) := by
      rw [hbeta]
      exact (le_iSup (fun k : Hbar R => (Y.map (embedS R)).map
        (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) hH).trans le_sup_left
    exact (map_mono hYbeta).trans ((sourceStarAlpha_le_iff R Y _).mp le_rfl g)
  obtain ⟨hat,hdt⟩ := transported_seed_edges R g hH
  obtain ⟨k,hk,hnk⟩ := h.original_exists_critical_escape geometry hb
    rfl hd hat hdt path.critical A hAU hcard hbadSeed hAn
  let A' := A.map (MulAut.conj k⁻¹).toMonoidHom
  have hkstar : (sourceStarAlpha R Y).map (MulAut.conj k⁻¹).toMonoidHom =
      sourceStarAlpha R Y := mem_normalizer_iff_map_conj_eq.mp
        (sourceStarAlpha_normalized R Y ((stabilizer R (alpha R)).inv_mem hk))
  have hkZ : (Z R (alpha R)).map (MulAut.conj k⁻¹).toMonoidHom = Z R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R)
      ((stabilizer R (alpha R)).inv_mem hk))
  have hA'star : A' ≤ sourceStarAlpha R Y := (map_mono hAstar).trans_eq hkstar
  have hnjoin : ¬ Z R z ≤ normalizer ((A' ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) : Set _) := by
    simpa only [Subgroup.map_sup,hkZ] using hnk
  obtain ⟨P'',hP''⟩ := exists_componentSylowSeed_act R d P' k
  have hAA : A'=componentSylowSeed R (act R k d) P'' := by
    change A.map (MulAut.conj k⁻¹).toMonoidHom = _
    rw [hA]
    exact hP''.symm
  have hka : act R k (alpha R)=alpha R := hk
  have hat' : Adjacent R (alpha R) (act R k t) := by
    simpa only [hka] using (adjacent_act_iff R k (alpha R) t).mpr hat
  have hdt' : Adjacent R (act R k d) (act R k t) :=
    (adjacent_act_iff R k d t).mpr hdt
  have hn' := map_seed_normalized_at_act R A hAn k
  change Q R (act R k t) ≤ normalizer (A' : Set (FreeAmalgam R)) at hn'
  rw [hAA] at hn'
  refine ⟨act R k d,act R k t,P'',(action_preserves_color R k d).trans hd,
    hat',hdt',hn',?_,?_⟩
  · exact hAA ▸ hA'star
  · exact hAA ▸ hnjoin



/-- The full fixed-Sylow seed has elementary-action centralizer index at
most the original field degree. -/
theorem Input.original_elementary_seed_index_le_degree
    {u : Vertex R} (hu : color R u = false)
    (P : Sylow 2 (Ltilde R u))
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R u)
    (hn : A ≤ normalizer (componentSylowSeed R u P : Set (FreeAmalgam R)))
    (hsquare : ∀ a ∈ A, a*a=1) :
    (centralizer (componentSylowSeed R u P : Set (FreeAmalgam R))).relIndex A ≤ n := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let : B.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm)) B
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex hu
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hbound := elementary_seed_actor_index_le_ringAut hFl s e he j hj hjr κ hκL
    (h.component_image_structure).2.2.2.2 hsemi hconj P A hA hn hsquare
  rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
    (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE])] at hbound


/-- An escaping seed from a bad source star contradicts the exact lower and
upper action indices on the full endpoint intersection. -/
theorem Input.original_no_escaping_star_seed
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P₀ : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P₀)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    {u t : Vertex R} (hu : color R u = false)
    (hat : Adjacent R (alpha R) t) (hut : Adjacent R u t)
    (P : Sylow 2 (Ltilde R u))
    (hnP : Q R t ≤ normalizer (componentSylowSeed R u P : Set (FreeAmalgam R)))
    (hs : componentSylowSeed R u P ≤ sourceStarAlpha R Y)
    (he : ¬ Z R z ≤ normalizer
      ((componentSylowSeed R u P ⊔ Z R (alpha R) :
        Subgroup (FreeAmalgam R)) : Set _)) : False := by
  let E := Z R z ⊓ Q R (alpha R)
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    change false ≠ color R t at hh
    cases hh' : color R t <;> simp_all
  have hEQ : E ≤ Q R t := inf_le_right.trans (Q_le_adjacent_h R ht hat)
  have hEU : E ≤ stabilizer R u := hEQ.trans (fun _ hx => hx.2 u (adjacent_symm _ hut))
  have hEN : E ≤ normalizer (componentSylowSeed R u P : Set (FreeAmalgam R)) :=
    hEQ.trans hnP
  let : IsElementaryAbelian 2 (Z R z) := geometry.Z_elementary hb z path.end_color
  have hEsquare : ∀ x ∈ E, x*x=1 := by
    intro x hx
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Z R z)) ⟨x,hx.1⟩
    have hx2 : x ^ 2 = 1 := congrArg Subtype.val hh
    simpa only [pow_two] using hx2
  have hup := h.original_elementary_seed_index_le_degree hu P E hEU hEN hEsquare
  have hYS := hs.trans (h.original_sourceStarAlpha_le_critical_endpoint_stabilizer geometry hb path Y P₀ hY hn)
  have hYQ := hs.trans (h.original_sourceStarAlpha_le_own_core geometry hb Y P₀ hY hn)
  have hlo := h.original_seed_actor_centralizer_index_ge_field path hb
    (componentSylowSeed R u P) hYS hYQ he
    (componentSylowSeed R u P) le_rfl hYS
  change Nat.card F ≤ (centralizer (componentSylowSeed R u P :
    Set (FreeAmalgam R))).relIndex E at hlo
  rw [h.field_card] at hlo
  have hlt := n.lt_two_pow_self
  omega

/-- The first star commutator comparison of MS93 (3.4), on the actual
original radical and at every nonbinary field degree. -/
theorem Input.original_sourceStarAlpha_commutator_le_Z
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ ≤
      Z R (alpha R) := by
  by_contra hbad
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := geometry)
    (a := alpha R) rfl
  obtain ⟨u,t,P',hu,hat,hut,hnP,hs,he⟩ :=
    h.original_bad_star_critical_seed geometry hb path Y P hY hn hbad
  exact h.original_no_escaping_star_seed geometry hb path Y P hY hn hu hat hut P' hnP hs he

/-- Coprime residual idempotence sharpens the first star bound to the literal
moving natural cover; the full fixed part is not removed from that cover. -/
theorem Input.original_sourceStarAlpha_commutator_le_U
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ ≤
      U R (alpha R) := by
  let S := stabilizer R (alpha R)
  let A := (sourceStarAlpha R Y).subgroupOf S
  let : Finite S := finite_stabilizer R (alpha R)
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sourceStarAlpha_normalized R Y)
  have hPQ : IsPGroup 2 (Q R (alpha R)) := by
    rw [Q_alpha R (h.radical.isPGroup) (h.radical.twoCore_le)]
    exact pCore_isPGroup.map _
  have hPA : IsPGroup 2 A := (hPQ.to_le
    (h.original_sourceStarAlpha_le_own_core geometry hb Y P hY hn)).comap_subtype
  have hi := commutator_isPPerfect_idempotent (pResidual 2 S) A
    (isPPerfect_pResidual 2) hPA le_normalizer_of_normal
  have hmap := congrArg (Subgroup.map S.subtype) hi
  have hAm : A.map S.subtype = sourceStarAlpha R Y :=
    map_subgroupOf_eq_of_le (sourceStarAlpha_le_stabilizer R Y)
  simp only [map_commutator,hAm] at hmap
  change ⁅⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆,
    Ltilde R (alpha R)⁆ =
    ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ at hmap
  rw [←hmap]
  exact commutator_mono (h.original_sourceStarAlpha_commutator_le_Z geometry hb Y P hY hn) le_rfl

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
