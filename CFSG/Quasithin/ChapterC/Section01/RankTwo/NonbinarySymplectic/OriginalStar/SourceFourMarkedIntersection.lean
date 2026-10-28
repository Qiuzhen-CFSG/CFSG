module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourRootSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourMarkedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourComplement

/-!
# The marked movement intersection for the original radical

The actual plane marking determines the same full hyperplane and section
centralizer. Their factorization and exact orders discharge the root
selection premises. In the escaping unequal-attachment branch, the first
complete attachment is exactly the intersection of the two movements.

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

omit hshort hinner hnsyl in
/-- The section centralizer of a marked full hyperplane has field index in
 the common plane radical. The original cover and arbitrary marking are retained. -/
theorem plane_cover_hyperplane_section_index
    {z t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (k : Sp cv.field.Carrier)
    (hk : ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (P B : Subgroup (FreeAmalgam R)) (hP : P ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (U R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hfix : ∀ w : (originalMovedSection h).space.toSubmodule,
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam R)) ↔
        (k • MovedSection.coverProjection (originalMovedSection h) cv.equiv w) (.inr 0)=0)
    (hmem : ∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧
      ∀ x ∈ U R z ⊓ centralizer (P : Set (FreeAmalgam R)),
        ⁅b,x⁆ ∈ ⁅P,U R z⁆) : B.relIndex (Q R t)=2^n := by
  have hc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  simpa only [cv.range_eq,hc] using SaturatedDistanceTwo.marked_section_index hlarge
    (MovedSection.coverProjection (originalMovedSection h) cv.equiv) cv.cover
    cv.embedding cv.injective (Q R t) cv.actor cv.actor_conjugation k hk P B hP
    (by simpa only [cv.range_eq] using hpoint) hfix (by simpa only [cv.range_eq] using hmem)

private theorem marked_hyperplane_geometry
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P B : Subgroup (FreeAmalgam R))
    (hmarked : HasOriginalMarkedHyperplane h z t P B) :
    let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
    let H₀ := ⁅Z R z,P⁆
    let A₀ := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    Q R z ≤ P ∧ P ≤ Q R t ∧ B ≤ Q R t ∧
      P=Q R t ⊓ centralizer (X : Set (FreeAmalgam R)) ∧
      X.relIndex (Z R z)=2^n ∧
      Z R t ≤ X ∧ ⁅Z R a,Z R z⁆ ≤ X ∧
      (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam R))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z R a,Z R z⁆ ∧ B.relIndex (Q R t)=2^n := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  obtain ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩ := hmarked
  obtain ⟨P₀,B₀,hP₀,hB₀,hpoint₀,hindex,hfix₀,hmem₀,hdis,hcard,hjoin⟩ :=
    original_plane_cover_hyperplane_attachment h cv k hk
  have hXeq : U R z ⊓ centralizer (P₀ : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (P : Set (FreeAmalgam R)) := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfix w.toAdd).mpr ((hfix₀ w.toAdd).mp hc)
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfix₀ w.toAdd).mpr ((hfix w.toAdd).mp hc)
  have hPeq : P₀=P := hpoint₀.trans ((congrArg
    (fun S : Subgroup (FreeAmalgam R) => Q R t ⊓ centralizer (S : Set (FreeAmalgam R))) hXeq).trans hpoint.symm)
  subst P₀
  have hBeq : B₀=B := by
    ext b
    exact (hmem₀ b).trans (hmem b).symm
  subst B₀
  have hBi := plane_cover_hyperplane_section_index h cv k hk P B hP hpoint hfix hmem
  let C := Z R t
  let V := U R z
  let X₀ := V ⊓ centralizer (P : Set (FreeAmalgam R))
  let X₁ := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y := Q R t
  have hgen : Z R z=V ⊔ C :=
    original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt
  have hC : C=omegaCenter Y := by simp [C,Y,Z,ht,edgeOmega]
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam R)) := by
    rw [hC]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hCZ : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have hCU : C ≤ normalizer (V : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam R)) := hCY.trans (centralizer_le hP)
  have hX : X₁=X₀ ⊔ C := by
    dsimp only [X₁,X₀]
    rw [hgen,sup_comm V C,inf_centralizer_sup_of_centralizing C V P hCU hCP,sup_comm]
  have hHZ : ⁅Z R z,P⁆=⁅P,V⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement V C Y P hCU hCY hP
  have hXB : ⁅X₁,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C Y B hCX hCY hB,
      commutator_comm]
  have hpointZ : P=Y ⊓ centralizer (X₁ : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
    · exact (inf_le_inf_left Y (centralizer_le
        (show X₀ ≤ X₁ from hX ▸ le_sup_left))).trans hpoint.ge
  have hQ : Q R z ≤ P := by
    rw [hpointZ]
    apply le_inf (Q_le_adjacent_h R ht hzt)
    exact le_centralizer_iff.mp
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R z path.end_color)))
  have hi : X₁.relIndex (Z R z)=2^n := by
    let := finite_Z R z
    let : Finite X₁ := Finite.of_injective (inclusion (show X₁ ≤ Z R z from inf_le_left))
      (inclusion_injective _)
    have hVX : V ⊔ X₁=Z R z := by
      rw [hX,←sup_assoc,sup_eq_left.mpr (show X₀ ≤ V from inf_le_left),←hgen]
    have hXU : X₁ ≤ normalizer (V : Set (FreeAmalgam R)) :=
      (inf_le_left.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [←hVX,relIndex_sup_of_normalizes V X₁ hXU]
    have hInf : X₁ ⊓ V=X₀ := by
      ext x
      exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨U_le_Z z hx.1,hx.2⟩,hx.1⟩⟩
    rw [←inf_relIndex_right,hInf,inf_relIndex_left]
    exact hindex
  have hCX₁ : C ≤ X₁ := le_inf hCZ hCP
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hcommon : ⁅Z R a,Z R z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)
  refine ⟨hQ,hP,hB,hpointZ,hi,hCX₁,hcommon.trans hCX₁,?_,?_,?_,?_,?_,hBi⟩
  · intro b
    rw [hmem]
    constructor
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      change x ∈ X₁ at hx
      rw [hX,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCX] at hx
      obtain ⟨u,hu,v,hv,rfl⟩ := hx
      have hbv : Commute b v := hCY hv b hb
      rw [hHZ,commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hbv]
      simpa only [mul_one,mul_inv_cancel_right] using hm u hu
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      rw [←hHZ]
      apply hm x
      change x ∈ X₁
      rw [hX]
      exact mem_sup_left hx
  · rw [hXB]
    exact hdis
  · rw [hXB]
    exact hcard
  · rw [hHZ,hXB]
    exact hjoin
  · rw [commutator_comm]
    exact (commutator_mono hP le_rfl).trans_eq
      (original_source_four_large_full_movement h hshort hinner hnsyl g hb path hat hzt hcritical)

private theorem marked_escaping_intersection
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P B : Subgroup (FreeAmalgam R))
    (hmarked : HasOriginalMarkedHyperplane h z t P B)
    (hP : P ≤ Q R t) (hB : B ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hi : (Z R z ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R z)=2^n)
    (hmem : ∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧
      ∀ x ∈ Z R z ⊓ centralizer (P : Set (FreeAmalgam R)), ⁅b,x⁆ ∈ ⁅Z R z,P⁆)
    (hdis : Disjoint ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆
      (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))))
    (hcard : Nat.card (⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆ :
      Subgroup (FreeAmalgam R))=2^n)
    (hjoin : ⁅Z R z,P⁆ = ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆ ⊔
      (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))))
    (hR : ⁅Z R z,P⁆ ≤ ⁅Z R a,Z R z⁆)
    (hBi : B.relIndex (Q R t)=2^n)
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z) :
    U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) =
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ⊓
        ⁅Z R z,P⁆ := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let D := ⁅Z R a,Z R z⁆
  let M := ⁅X,Z R a⁆
  let A := ⁅X,B⁆
  have hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n := by
    by_contra hn
    exact hne (original_source_four_large_escaping_small_attachment_eq h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape hn)
  have hfull' := (original_source_four_large_attachment_card_eq h hshort hinner hnsyl g hb path hat hzt hcritical).symm.trans hfull
  have hn := original_source_four_large_escaping_not_le_hyperplane h hshort hinner hnsyl g hb path hat hzt
    hcritical P B hP hpoint hi hmem hcard hne hescape
  have hZaT : Z R a ≤ Q R t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hat))
  have he : Z R a ⊓ B=Z R a ⊓ centralizer (X : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro u ⟨hu,hbB⟩
      refine ⟨hu,?_⟩
      apply (original_source_four_large_full_section_centralizer h hshort hinner hnsyl g hb path hat hzt
        hcritical P hP hpoint hi hescape hfull hn u hu).mp
      intro x hx
      rw [←commutatorElement_inv]
      exact inv_mem (((hmem u).mp hbB).2 x hx)
    · rintro u ⟨hu,hc⟩
      refine ⟨hu,(hmem u).mpr ⟨hZaT hu,?_⟩⟩
      intro x hx
      rw [commutatorElement_eq_one_iff_commute.mpr (hc x hx).symm]
      exact one_mem _
  have hBZ : B.relIndex (Z R a)=2^n := by
    rw [←inf_relIndex_left,he]
    exact (original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).1
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R z from fun _ hx => hx.2 _ (adjacent_symm R hzt))) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion hB) (inclusion_injective _)
  have hnorm : B ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    hB.trans ((show Q R t ≤ stabilizer R a from fun _ hx => hx.2 _ (adjacent_symm R hat)).trans (Z_normalized R a))
  have hJ : Z R a ⊔ B ≤ Q R t := sup_le hZaT hB
  have hfactor : Q R t=Z R a ⊔ B := by
    have hh := relIndex_mul_relIndex B (Z R a ⊔ B) (Q R t) le_sup_right hJ
    rw [relIndex_sup_of_normalizes _ _ hnorm,hBZ,hBi] at hh
    have hidx : (Z R a ⊔ B).relIndex (Q R t)=1 := by
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^n) (hh.trans (mul_one _).symm)
    exact le_antisymm (relIndex_eq_one.mp hidx) hJ
  have hXD : ⁅X,Q R t⁆=D :=
    original_source_four_large_hyperplane_full_movement h hshort hinner hnsyl g hb path hat hzt hcritical P hP hi
  have hMD : M ≤ D := (commutator_mono le_rfl hZaT).trans_eq hXD
  have hAD : A ≤ D := (commutator_mono le_rfl hB).trans_eq hXD
  have hDC : D ≤ Z R t := by
    change ⁅Z R a,Z R z⁆ ≤ Z R t
    rw [commutator_comm]
    exact (commutator_mono le_rfl ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _))).trans (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)
  have hDT : D ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    apply hDC.trans
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hsup : D=M ⊔ A := by
    apply le_antisymm ?_ (sup_le hMD hAD)
    rw [←hXD]
    apply commutator_le.mpr
    intro x hx b hbT
    rw [hfactor,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hbT
    obtain ⟨u,hu,v,hv,rfl⟩ := hbT
    have hxv : ⁅x,v⁆ ∈ A := commutator_mem_commutator hx hv
    have hh := hDT (hAD hxv) u (hZaT hu)
    rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅x,u⁆ u ⁅x,v⁆,hh,
      ←mul_assoc ⁅x,u⁆ ⁅x,v⁆ u,mul_inv_cancel_right]
    exact (M ⊔ A).mul_mem (mem_sup_left (commutator_mem_commutator hx hu)) (mem_sup_right hxv)
  have hMc : Nat.card M=(2^n)^2 := by
    have hh := (original_source_four_large_escaping_movement h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  have hDc : Nat.card D=(2^n)^3 := by
    rw [(original_source_four_large_displacement_order h hshort hinner hnsyl g hb path hat hzt hcritical).2.2,hfull']
    exact (pow_succ (2^n) 2).symm
  have hDA : Disjoint M A := by
    have hDZ : D ≤ Z R z := hDC.trans (Sp4Four.edge_Z_le_endpoint R path.end_color hzt)
    let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
    have hAM : A ≤ normalizer (M : Set (FreeAmalgam R)) :=
      (hAD.trans hDZ).trans ((Z R z).le_centralizer.trans (centralizer_le (hMD.trans hDZ)))
        |>.trans (Subgroup.centralizer_le_normalizer _)
    have hh := SaturatedDistanceTwo.subgroup_product_card M A hAM
    rw [hMc,hcard,←hsup,hDc,←pow_succ] at hh
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2^n)^3)
    simpa only [one_mul] using hh.symm
  let A₀ := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  let N := ⁅Z R z,P⁆
  have hDZ : D ≤ Z R z := hDC.trans
    (Sp4Four.edge_Z_le_endpoint R path.end_color hzt)
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hA₀A : A₀ ≤ normalizer (A : Set (FreeAmalgam R)) :=
    (inf_le_left.trans (U_le_Z z)).trans
      ((Z R z).le_centralizer.trans (centralizer_le (hAD.trans hDZ))) |>.trans
        (Subgroup.centralizer_le_normalizer _)
  have hNc : Nat.card N=(2^n)^2 := by
    change Nat.card (⁅Z R z,P⁆ : Subgroup (FreeAmalgam R))=_
    rw [hjoin,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hA₀A hdis,hcard,hfull',pow_two]
  have hNM : N ≤ normalizer (M : Set (FreeAmalgam R)) :=
    (hR.trans hDZ).trans ((Z R z).le_centralizer.trans (centralizer_le (hMD.trans hDZ)))
      |>.trans (Subgroup.centralizer_le_normalizer _)
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hDc]; positivity)
  have hmeet : (M ⊓ N : Subgroup (FreeAmalgam R)) ≠ ⊥ := by
    intro hbot
    have hp := SaturatedDistanceTwo.subgroup_product_card M N hNM
    rw [hMc,hNc,hbot,Subgroup.card_bot,one_mul] at hp
    have hc := Nat.card_le_card_of_injective (inclusion (sup_le hMD hR)) (inclusion_injective _)
    rw [hDc,←hp] at hc
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    have hlt : (2^n)^3 < (2^n)^2*(2^n)^2 := by
      calc
        (2^n)^3 < (2^n)^4 := Nat.pow_lt_pow_right hq (by decide)
        _ = (2^n)^2*(2^n)^2 := by ring
    exact hlt.not_ge hc
  have hle : A₀ ≤ M := original_source_four_large_marked_attachment_le h hshort hinner hnsyl g hb path hat hzt hcritical P B hmarked hi hescape hfull hNc hn hmeet hDA
  apply le_antisymm (le_inf hle (hjoin ▸ le_sup_right))
  rintro x ⟨hxM,hxN⟩
  change x ∈ ⁅Z R z,P⁆ at hxN
  rw [hjoin,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hA₀A] at hxN
  obtain ⟨b,hbA,a₀,ha₀,rfl⟩ := hxN
  have hbM : b ∈ M := by
    simpa only [mul_inv_cancel_right] using M.mul_mem hxM (M.inv_mem (hle ha₀))
  have hb1 : b=1 := hDA.le_bot ⟨hbM,hbA⟩
  change b*a₀ ∈ A₀
  rw [hb1,one_mul]
  exact ha₀

/-- For the same marked hyperplane supplied by the full plane cover, all
order, intersection and complement premises of root selection are consequences
of the original source geometry. In the escaping unequal-attachment branch,
the entire attachment is exactly the intersection of the two movements. -/
theorem original_source_four_large_marked_attachment_intersection
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (P B : Subgroup (FreeAmalgam R))
    (hmarked : HasOriginalMarkedHyperplane h z t P B)
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z) :
    U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) =
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ⊓
        ⁅Z R z,P⁆ := by
  obtain ⟨hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    marked_hyperplane_geometry h hshort hinner hnsyl g hb path hat hzt hcritical P B hmarked
  exact marked_escaping_intersection h hshort hinner hnsyl g hb path hat hzt hcritical
    P B hmarked hP hB hpoint hi hmem hdis hcard hjoin hR hBi hne hescape

/-- The preceding plane geometry constructs the marked source hyperplane;
no comparison or intersection hypothesis is included in that construction. -/
theorem original_source_four_large_unequal_marked_intersection
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
    ∃ P B : Subgroup (FreeAmalgam R),
      let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
      let H₀ := ⁅Z R z,P⁆
      let A₀ := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
      HasOriginalMarkedHyperplane h z t P B ∧ Q R z ≤ P ∧ P ≤ Q R t ∧ B ≤ Q R t ∧
      P=Q R t ⊓ centralizer (X : Set (FreeAmalgam R)) ∧
      X.relIndex (Z R z)=2^n ∧
      Z R t ≤ X ∧ ⁅Z R a,Z R z⁆ ≤ X ∧
      (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam R))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z R a,Z R z⁆ ∧ B.relIndex (Q R t)=2^n ∧
      (¬ Z R a ⊓ centralizer (X : Set (FreeAmalgam R)) ≤ Q R z →
        A₀=⁅X,Z R a⁆ ⊓ H₀) := by
  obtain ⟨⟨cv⟩,_,_,_⟩ := original_source_four_large_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨k,hk⟩ := cv.plane_image
  obtain ⟨P,B,hP,hB,hpoint,_,hfix,hmem,_⟩ := original_plane_cover_hyperplane_attachment h cv k hk
  have hm : HasOriginalMarkedHyperplane h z t P B := ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩
  obtain ⟨hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    marked_hyperplane_geometry h hshort hinner hnsyl g hb path hat hzt hcritical P B hm
  refine ⟨P,B,hm,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,?_⟩
  exact original_source_four_large_marked_attachment_intersection h hshort hinner hnsyl g hb path hat hzt
    hcritical hne P B hm


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
