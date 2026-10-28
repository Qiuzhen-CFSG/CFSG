module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.Midpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceThreeContained
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreePlane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreePlane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# Original Sylow core containment and whole-core decomposition

If the first full core escaped Z Q', source (2) would force the opposite
full radical action to fill a plane radical. That action has order q cubed,
contradicting the literal original Sylow order q to the fourth. The original
contained-core argument then gives Q = U D, X = Z and both overlap indices q.

Source: MS93 (3.7)(3), printed pp.873--874. The private imports deliberately
reuse generic symplectic plane geometry and the original full-cover setup.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- Noncontainment forces the full original edge action to be a plane radical. -/
private theorem noncontained_plane_cover
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    Nonempty (SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t) ∧
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex
        (U R z)=(2^n)^2 ∧
      (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
        (U R z)=(2^n)^2 := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hCtop : (K.map (QuotientGroup.mk' (pCore 2 H))) = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict ((K.map (QuotientGroup.mk' (pCore 2 H)))) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let β := γ.comp (inclusion hTSz)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hact (u : Q R t) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hTSz u)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hTSz u) w
  have hαker : α.ker = (Q R z).subgroupOf (Q R t) := by
    have hkκ : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [α,β,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hFc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans hQaT
  let βA := β.comp (inclusion hQaT)
  let αA := (commutator (Sp E.Carrier)).subtype.comp βA
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans hTSz
  let δ := κ.comp (inclusion hZaS)
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [h.field_card,hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  rw [h.field_card] at hother
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer a path.start_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβmark (u : Q R t) : (e.groupEquiv.symm (β u) : _) =
      κ (inclusion hTSz u) :=
    congrArg Subtype.val (e.groupEquiv.symm_apply_apply (κC (inclusion hTSz u)))
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    have hr : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
      rw [MonoidHom.range_comp,hβZ]
    rw [hr]
    exact hηdim
  have hZcard : Nat.card αZ.range=Nat.card E.Carrier := by
    rw [MonoidHom.range_comp,hβZ,card_map_of_injective
      (commutator (Sp E.Carrier)).subtype_injective,hηcard]
  have hAT : αA.range ≤ α.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hQaT y,rfl⟩
  have hZA : αZ.range ≤ αA.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hZaQ y,rfl⟩
  have hnot' : ¬ αA.range ≤ αZ.range := by
    intro hh
    apply hnot
    intro x hx
    obtain ⟨y,hy⟩ := hh (show αA ⟨x,hx⟩ ∈ αA.range from ⟨⟨x,hx⟩,rfl⟩)
    let u : Q R t := inclusion hQaT ⟨x,hx⟩ * (inclusion hZaT y)⁻¹
    have hu : u ∈ α.ker := by
      change α u=1
      dsimp only [u]
      rw [map_mul,map_inv]
      change αA ⟨x,hx⟩ * (αZ y)⁻¹=1
      rw [hy,mul_inv_cancel]
    have hq : x*y.val⁻¹ ∈ Q R z :=
      show u ∈ (Q R z).subgroupOf (Q R t) from hαker ▸ hu
    have hh := (Z R a ⊔ Q R z).mul_mem
      (mem_sup_right hq) (mem_sup_left y.property)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcomm : ⁅U R z,Q R a⁆ ≤
      centralizer (Q R t : Set (FreeAmalgam R)) := by
    apply ((commutator_mono (U_le_Z z) le_rfl).trans
      (original_source_two_midpoint_containment h hshort hinner hsyl g hb path hat hzt)).trans
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfix := embedded_displacement_fixed (MovedSection.coverProjection s e) he
    (U R z) (Q R t) (Q R a) hQaT
    j hj hjr β hact hcomm
  obtain ⟨hAdim,hfixed,hTdisp⟩ := plane_of_root_escape α.range αA.range αZ.range
    hAT hZA hZdim hZcard hfix hnot'
  have hquad : ∀ x ∈ αA.range, ∀ y ∈ αA.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp αA.range.subtype) ⟨y,hy⟩ v) x (hAT hx)
  have hcard : Nat.card E.Carrier^3 ≤ Nat.card α.range := by
    rw [←index_ker,hαker]
    change Nat.card E.Carrier^3 ≤ (Q R z).relIndex (Q R t)
    rw [original_sylow_full_radical_card h hinner hsyl path.end_color hzt,hFc]
    exact Nat.pow_le_pow_right (by positivity) (by decide : 3≤4)
  have hp := plane_radical_of_fixed_plane α.range (displacementSpace αA.range)
    hAdim (quadratic_displacement_isotropic αA.range hquad) hfix hcard
  refine ⟨⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
             edge_le := hTSz
             actor := β
             actor_marking := hβmark
             actor_conjugation := hact
             actor_kernel := hαker
             plane_image := hp }⟩,?_,?_⟩
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U R z) (Q R a) j hj hjr βA
        (fun u w => hact (inclusion hQaT u) w),hAdim,hFc]
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U R z) (Q R t) j hj hjr β hact,hTdisp,hAdim,hFc]


/-- The full original Sylow branch is contained; its plane-escape alternative
would have the wrong original marked order. All complete cores are retained. -/
theorem original_source_three_of_full_sylow
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    Q R a ≤ Z R a ⊔ Q R z ∧
      Q R a=U R a ⊔ fixedCore R a ∧
      X R a=Z R a ∧
      (Z R z).relIndex (Z R a)=2^n ∧
      (Z R a).relIndex (Z R z)=2^n := by
  have hcritical := (original_critical_indices_eq_field_of_full_sylow
    h hshort hinner hsyl path hb hat hzt).1
  have hinside : Q R a ≤ Z R a ⊔ Q R z := by
    by_contra hn
    obtain ⟨⟨cv⟩,_⟩ := noncontained_plane_cover h hshort hinner hsyl
      g hb path hat hzt hcritical hn
    have hc := cv.radical_index
    rw [original_sylow_full_radical_card h hinner hsyl path.end_color hzt] at hc
    have hq : 1<2^n := one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
    exact (Nat.pow_lt_pow_right hq (by decide : 3<4)).ne hc.symm
  obtain ⟨hQ,hX⟩ := original_source_three_contained_core
    h hshort hinner path (by omega) hat hcritical hinside
  exact ⟨hinside,hQ,hX,original_source_three_contained_core_overlap
    h hshort hinner path hb hat hzt hcritical hinside⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
