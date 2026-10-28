module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceThree
public import Theory.Representation.SymplecticFourOrthogonalCover.RootTranslations
public import Theory.GroupTheory.NormalizedSupCard
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# Full fixed-kernel comparison in the original critical graph

Individual critical commutators lying in a component-fixed attachment vanish
by fixed-vector lifting on the full natural cover. The root-value and
translation calculations therefore force the two attachments either to agree
or to be disjoint of order q, with product the whole critical displacement.
All actions and full covering kernels belong to the original radical.

These are the commutator-value steps of MS93 (3.7)(4), printed p.875.
The companion SourceFourEquality excludes the unequal case for the original
nonsylow star using the common overlap and the cubic marked radical action.
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
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- Fixed-vector lifting kills an individual critical commutator in the
entire component-fixed attachment. -/
theorem original_critical_value_in_fixed_eq_one
    (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (_hb : g.b R = 2)
    (hat : Adjacent R a t)
    (b : FreeAmalgam R) (hbZ : b ∈ Z R z)
    (u : FreeAmalgam R) (hu : u ∈ U R a)
    (hfix : ⁅b,u⁆ ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) :
    ⁅b,u⁆=1 := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,f,hf,hact,hker⟩ := h.initial_cover_at_vertex path.start_color
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hprod : stabilizer R a = Ltilde R a ⊔ Q R a := by
    obtain ⟨x,rfl⟩ := exists_mVertex_of_color R path.start_color
    have ha : mVertex R x = act R x (alpha R) := by simp [alpha,act_mVertex]
    rw [ha,stabilizer_act,Ltilde_act,Q_act,←Subgroup.map_sup,
      Ltilde_alpha,h.residual_eq,Q_alpha R h.radical.isPGroup h.radical.twoCore_le,
      ←Subgroup.map_sup,hinner]
    simp only [alpha,stabilizer_m_base,Mbar,MonoidHom.range_eq_map]
  have hbprod : b ∈ Ltilde R a ⊔ Q R a := hprod ▸ hZA hbZ
  have hn : Ltilde R a ≤ normalizer (Q R a : Set (FreeAmalgam R)) :=
    (Ltilde_le_stabilizer _).trans (Q_normalized _ _)
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hn] at hbprod
  obtain ⟨l,hl,q,hq,rfl⟩ := hbprod
  have hqu : Commute q u :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color)
      (U_le_Z a hu) q hq)
  have heq : ⁅l*q,u⁆ = ⁅l,u⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hqu]
    simp only [mul_one,mul_inv_cancel,one_mul]
  rw [heq] at hfix ⊢
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨hjr ▸ ⟨w,rfl⟩,(hker w.toAdd).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := hjr.symm ▸ hx
      exact ⟨w,(hker w.toAdd).mpr hc,rfl⟩
  apply embedded_cover_value_in_kernel_eq_one (U R a) (Ltilde R a)
    (MovedSection.coverProjection s e) he j hj hjr f hact l hl u hu
  rw [hk]
  exact ⟨le_normalizer_iff_commutator_le_right.mp
    ((Ltilde_le_stabilizer _).trans (U_normalized a)) (commutator_mem_commutator hl hu),hfix⟩

variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include hshort hinner

/-- If the full fixed kernel is smaller than the maximal orthogonal kernel,
every element of the critical displacement outside it is an individual
commutator of the two actual moving groups. -/
theorem original_critical_paired_commutator_value
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hsmall : Nat.card (↥(U R a ⊓
      centralizer (Ltilde R a : Set (FreeAmalgam R)))) ≠ 2^n)
    (x : FreeAmalgam R) (hx : x ∈ ⁅Z R a,Z R z⁆)
    (hn : x ∉ U R a ⊓
      centralizer (Ltilde R a : Set (FreeAmalgam R))) :
    ∃ b ∈ U R z, ∃ u ∈ U R a, ⁅b,u⁆=x := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  rw [h.field_card] at haq hzq
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  let p := MovedSection.coverProjection s e
  have hs : Nat.card p.toLinearMap.ker ≠ Nat.card E.Carrier := by
    rw [←embedded_cover_kernel_card p j hj,hk,hFc]
    exact hsmall
  have hx' : x ∈ ⁅Z R z,U R a⁆ := by
    rw [commutator_comm,←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact hx
  obtain ⟨b,hbZ,u,hu,he⟩ := embedded_root_value_of_kernel_card_ne hcard
    (U R a) (Z R z) p he j hjr β hβ hβcard hβdim hβquad hs
    x hx' (by rwa [hk])
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have htz : Z R t ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have hta : Z R t ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have hcent : Z R t ≤ centralizer (U R z : Set (FreeAmalgam R)) :=
    htz.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))
  have hbjoin : b ∈ U R z ⊔ Z R t := by
    rwa [←original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
    (hcent.trans (Subgroup.centralizer_le_normalizer _))] at hbjoin
  obtain ⟨v,hv,w,hw,rfl⟩ := hbjoin
  have hwu : Commute w u :=
    ((hta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))) hw u hu).symm
  refine ⟨v,hv,u,hu,?_⟩
  rw [commutatorElement_mul_left_eq_conj_mul,commutatorElement_eq_one_iff_commute.mpr hwu] at he
  simpa only [mul_one,mul_inv_cancel,one_mul] using he

/-- The two full fixed kernels agree unless both have the full field order.
The exceptional full orthogonal-cover case remains explicit. -/
theorem original_critical_fixed_kernels_eq_or_full
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    A=A' ∨ Nat.card A=2^n ∧ Nat.card A'=2^n := by
  classical
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  obtain ⟨_,hcontain,_,_,hcard⟩ := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical
  by_cases hfull : Nat.card A=2^n
  · exact Or.inr ⟨hfull,hcard.symm.trans hfull⟩
  left
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hle : A' ≤ A := by
    intro x hx
    by_contra hn
    obtain ⟨b,hbU,u,hu,he⟩ := original_critical_paired_commutator_value h hshort hinner path hb hat hzt hcritical
      hfull x (hcontain (mem_sup_right hx)) hn
    have hc : ⁅u,b⁆ ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
      rw [←commutatorElement_inv,he]
      exact inv_mem hx.2
    have he1 := original_critical_value_in_fixed_eq_one h hinner rev hb hzt
      u (U_le_Z a hu) b hbU hc
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    exact hn (he.symm ▸ he2.symm ▸ A.one_mem)
  let := finite_Z R a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

/-- A nonidentity fixed-kernel translate of an actual critical displacement
is an individual commutator whenever the original element is not one. -/
theorem original_critical_paired_commutator_or_mul
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (x : FreeAmalgam R) (hx : x ∈ ⁅Z R a,Z R z⁆)
    (hn : x ∉ U R a ⊓
      centralizer (Ltilde R a : Set (FreeAmalgam R)))
    (k : FreeAmalgam R)
    (hk : k ∈ U R a ⊓
      centralizer (Ltilde R a : Set (FreeAmalgam R))) (hk0 : k ≠ 1) :
    ∃ b ∈ U R z, ∃ u ∈ U R a, ⁅b,u⁆=x ∨ ⁅b,u⁆=x*k := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  rw [h.field_card] at haq hzq
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hkerImage : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  let p := MovedSection.coverProjection s e
  have hx' : x ∈ ⁅Z R z,U R a⁆ := by
    rw [commutator_comm,←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact hx
  obtain ⟨b,hbZ,u,hu,he⟩ := embedded_root_value_or_mul_kernel hcard
    (U R a) (Z R z) p he j hjr β hβ hβcard hβdim hβquad
    x k hx' (by rwa [hkerImage]) (by rwa [hkerImage]) hk0
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have htz : Z R t ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have hta : Z R t ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have hcent : Z R t ≤ centralizer (U R z : Set (FreeAmalgam R)) :=
    htz.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))
  have hbjoin : b ∈ U R z ⊔ Z R t := by
    rwa [←original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
    (hcent.trans (Subgroup.centralizer_le_normalizer _))] at hbjoin
  obtain ⟨v,hv,w,hw,rfl⟩ := hbjoin
  have hwu : Commute w u :=
    ((hta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))) hw u hu).symm
  refine ⟨v,hv,u,hu,?_⟩
  have hv : ⁅v*w,u⁆=⁅v,u⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,commutatorElement_eq_one_iff_commute.mpr hwu]
    simp only [mul_one,mul_inv_cancel,one_mul]
  simpa only [hv] using he

/-- The complete paired fixed kernels either agree or have trivial intersection. -/
theorem original_critical_fixed_kernels_eq_or_disjoint
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    A=A' ∨ Disjoint A A' := by
  classical
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  obtain ⟨_,hcontain,_,_,hcard⟩ := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical
  by_cases heq : A=A'
  · exact Or.inl heq
  right
  apply disjoint_iff_inf_le.mpr
  intro k hk
  change k=1
  by_contra hk0
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hle : A' ≤ A := by
    intro x hx
    by_contra hn
    obtain ⟨b,hbU,u,hu,he⟩ := original_critical_paired_commutator_or_mul h hshort hinner path hb hat hzt hcritical
      x (hcontain (mem_sup_right hx)) hn k hk.1 hk0
    have hc : ⁅b,u⁆ ∈ A' := by
      rcases he with he | he
      · exact he ▸ hx
      · exact he ▸ A'.mul_mem hx hk.2
    have hc' : ⁅u,b⁆ ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
      rw [←commutatorElement_inv]
      exact inv_mem hc.2
    have he1 := original_critical_value_in_fixed_eq_one h hinner rev hb hzt
      u (U_le_Z a hu) b hbU hc'
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    rcases he with he | he
    · exact hn (he.symm ▸ he2.symm ▸ A.one_mem)
    · have hxk : x*k ∈ A := he ▸ he2.symm ▸ A.one_mem
      have hxA := A.mul_mem hxk (A.inv_mem hk.1)
      exact hn (by simpa only [mul_inv_cancel_right] using hxA)
  let := finite_Z R a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  exact heq (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

/-- If the complete fixed kernels differ, they are complementary in the
actual common displacement, and each has the full field order. -/
theorem original_critical_fixed_kernels_dichotomy
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    A=A' ∨ Disjoint A A' ∧ Nat.card A=2^n ∧ Nat.card A'=2^n ∧
      A ⊔ A'=⁅Z R a,Z R z⁆ := by
  classical
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  by_cases he : A=A'
  · exact Or.inl he
  have hd := (original_critical_fixed_kernels_eq_or_disjoint h hshort hinner path hb hat hzt hcritical).resolve_left he
  obtain ⟨hA,hA'⟩ := (original_critical_fixed_kernels_eq_or_full h hshort hinner path hb hat hzt hcritical).resolve_left he
  refine Or.inr ⟨hd,hA,hA',?_⟩
  obtain ⟨_,hle,hWU,hWcard,_⟩ := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical
  let := finite_Z R a
  let : Finite (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (hWU.trans inf_le_left |>.trans (U_le_Z a))) (inclusion_injective _)
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hcent : A' ≤ centralizer (A : Set (FreeAmalgam R)) :=
    (le_sup_right.trans hle |>.trans hWU |>.trans inf_le_left |>.trans (U_le_Z a)).trans
      ((Z R a).le_centralizer.trans (centralizer_le (inf_le_left.trans (U_le_Z a))))
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A A'
    (hcent.trans (Subgroup.centralizer_le_normalizer _)) hd,hWcard,hA,hA']


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
