module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexIntersectionBound

/-!
# Displacement comparison on the selected strict-index spans

Source: Meierfrankenfeld--Stellmacher (1993), (3.3) and (5.9), p.921.
The full-cover hyperplane comparison bounds the whole terminal intersection
commutator whenever the displacement comparison fails. Each conjugate of the
smaller seed which moves A₀ realizes the whole R₃. For its first orbit span,
equality of the intersection commutator with R₃ would put the entire span in
B at that conjugate, contrary to the preserved index q. Thus the first-span
commutator has order strictly greater than q, and its displacement comparison
holds. The original selection and both second spans are retained.

This gives the comparison for every moving conjugate in the same C₀-orbit.
For each remaining conjugate whose seed fixes A₀, the entire A₀ lies in
the literal transported T₀, and its first-span commutator lies in the same H₂.
The bound R₃ ≤ D_c and the comparison for these remaining spans are still
needed for the full second-span comparison, strict-index contradiction,
later terminal exclusions and distance-two witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

/-- Escape from the literal displacement comparison bounds the whole
terminal X-intersection commutator, including all central attachments. -/
theorem Input.replacement_critical_intersection_bound_of_comparison
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical)) (hZaY : Z d.radical a ≤ Y)
    (hYQ : Y ≤ Q d.radical a) (hYS : Y ≤ stabilizer d.radical z)
    (hquad : ⁅⁅X d.radical z ⊓ Q d.radical a,Y⁆,Y⁆=⊥)
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F)
    (hi' : (Q d.radical a).relIndex (Z d.radical z)=Nat.card F)
    (hbad : ¬ ⁅Y,Z d.radical z⁆ ≤ Z d.radical a ⊔ ⁅Y,X d.radical z ⊓ Q d.radical a⁆) :
    Nat.card (⁅Y,X d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F := by
  let A := X d.radical z ⊓ Q d.radical a
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hAU : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hUA : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤ A := by
    rw [hAU]
    exact inf_le_inf ((U_le_Z z).trans hZX) le_rfl
  have hpos : 0 < geometry.b d.radical := by omega
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hYS)
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : Y) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hYS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hYS y) w
  let βT := β.comp (inclusion (show Z d.radical a ≤ Y from hZaY))
  have hcard : Nat.card βT.range=Nat.card E.Carrier := by
    have hmark : βT.ker=(Q d.radical z).subgroupOf (Z d.radical a) := by
      ext x
      change e.groupEquiv (κC (inclusion hYS (inclusion hZaY x)))=1 ↔ x.val ∈ Q d.radical z
      rw [e.groupEquiv.map_eq_one_iff]
      have heq : κC (inclusion hYS (inclusion hZaY x))=1 ↔
          inclusion hYS (inclusion hZaY x) ∈ κ.ker := Subtype.ext_iff
      rw [heq]
      constructor
      · intro hx
        exact hκQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype hx
      · intro hx
        obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
        have he : y=inclusion hYS (inclusion hZaY x) := Subtype.ext hyx
        exact he ▸ hy
    rw [←index_ker,hmark]
    exact hi.trans hFc.symm
  have hactT (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (βT x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ :=
    hact (inclusion hZaY x) w
  obtain ⟨hd,hrootquad⟩ := critical_root_coordinates_of_reciprocal_index_field path hpos hCa hFl
    σ p he j hj hjr βT hactT hcard (hi'.trans hFc.symm)
  have hcomm : ⁅Z d.radical a,j.range⁆ ≤ Z d.radical a := by
    rw [hjr]
    exact (commutator_mono le_rfl (U_le_Z z)).trans (critical_commutator_le_start_seed path)
  have hcent : Y ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)))
  have hwhole : ⁅Y,X d.radical z ⊓ Q d.radical a⁆ =
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ := by
    rw [(h.replacement_root_intersection_fixed_and_commutator d path hb hsmall Y hYS).1,hAU]
  have hbadU : ¬ ⁅Y,U d.radical z⁆ ≤ Z d.radical a ⊔
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ := by
    rw [←hwhole]
    intro hh
    apply hbad
    rw [commutator_comm Y (Z d.radical z),
      h.replacement_Z_commutator_eq_U d geometry hb path.end_color Y hYS,
      commutator_comm (U d.radical z)]
    exact hh
  have hbound := HyperplaneMovement.embedded_root_hyperplane_bound_of_comparison hFl p he j hj Y
    (Z d.radical a) hZaY β hact hcard hd hrootquad hcomm hcent
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rw [hjr]; exact hbadU)
  rwa [hjr,hFc,←hwhole] at hbound


private theorem realizing_span_comparison
    {geometry : Geometry d.radical} {c e mu : Vertex d.radical}
    (path : CriticalPath d.radical geometry c e) (hb : 4 < geometry.b d.radical)
    (hmu : color d.radical mu=false) (hd : (cosetGraph d.radical).dist c mu ≤ 2)
    (hYV : sourceSeedSpan d.radical c mu ≤ V d.radical mu)
    (hZmuY : Z d.radical mu ≤ sourceSeedSpan d.radical c mu)
    (hYS : sourceSeedSpan d.radical c mu ≤ stabilizer d.radical e)
    (hi : (Q d.radical e).relIndex (Z d.radical c)=Nat.card F)
    (hi' : (Q d.radical c).relIndex (Z d.radical e)=Nat.card F)
    (hB : (B d.radical mu (geometry.Z_normal mu)).relIndex (U d.radical c)=Nat.card F)
    (hnot : ¬ X d.radical e ⊓ Q d.radical c ≤ Q d.radical mu)
    (hseed : Nat.card (⁅Z d.radical mu,X d.radical e ⊓ Q d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical))=Nat.card F) :
    let Y := sourceSeedSpan d.radical c mu
    Nat.card F < Nat.card (⁅Y,X d.radical e ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) ∧
    ⁅Y,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y,X d.radical e ⊓ Q d.radical c⁆ := by
  dsimp only
  let Y := sourceSeedSpan d.radical c mu
  let A := X d.radical e ⊓ Q d.radical c
  have hYN : Q d.radical c ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    sourceSeedSpan_normalized_by_kernel path.start_color hmu hd
  have hcommY : ⁅A,Y⁆ ≤ Y := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hYN)
  have habel : Y ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    (hYV.trans (le_centralizer_iff_isMulCommutative.mpr
      (V_abelian_of_four_lt d.radical hmu hb))).trans (centralizer_le hYV)
  have hquad : ⁅⁅A,Y⁆,Y⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hcommY.trans habel)
  have heU : ⁅Y,A⁆=⁅Y,U d.radical e ⊓ Q d.radical c⁆ :=
    (h.replacement_root_intersection_fixed_and_commutator d path hb.le
      (by rw [hi]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith) Y hYS).1
  have hRU : ⁅Y,A⁆ ≤ U d.radical e := by
    rw [heU,commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized e)))
  let := finite_Z d.radical e
  let : Finite (U d.radical e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  let : Finite (⁅Y,A⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hRU) (inclusion_injective _)
  have hstrict : Nat.card F < Nat.card (⁅Y,A⁆ : Subgroup (FreeAmalgam d.radical)) := by
    by_contra! hbound
    have heq : ⁅Z d.radical mu,A⁆=⁅Y,A⁆ := eq_of_le_of_card_ge
      (commutator_mono hZmuY le_rfl) (hbound.trans hseed.ge)
    have hAS : A ≤ stabilizer d.radical mu := inf_le_right.trans
      (Q_le_stabilizer_of_dist_le_two c mu path.start_color hmu hd)
    have hAZ : ⁅Y,A⁆ ≤ Z d.radical mu := by
      rw [←heq]
      exact le_normalizer_iff_commutator_le_left.mp (hAS.trans (Z_normalized d.radical mu))
    obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le hmu
    have hlarge : 3 < Nat.card E.Carrier := by
      rw [E.card_eq,hE]
      exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
    let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
    let : IsSimpleGroup (Sp E.Carrier) :=
      Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
    have hk : f.ker=(Q d.radical mu).subgroupOf (stabilizer d.radical mu) := by
      apply map_injective (stabilizer d.radical mu).subtype_injective
      rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical mu ≤ stabilizer d.radical mu from fun _ hx => hx.1)]
    have hYB := normal_radius_le_B_of_kernel_escape geometry (by omega) hmu f hf hk
      (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) mu hmu)
      Y A hYV (le_normalizer_conjugateSpanBy _ _) hAS hnot hAZ
    have hUB : U d.radical c ≤ B d.radical mu (geometry.Z_normal mu) :=
      ((U_le_Z c).trans (le_conjugateSpanBy _ _)).trans hYB
    have hidx := relIndex_eq_one.mpr hUB
    rw [hB] at hidx
    exact (ne_of_gt (Finite.one_lt_card (α := F))) hidx
  refine ⟨hstrict,?_⟩
  by_contra hbad
  exact (not_le_of_gt hstrict) (h.replacement_critical_intersection_bound_of_comparison d path hb.le Y
    (le_conjugateSpanBy _ _) (sourceSeedSpan_le_Q geometry hb path.start_color hd) hYS
    hquad hi hi' hbad)


/-- The same original selector and realizing conjugate supply a strict
increase from R₃ to the first-span commutator, and the full displacement
comparison on that first span. Both second spans and all overlaps persist. -/
theorem Input.replacement_strict_index_selected_displacement_comparison
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2))=Nat.card F ∧
    ∃ y ∈ stabilizer d.radical (path.walk.getVert 2),
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let T₂ := (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom
    let H₂ := conjugatedKernelCommutator geometry a c y
    let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
    let W := sourceCentralizerSpan d.radical c mu H₂
    ¬ Z d.radical mu ≤ B d.radical c (geometry.Z_normal c) ∧
    ¬ T₂ ≤ Q d.radical c ∧
    ¬ H₂ ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) ∧
    ∃ e, ∃ selected : CriticalPath d.radical geometry c e,
      (cosetGraph d.radical).dist e z=2 ∧
      (∀ i ≤ path.walk.length-2, selected.walk.getVert i=path.walk.getVert (i+2)) ∧
      ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) ∧
      C₀ ⊔ Z d.radical e=stabilizer d.radical c ∧
      Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧ W ≤ Q d.radical z ∧
      (Q d.radical e).relIndex (Z d.radical c)=Nat.card F ∧
      (Q d.radical c).relIndex (Z d.radical e)=Nat.card F ∧
      let A₀ := X d.radical e ⊓ Q d.radical c
      let R₃ := ⁅Z₀,A₀⁆
      ¬ ⁅Z₀,Z d.radical e⁆ ≤ Z d.radical c ∧
      R₃ ≠ ⊥ ∧ Nat.card F ≤ Nat.card R₃ ∧
      R₃=⁅Z₀,U d.radical e ⊓ Q d.radical c⁆ ∧
      R₃ ≤ Z₀ ⊓ U d.radical e ∧
      ¬ Z d.radical e ≤ normalizer ((Z₀ ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      Nat.card R₃=Nat.card F ∧
      R₃ ≤ centralizer (V d.radical c : Set (FreeAmalgam d.radical)) ∧
      ∃ t ∈ C₀, ⁅Z d.radical (act d.radical t mu),A₀⁆=R₃ ∧
        ⁅U d.radical (act d.radical t mu),A₀⁆=R₃ ∧
        (centralizer (A₀ : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical (act d.radical t mu))=Nat.card F ∧
        (Q d.radical (act d.radical t mu)).relIndex A₀=Nat.card F ∧
        R₃ ≤ centralizer (Subgroup.SmallMover.join
          (U d.radical (act d.radical t mu)) (Q d.radical (act d.radical t mu))
          (Q d.radical (act d.radical t (act d.radical y (path.walk.getVert 1))))
          (Nat.card F^2) : Set (FreeAmalgam d.radical)) ∧
        let Y := sourceSeedSpan d.radical c (act d.radical t mu)
        Y ≤ W ∧
        R₃ < ⁅Y,A₀⁆ ∧
        Nat.card F < Nat.card (⁅Y,A₀⁆ : Subgroup (FreeAmalgam d.radical)) ∧
        ⁅Y,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y,A₀⁆ ∧
        (∀ s ∈ C₀, ⁅Z d.radical (act d.radical s mu),A₀⁆ ≠ ⊥ →
          let Y₁ := sourceSeedSpan d.radical c (act d.radical s mu)
          ⁅Z d.radical (act d.radical s mu),A₀⁆=R₃ ∧ Y₁ ≤ W ∧
          R₃ < ⁅Y₁,A₀⁆ ∧
          Nat.card F < Nat.card (⁅Y₁,A₀⁆ : Subgroup (FreeAmalgam d.radical)) ∧
          ⁅Y₁,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y₁,A₀⁆) ∧
        (∀ s ∈ C₀, ⁅Z d.radical (act d.radical s mu),A₀⁆=⊥ →
          A₀ ≤ kernelCentralizer geometry (act d.radical s mu) c ∧
          ⁅sourceSeedSpan d.radical c (act d.radical s mu),A₀⁆ ≤ H₂) := by
  obtain ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz,
      hic,hie,hbad,hne,hcard,heq,hRU,hnotn,hsize,hcentral,t,ht,htEq,htU,hidx,hQidx,hfixed⟩ :=
    h.replacement_strict_index_selected_field_intersection d path hb hsmall
  let c := path.walk.getVert 2
  let mu := act d.radical y a
  let H₂ := conjugatedKernelCommutator geometry a c y
  let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
  let W := sourceCentralizerSpan d.radical c mu H₂
  let A₀ := X d.radical e ⊓ Q d.radical c
  have hall (s : FreeAmalgam d.radical) (hs : s ∈ C₀)
      (hm : ⁅Z d.radical (act d.radical s mu),A₀⁆ ≠ ⊥) :
      let Y₁ := sourceSeedSpan d.radical c (act d.radical s mu)
      ⁅Z d.radical (act d.radical s mu),A₀⁆=⁅Z₀,A₀⁆ ∧ Y₁ ≤ W ∧
      ⁅Z₀,A₀⁆ < ⁅Y₁,A₀⁆ ∧
      Nat.card F < Nat.card (⁅Y₁,A₀⁆ : Subgroup (FreeAmalgam d.radical)) ∧
      ⁅Y₁,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y₁,A₀⁆ := by
    dsimp only
    let nu := act d.radical s mu
    let Y := sourceSeedSpan d.radical c nu
    have hnu : color d.radical nu=false := by
      rw [action_preserves_color,action_preserves_color]; exact path.start_color
    have hyt : y*s ∈ stabilizer d.radical c := (stabilizer d.radical c).mul_mem hy hs.1
    have hytc : act d.radical (y*s) c=c := hyt
    have hytmu : act d.radical (y*s) a=nu := by rw [act_mul]
    obtain ⟨_,_,hZcY,hZnuY,hYV,_,_,_,_,_⟩ :=
      h.replacement_strict_index_conjugated_span d path hb hsmall (y*s) hyt
    rw [hytmu] at hZnuY hYV
    have hd : (cosetGraph d.radical).dist c nu ≤ 2 := by
      have hh := dist_act d.radical (y*s) c a
      rw [hytc,hytmu] at hh
      rw [hh,SimpleGraph.dist_comm]
      exact (path.dist_start (by rw [path.length_eq_b]; omega)).le
    have hmap : (sourceSeedSpan d.radical c mu).map (MulAut.conj s⁻¹).toMonoidHom=Y := by
      change (conjugateSpanBy _ _).map _=conjugateSpanBy _ _
      rw [map_conjugateSpanBy,←Z_act,←stabilizer_act,
        show act d.radical s c=c from hs.1]
    have hYW : Y ≤ W := by
      rw [←hmap]
      rintro _ ⟨v,hv,rfl⟩
      exact subset_closure ⟨s⁻¹,C₀.inv_mem hs,v,hv,rfl⟩
    have hYS : Y ≤ stabilizer d.radical e := (hYW.trans hWz).trans
      (Q_le_stabilizer_of_dist_le_two z e path.end_color selected.end_color
        (by rw [SimpleGraph.dist_comm]; exact hez.le))
    have hBi : (B d.radical nu (geometry.Z_normal nu)).relIndex (U d.radical c)=Nat.card F := by
      have hh := relIndex_map_map_of_injective (f := (MulAut.conj (y*s)⁻¹).toMonoidHom)
        (B d.radical a (geometry.Z_normal a))
        (U d.radical c) (MulAut.conj (y*s)⁻¹).injective
      rw [←Escape.PairingControl.FirstPairing.B_act (by omega) (y*s) a path.start_color,
        ←U_act,hytc,hytmu] at hh
      exact hh.trans hi
    have hZnuZ : Z d.radical nu ≤ Z₀ := by
      rw [Z_act]
      rintro _ ⟨v,hv,rfl⟩
      exact subset_closure ⟨s⁻¹,C₀.inv_mem hs,v,hv,rfl⟩
    have hlo := h.replacement_root_intersection_commutator_card_ge_field d selected hb.le
      (by rw [hic]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith)
      (Z d.radical nu) (hZnuY.trans hYS) hm
    let := finite_Z d.radical e
    let : Finite (U d.radical e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
    let : Finite (⁅Z₀,A₀⁆ : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion (hRU.trans inf_le_right)) (inclusion_injective _)
    have hsEq : ⁅Z d.radical nu,A₀⁆=⁅Z₀,A₀⁆ := eq_of_le_of_card_ge
      (commutator_mono hZnuZ le_rfl) (hsize.le.trans hlo)
    have hseed : Nat.card (⁅Z d.radical nu,A₀⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card F :=
      by rw [hsEq]; exact hsize
    have hnot : ¬ A₀ ≤ Q d.radical nu := by
      intro hh
      exact hm (le_bot_iff.mp ((commutator_mono le_rfl hh).trans
        (geometry.centralizes nu hnu).le))
    obtain ⟨hstrict,hcompare⟩ := realizing_span_comparison h d selected hb hnu hd hYV hZnuY
      hYS hic hie hBi hnot hseed
    have hproper : ⁅Z₀,A₀⁆ < ⁅Y,A₀⁆ := by
      apply lt_of_le_of_ne
      · rw [←hsEq]
        exact commutator_mono hZnuY le_rfl
      · intro he
        have hh := congrArg (fun T : Subgroup (FreeAmalgam d.radical) => Nat.card T) he
        rw [hsize] at hh
        exact (ne_of_gt hstrict) hh.symm
    exact ⟨hsEq,hYW,hproper,hstrict,hcompare⟩
  have hquiet (s : FreeAmalgam d.radical) (hs : s ∈ C₀)
      (hm : ⁅Z d.radical (act d.radical s mu),A₀⁆=⊥) :
      A₀ ≤ kernelCentralizer geometry (act d.radical s mu) c ∧
      ⁅sourceSeedSpan d.radical c (act d.radical s mu),A₀⁆ ≤ H₂ := by
    let nu := act d.radical s mu
    have hnu : color d.radical nu=false := by
      rw [action_preserves_color,action_preserves_color]; exact path.start_color
    have hys : y*s ∈ stabilizer d.radical c := (stabilizer d.radical c).mul_mem hy hs.1
    have hysnu : act d.radical (y*s) a=nu := by rw [act_mul]
    have hd : (cosetGraph d.radical).dist c nu ≤ 2 := by
      have hh := dist_act d.radical (y*s) c a
      rw [show act d.radical (y*s) c=c from hys,hysnu] at hh
      rw [hh,SimpleGraph.dist_comm]
      exact (path.dist_start (by rw [path.length_eq_b]; omega)).le
    have hAS : A₀ ≤ stabilizer d.radical nu := inf_le_right.trans
      (Q_le_stabilizer_of_dist_le_two c nu selected.start_color hnu hd)
    have hAQ : A₀ ≤ Q d.radical nu := by
      rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) nu hnu]
      exact le_inf hAS (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm))
    have hAU : A₀ ≤ centralizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
      (inf_le_right.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes c selected.start_color)))).trans (centralizer_le (U_le_Z c))
    have hAT : A₀ ≤ kernelCentralizer geometry nu c :=
      le_inf hAQ (hAU.trans (centralizer_le inf_le_left))
    obtain ⟨hTnu,_,_,_,_,_,_,hdisp,_,_⟩ :=
      h.replacement_strict_index_conjugated_span d path hb hsmall (y*s) hys
    rw [hysnu] at hTnu hdisp
    have hHeq : conjugatedKernelCommutator geometry a c (y*s)=H₂ := by
      change (kernelCommutator geometry a c).map (MulAut.conj (y*s)⁻¹).toMonoidHom=H₂
      have he : (MulAut.conj (y*s)⁻¹).toMonoidHom=
          (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change (y*s)⁻¹*x*((y*s)⁻¹)⁻¹=s⁻¹*(y⁻¹*x*(y⁻¹)⁻¹)*(s⁻¹)⁻¹
        group
      rw [he,←map_map]
      exact mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.centralizer_le_normalizer _) (C₀.inv_mem hs).2)
    rw [←hTnu,hHeq] at hdisp
    exact ⟨hAT,(commutator_mono le_rfl hAT).trans_eq hdisp⟩
  obtain ⟨_,hYW,hproper,hstrict,hcompare⟩ := hall t ht (by rw [htEq]; exact hne)
  exact ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz,
    hic,hie,hbad,hne,hcard,heq,hRU,hnotn,hsize,hcentral,t,ht,htEq,htU,hidx,hQidx,hfixed,
    hYW,hproper,hstrict,hcompare,hall,hquiet⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
