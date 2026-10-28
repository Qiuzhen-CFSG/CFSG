module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanNatural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanFixedFree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFixedCentrality
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.SpecificGroups.SymplecticFour.CentralNaturalDerived

/-!
# The field-size derived bound on the selected full moved radius

Keep the actual orientation and full quotient chosen by SpanNatural. Under
its original coordinates, SpanMovement identifies the image of Vcirc with
the literal moved space. FixedFree removes the further fixed preimage in
the canonical moved quotient. Composing these same maps with the retained
natural coordinates gives a surjective natural map on the full Vcirc.

Its kernel lies in B, which centralizes Vcirc in the actual fixed-radius
branch. The derived group is fixed by the actual residual actor. The
natural commutator-row bound therefore gives order at most the original
field size. The reciprocal orientation remains explicit; no prescribed
orbit for the backward endpoint is inferred.
Source: MS93 (3.10)(i), printed p.880, as used in (5.12)(2), p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem derived_bound_from_same_span
    {geometry : Geometry d.radical} {a z c₀ y : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (largePath : CriticalPath d.radical geometry c₀ y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c₀))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hnat : distanceFourSpanNatural geometry a (path.walk.getVert 2) n) :
    Nat.card (⁅Vcirc d.radical a,Vcirc d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤
      Nat.card F := by
  obtain ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor,hIrr,Eₙ,hEₙ,⟨eₙ⟩⟩ := hnat
  let := hD
  let := hEA
  let W := localZSpan d.radical (path.walk.getVert 2) a
  let P := Vcirc d.radical a
  let L := Ltilde d.radical a
  let S := stabilizer d.radical a
  let s := MovedSection.ofNormal σ (⊤ : Subgroup (Sp E.Carrier))
  have hb2 : 2 < geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  have hPW : P ≤ W :=
    h.replacement_distance_four_moving_le_midpoint_span_of_large_path d path hb largePath hlarge
  have hm : c.imageSpace P=s.space.toSubmodule :=
    (h.replacement_distance_four_span_moved_image d path hb largePath hlarge E hE f hf σ c).trans
      s.space_eq.symm
  have hzero := h.replacement_radius_section_fixedSpace_eq_bot d geometry hb2
    path.start_color W hWV f σ c
  let κ : P →* Multiplicative s.space.toSubmodule := {
    toFun v := Multiplicative.ofAdd ⟨(c.coordinates (inclusion hPW v)).toAdd,by
      rw [←hm]
      exact (c.mem_imageSpace_iff P _).mpr ⟨inclusion hPW v,v.property,rfl⟩⟩
    map_one' := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd c.coordinates.map_one
    map_mul' v w := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (c.coordinates.map_mul (inclusion hPW v) (inclusion hPW w)) }
  have hκ : Function.Surjective κ := by
    intro v
    have hv : v.toAdd.val ∈ c.imageSpace P := hm.symm ▸ v.toAdd.property
    obtain ⟨w,hw,he⟩ := (c.mem_imageSpace_iff P v.toAdd.val).mp hv
    refine ⟨⟨w,hw⟩,?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext he
  let p : s.space.toSubmodule →ₗ[ZMod 2] Vector Eₙ.Carrier :=
    eₙ.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  have hp : Function.Surjective p :=
    eₙ.linearEquiv.surjective.comp (Submodule.mkQ_surjective s.central.toSubmodule)
  have hpk (v : s.space.toSubmodule) (hv : p v=0) : v.val=0 := by
    change eₙ.linearEquiv (s.central.toSubmodule.mkQ v)=0 at hv
    have hz : s.central.toSubmodule.mkQ v=0 :=
      eₙ.linearEquiv.injective (hv.trans eₙ.linearEquiv.map_zero.symm)
    have hmem := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hz
    rw [s.central_eq] at hmem
    have hvfix : v.val ∈ fixedSpace σ ⊤ := by
      intro g
      exact congrArg Subtype.val (hmem g)
    simpa only [hzero,Submodule.mem_bot] using hvfix
  let q : P →* Multiplicative (Vector Eₙ.Carrier) := p.toAddMonoidHom.toMultiplicative.comp κ
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w,hw⟩ := hp v.toAdd
    obtain ⟨v₀,hv₀⟩ := hκ (Multiplicative.ofAdd w)
    refine ⟨v₀,Multiplicative.toAdd.injective ?_⟩
    change p (κ v₀).toAdd=v.toAdd
    rw [hv₀]
    exact hw
  have hBP : B d.radical a (geometry.Z_normal a) ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact radius_moving_centralizes_full_B geometry hb2 path.start_color hfixed)
  have hk : q.ker ≤ center P := by
    intro v hv
    have hvzero : (c.coordinates (inclusion hPW v)).toAdd=0 := hpk (κ v).toAdd hv
    have hvB := ((c.coordinates_eq_one_iff (inclusion hPW v)).mp hvzero).2
    apply mem_center_iff.mpr
    intro w
    exact Subtype.ext (hBP hvB w w.property)
  have hLP : L ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    (Ltilde_le_stabilizer a).trans (Vcirc_normalized a)
  let α : L →* MulAut P := P.normalizerMonoidHom.comp (inclusion hLP)
  have hLS : L ≤ S := Ltilde_le_stabilizer a
  let fL : L →* Sp E.Carrier := f.comp (inclusion hLS)
  let := finite_stabilizer d.radical a
  have hcard : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let : Group.IsPerfect (Sp E.Carrier) := perfect_of_card_gt_two hcard
  have hmap : (L.subgroupOf S).map f=⊤ := by
    have he : L.subgroupOf S=pResidual 2 S :=
      comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf,pResidual_eq_top_of_isPerfect 2]
  have hfL : Function.Surjective fL := by
    intro x
    obtain ⟨l,hl,he⟩ := (show x ∈ (L.subgroupOf S).map f from hmap.symm ▸ mem_top x)
    exact ⟨⟨l,hl⟩,he⟩
  let π : L →* Sp Eₙ.Carrier :=
    eₙ.groupEquiv.toMonoidHom.comp (topEquiv.symm.toMonoidHom.comp fL)
  have hπ : Function.Surjective π :=
    eₙ.groupEquiv.surjective.comp (topEquiv.symm.surjective.comp hfL)
  have heq (l : L) (v : P) : (q (α l v)).toAdd=π l • (q v).toAdd := by
    have he : (κ (α l v)).toAdd=s.space.toRepresentation (fL l) (κ v).toAdd := by
      apply Subtype.ext
      exact c.equivariant (inclusion hLS l) (inclusion hPW v)
    change p (κ (α l v)).toAdd=π l • p (κ v).toAdd
    exact (congrArg p he).trans
      (eₙ.intertwines (topEquiv.symm (fL l)) (s.central.toSubmodule.mkQ (κ v).toAdd))
  have hPV := DistanceEight.Vcirc_le_V d.radical a
  have hder : ⁅P,P⁆ ≤ fixedCore d.radical a :=
    (commutator_mono hPV (hPV.trans (geometry.V_le_Q hb2 a path.start_color))).trans hfixed
  have hfix (l : L) (v : P) (hv : v ∈ _root_.commutator P) : α l v=v := by
    have hv' : (v : FreeAmalgam d.radical) ∈ ⁅P,P⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem P.subtype hv
    apply Subtype.ext
    change (l : FreeAmalgam d.radical)*(v : FreeAmalgam d.radical)*(l : FreeAmalgam d.radical)⁻¹=v
    rw [(hder hv').2 l l.property,mul_inv_cancel_right]
  have hc : _root_.commutator P ≤ center P := (Abelianization.commutator_subset_ker q).trans hk
  have hbound := Subgroup.ClassTwo.card_commutator_le_of_symplectic_section
    hc α π hπ q hq hk heq hfix
  rw [←map_subtype_commutator,card_map_of_injective P.subtype_injective]
  simpa only [Eₙ.card_eq,hEₙ,h.field_card] using hbound

/-- The original actual branch supplies the field-size derived bound on
the same orientation selected by natural recognition, retaining that entire
marked span certificate. No natural-map or numerical-bound premise is supplied. -/
theorem Input.replacement_distance_four_span_derived_bound_or_reciprocal
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (distanceFourSpanNatural geometry a (path.walk.getVert 2) n ∧
      Nat.card (⁅Vcirc d.radical a,Vcirc d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F) ∨
    (distanceFourSpanNatural geometry (path.walk.getVert 2) a n ∧
      Nat.card (⁅Vcirc d.radical (path.walk.getVert 2),Vcirc d.radical (path.walk.getVert 2)⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hsq : Nat.card F^2 ≤ (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u) := by
    by_contra! hs
    exact (ne_of_gt hlarge) (h.replacement_small_critical_indices_eq_field d back (by omega) hs).1
  rcases h.replacement_distance_four_span_natural_or_reciprocal d path hb back hmid hlarge hfixed
    with hnat | hnat
  · exact Or.inl ⟨hnat,derived_bound_from_same_span h d path hb back hsq hfixed hnat⟩
  · let e := path.walk.getVert 2
    have he := back.end_color
    have hfixed_e : ⁅V d.radical e,Q d.radical e⁆ ≤ fixedCore d.radical e := by
      obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical path.start_color
      obtain ⟨k,hk⟩ := exists_mVertex_of_color d.radical he
      have hact : act d.radical (g⁻¹*k) a=e := by
        rw [hg,act_mVertex,mul_inv_cancel_left,←hk]
      have hh := map_mono (f := (MulAut.conj (g⁻¹*k)⁻¹).toMonoidHom) hfixed
      rwa [map_commutator,←V_act,←Q_act,←Escape.EdgeTransfer.fixedCore_act,hact] at hh
    let rev : CriticalPath d.radical geometry e u := {
      start_color := back.end_color
      walk := back.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,back.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        u back.start_color (by
          rw [geometry.distance_constant u back.start_color]
          exact lt_of_lt_of_le (by decide : 0<4) hb4)
        e back.end_color back.critical }
    have hrmid : rev.walk.getVert 2=a := by
      change back.walk.reverse.getVert 2=a
      rw [SimpleGraph.Walk.getVert_reverse,back.length_eq_b,hb]
      exact hmid
    refine Or.inr ⟨hnat,?_⟩
    apply derived_bound_from_same_span h d rev hb back hsq hfixed_e
    rwa [hrmid]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
