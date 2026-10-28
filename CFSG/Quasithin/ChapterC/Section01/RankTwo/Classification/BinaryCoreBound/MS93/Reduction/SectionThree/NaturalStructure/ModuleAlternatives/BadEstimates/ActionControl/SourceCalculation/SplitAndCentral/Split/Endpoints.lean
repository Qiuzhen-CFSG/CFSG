module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Moving
/-!
# Actual endpoint ranks in the doubled natural branch

The opposite X layer centralizes exactly its intersection with the local
projection kernel. The elementary rank of SL₃(2) therefore bounds each
critical displacement index by four. Conversely, conjugation to the base
vertex and the genuine doubled-module involution bound force that index
to be at least four. Thus both critical images are actual four-groups.

The proof retains the specified projection in every frame and does not use
edge-offender uniqueness or the later critical-image control theorem.
These are inputs to the source-(3.3) linear calculation, not that calculation.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.2), pp.856–857, (3.2)(iii), p.863, and (3.3), pp.866–868.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The given source projection of an ambient subgroup at the distinguished vertex. -/
@[expose] noncomputable def baseImage (source : LocalSource L R) (E : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (E.subgroupOf (stabilizer R (alpha R))).map (baseProjection source)

theorem baseImage_card (source : LocalSource L R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) :
    Nat.card (baseImage source E) = (Q R (alpha R)).relIndex E := by
  rw [baseImage, ← relIndex_ker, baseProjection_kernel, subgroupOf, relIndex_comap,
    map_subgroupOf_eq_of_le hE]

private theorem action_apply (source : LocalSource L R)
    (s : stabilizer R (alpha R)) (x : X R (alpha R)) :
    (xAction source (baseProjection source s) x : FreeAmalgam R) = s * x * (s : FreeAmalgam R)⁻¹ := by
  obtain ⟨m, rfl⟩ := (baseEquiv (R := R)).surjective s
  rw [baseProjection_baseEquiv, xAction, layerAction_apply, baseEquiv_val]

/-- Fixed vectors are exactly the subgroup centralizing the endpoint layer. -/
theorem baseImage_fixedCodim (source : LocalSource L R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) :
    letI := X_elementary R (alpha R)
    2 ^ fixedCodim (Offenders.linearize (xAction source)) (baseImage source E) =
      Offenders.displacement (X R (alpha R)) E := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  let Y := X R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  let C := (centralizer (E : Set (FreeAmalgam R))).subgroupOf Y
  have hfix (v : Additive Y) : v ∈ fixedSpace ρ (baseImage source E) ↔ v.toMul ∈ C := by
    constructor
    · intro hv e he
      have hh := congrArg (fun w : Additive Y => (w.toMul : FreeAmalgam R))
        (hv ⟨baseProjection source ⟨e, hE he⟩, ⟨⟨e, hE he⟩, he, rfl⟩⟩)
      change (xAction source (baseProjection source ⟨e, hE he⟩) v.toMul : FreeAmalgam R) = _ at hh
      rw [action_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hv g
      obtain ⟨s, hs, he⟩ := g.property
      apply Additive.toMul.injective
      apply Subtype.ext
      change (xAction source g.val v.toMul : FreeAmalgam R) = _
      rw [← he, action_apply]
      have hc : (s : FreeAmalgam R) * (v.toMul : FreeAmalgam R) = v.toMul * s := hv s hs
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  let e : fixedSpace ρ (baseImage source E) ≃ C := {
    toFun := fun v => ⟨v.val.toMul, (hfix v.val).mp v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, (hfix _).mpr x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (baseImage source E)) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (baseImage source E))
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hY : Nat.card Y = 2 ^ Module.finrank (ZMod 2) (Additive Y) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ (baseImage source E)
  have hmul := C.card_mul_index
  rw [hC, hY, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ (baseImage source E))] at hmul
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hmul).symm

private theorem four_le_displacement_base (source : LocalSource L R)
    (hbound : Models.InvolutionBound source) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) (hne : ¬ E ≤ Q R (alpha R))
    [IsElementaryAbelian 2 E] : 4 ≤ Offenders.displacement (X R (alpha R)) E := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  let := IsElementaryAbelian.subgroupOf (p := 2) hE
  let : IsElementaryAbelian 2 (baseImage source E) := IsElementaryAbelian.map (baseProjection source)
  have hn : baseImage source E ≠ ⊥ := by
    intro h
    have hk := (Subgroup.map_eq_bot_iff _).mp h
    rw [baseProjection_kernel] at hk
    exact hne (fun e he => hk (show (⟨e, hE he⟩ : stabilizer R (alpha R)) ∈ E.subgroupOf _ from he))
  obtain ⟨g, hg, hg1⟩ := (baseImage source E).bot_or_exists_ne_one.resolve_left hn
  have hlow := hbound g (elemPow_eq_one_of_isElementaryAbelian g hg) hg1
  let ρ := Offenders.linearize (xAction source)
  change 2 ≤ fixedCodim ρ (zpowers g) at hlow
  have hmono := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr hg))
  have hc := fixedCodim_add_finrank ρ (zpowers g)
  have hEcodim := fixedCodim_add_finrank ρ (baseImage source E)
  have hd : 2 ≤ fixedCodim ρ (baseImage source E) := by omega
  rw [← baseImage_fixedCodim source E hE]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hd

/-- The actual local projection of an ambient subgroup, in its given frame. -/
@[expose] noncomputable def endpointImage (source : LocalSource L R)
    {a : Vertex R} (frame : Frame R a) (E : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (E.subgroupOf (stabilizer R a)).map (frame.projection source)

/-- No quotient marking is changed in the image/index comparison. -/
theorem endpointImage_card (source : LocalSource L R) {a : Vertex R}
    (frame : Frame R a) (E : Subgroup (FreeAmalgam R)) (hE : E ≤ stabilizer R a) :
    Nat.card (endpointImage source frame E) = (Q R a).relIndex E := by
  rw [endpointImage, ← relIndex_ker, frame.projection_kernel, subgroupOf, relIndex_comap,
    map_subgroupOf_eq_of_le hE]

omit [Finite M] in
theorem endpointImage_elementary (source : LocalSource L R) {a : Vertex R}
    (frame : Frame R a) (E : Subgroup (FreeAmalgam R)) (hE : E ≤ stabilizer R a)
    [IsElementaryAbelian 2 E] : IsElementaryAbelian 2 (endpointImage source frame E) := by
  let := IsElementaryAbelian.subgroupOf (p := 2) hE
  exact IsElementaryAbelian.map (frame.projection source)

omit [Finite M] in
/-- Every elementary image in the marked binary local quotient has order at most four. -/
theorem endpointImage_card_le_four (source : LocalSource L R) {a : Vertex R}
    (frame : Frame R a) (E : Subgroup (FreeAmalgam R)) (hE : E ≤ stabilizer R a)
    [IsElementaryAbelian 2 E] : Nat.card (endpointImage source frame E) ≤ 4 := by
  have helem := endpointImage_elementary source frame E hE
  by_cases hn : endpointImage source frame E = ⊥
  · simp [hn]
  have htwo : IsElementaryTwo (endpointImage source frame E) := ⟨hn, helem⟩
  rw [htwo.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two _ helem)

/-- The opposite X layer has precisely the actual local kernel as its
centralizer of X. This does not use offender uniqueness or a model alternative. -/
theorem critical_centralizer_eq (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    X R a ⊓ centralizer (X R a' : Set (FreeAmalgam R)) = X R a ⊓ Q R a' := by
  have ha' := critical_endpoint_color R a ha _ hc
  have hXS := critical_X_le_stabilizer source geometry hb a ha a' hc
  have hZX := (critical_endpoint_choice source geometry hb a ha a' hc).1
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rw [← source.C_eq_Q geometry.radical_ne_bot a' ha']
    exact ⟨hXS hx.1, centralizer_le hZX hx.2⟩
  · exact inf_le_inf_left _ (Q_le_centralizer_X R a')

theorem critical_displacement_eq_index (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Offenders.displacement (X R a) (X R a') = (Q R a').relIndex (X R a) := by
  unfold Offenders.displacement
  rw [← inf_relIndex_left (X R a), critical_centralizer_eq source geometry hb a ha a' hc,
    inf_relIndex_left]

theorem critical_displacement_le_four (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Offenders.displacement (X R a) (X R a') ≤ 4 := by
  let := X_elementary R a
  obtain ⟨frame⟩ := exists_frame a' (critical_endpoint_color R a ha _ hc)
  have hXS := critical_X_le_stabilizer source geometry hb a ha a' hc
  rw [critical_displacement_eq_index source geometry hb a ha a' hc,
    ← endpointImage_card source frame (X R a) hXS]
  exact endpointImage_card_le_four source frame (X R a) hXS

/-- The split involution displacement bound forces every actual critical
displacement index to be four, using only the rank of the marked quotient. -/
theorem critical_displacement_eq_four (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Offenders.displacement (X R a) (X R a') = 4 := by
  apply le_antisymm (critical_displacement_le_four source geometry hb a ha a' hc)
  obtain ⟨frame⟩ := exists_frame a ha
  let f := frame.element⁻¹
  have hf : act R f a = alpha R := by
    rw [← frame.vertex]
    simp only [f, ← act_mul, mul_inv_cancel, act_one]
  have hfcol : color R (act R f a) = false := by rw [hf]; rfl
  have hc' := (criticalPair_act_iff R f a a' (geometry.exists_critical a ha)
    (geometry.exists_critical (act R f a) hfcol)).mpr hc
  have hh : 4 ≤ Offenders.displacement (X R (act R f a)) (X R (act R f a')) := by
    simp only [hf] at hc' ⊢
    let := X_elementary R (act R f a')
    have hcol := critical_endpoint_color R (alpha R) rfl _ hc'
    have hrev := source.critical_reverse geometry (alpha R) rfl _ hcol hc'
    apply four_le_displacement_base source (Models.splitDouble_involutionBound source geometry hb hmodel)
      (X R (act R f a')) (critical_X_le_stabilizer source geometry hb _ hcol _ hrev)
    intro h
    exact (critical_endpoint_choice source geometry hb (alpha R) rfl _ hc').2
      ((critical_endpoint_choice source geometry hb (alpha R) rfl _ hc').1.trans h)
  simpa only [X_act, Offenders.displacement_map] using hh

/-- Every critical endpoint image in the split branch is an actual four-group. -/
theorem critical_endpointImage_card (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) (frame : Frame R a') :
    Nat.card (endpointImage source frame (X R a)) = 4 := by
  rw [endpointImage_card source frame (X R a)
    (critical_X_le_stabilizer source geometry hb a ha a' hc),
    ← critical_displacement_eq_index source geometry hb a ha a' hc]
  exact critical_displacement_eq_four source geometry hb hmodel a ha a' hc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split
