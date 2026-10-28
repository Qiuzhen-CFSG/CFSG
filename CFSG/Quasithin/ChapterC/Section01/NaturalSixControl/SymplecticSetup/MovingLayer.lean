module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NaturalLayer
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NaturalLayerOriginal

/-!
# Literal coordinates and fixed points of the symplectic moving layer

The recognized moving layer uses the original natural coordinates and exactly
its original conjugation action. Its component-fixed subgroup is trivial, so
it is disjoint from both the source fixed core and the local stabilizer center.
The original Baumann pair and each characteristic replacement retain this
same marked layer.

Source: MS93 (3.2)(vi), printed pp.863--864. These facts identify U and its
fixed points; they do not assert a fixed complement to U in the entire X-layer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal]

/-- The actual central moving layer, with the specified native module. -/
structure NativeCentralLayer (_s : Source L R W) : Prop where
  X_commutator : ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R)
  U_eq_module : U R (alpha R) = W.map (embedM R)

namespace Source
variable (s : Source L R W)
include s

theorem nativeCentralLayer (hsq : IsSQTK KnownSimple.IsKnownSimple M) :
    NativeCentralLayer s := ⟨(s.natural_moving_layer hsq).1,(s.natural_moving_layer hsq).2⟩

/-- The marked natural coordinates are transported to the actual graph layer. -/
noncomputable def movingLayerCoordinates (h : NativeCentralLayer s) :
    U R (alpha R) ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  ((MulEquiv.subgroupCongr h.U_eq_module).trans
    (W.equivMapOfInjective (embedM R) (embedM_injective R)).symm).trans s.coordinates

omit [Finite M] [L.Normal] s in
private theorem embed_conj (g : M) (w : W) :
    embedM R (MulAut.conjNormal g w) =
      (MulAut.conj (embedM R g)) (embedM R w) := by
  change embedM R (g*(w:M)*g⁻¹) = _
  rw [map_mul,map_mul,map_inv]
  rfl

omit [Finite M] in
/-- The local group normalizes the actual moving layer. -/
theorem movingLayer_normalized (h : NativeCentralLayer s) :
    (⊤ : Subgroup M).map (embedM R) ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) := by
  rw [h.U_eq_module]
  simpa only [normalizer_eq_top] using W.le_normalizer_map (embedM R)

omit [Finite M] in
/-- The coordinates on U use exactly the source's original natural action. -/
theorem movingLayerCoordinates_action (h : NativeCentralLayer s)
    (g : M) (u : U R (alpha R)) :
    (s.movingLayerCoordinates h ((U R (alpha R)).normalizerMonoidHom
      ⟨embedM R g,s.movingLayer_normalized h (mem_map_of_mem (embedM R) (mem_top g))⟩ u)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (s.projection g)
        (s.movingLayerCoordinates h u).toAdd := by
  let e : W ≃* U R (alpha R) :=
    (W.equivMapOfInjective (embedM R) (embedM_injective R)).trans
      (MulEquiv.subgroupCongr h.U_eq_module.symm)
  obtain ⟨w,rfl⟩ := e.surjective u
  have he : (U R (alpha R)).normalizerMonoidHom
      ⟨embedM R g,s.movingLayer_normalized h (mem_map_of_mem (embedM R) (mem_top g))⟩ (e w) =
        e (MulAut.conjNormal g w) := by
    apply Subtype.ext
    exact (embed_conj g w).symm
  rw [he]
  have hc (v : W) : s.movingLayerCoordinates h (e v) = s.coordinates v := by
    unfold movingLayerCoordinates
    change s.coordinates ((W.equivMapOfInjective (embedM R) (embedM_injective R)).symm
      ((MulEquiv.subgroupCongr h.U_eq_module) (e v))) = s.coordinates v
    have hh : (MulEquiv.subgroupCongr h.U_eq_module) (e v) =
        (W.equivMapOfInjective (embedM R) (embedM_injective R)) v := by
      apply Subtype.ext
      rfl
    rw [hh,MulEquiv.symm_apply_apply]
  rw [hc,hc]
  exact s.action g w


omit [Finite M] in
/-- The specified natural module has no component-fixed vector. -/
theorem module_inf_component_centralizer_eq_bot :
    W ⊓ centralizer (L : Set M) = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨hx,hc⟩
  have hf : (s.coordinates ⟨x,hx⟩).toAdd ∈ Representation.BinaryOffender.fixedSpace
      Model.rho (alternatingGroup (Fin 6)) := by
    intro a
    obtain ⟨l,hl,he⟩ := s.component_image.ge a.property
    have hconj : MulAut.conjNormal l (⟨x,hx⟩ : W) = ⟨x,hx⟩ := by
      apply Subtype.ext
      change l*x*l⁻¹=x
      rw [hc l hl,mul_inv_cancel_right]
    have hh := s.action l ⟨x,hx⟩
    rw [hconj,he] at hh
    exact hh.symm
  rw [Model.fixedSpace_alternating_eq_bot] at hf
  have hx1 : (⟨x,hx⟩ : W) = 1 := s.coordinates.injective (by
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hf)
  exact congrArg Subtype.val hx1

/-- The moving natural layer meets its component-fixed subgroup trivially. -/
theorem movingLayer_inf_component_centralizer_eq_bot (h : NativeCentralLayer s) :
    U R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) = ⊥ := by
  rw [h.U_eq_module,Ltilde_alpha,s.residual]
  apply le_bot_iff.mp
  rintro x ⟨⟨w,hw,rfl⟩,hc⟩
  have hcM : w ∈ centralizer (L : Set M) := by
    intro l hl
    apply embedM_injective R
    simpa only [map_mul] using hc (embedM R l) (mem_map_of_mem _ hl)
  have hw0 : w ∈ (⊥ : Subgroup M) :=
    s.module_inf_component_centralizer_eq_bot ▸ ⟨hw,hcM⟩
  simpa only [mem_bot,map_one] using congrArg (embedM R) (mem_bot.mp hw0)

/-- In particular U is disjoint from the source fixed core D. -/
theorem movingLayer_inf_fixedCore_eq_bot (h : NativeCentralLayer s) :
    U R (alpha R) ⊓ fixedCore R (alpha R) = ⊥ := by
  apply le_bot_iff.mp
  exact (inf_le_inf_left _ inf_le_right).trans_eq
    (s.movingLayer_inf_component_centralizer_eq_bot h)

/-- The center of the local stabilizer contributes no vector to U. -/
theorem movingLayer_inf_stabilizer_center_eq_bot (h : NativeCentralLayer s) :
    U R (alpha R) ⊓ (center (stabilizer R (alpha R))).map
      (stabilizer R (alpha R)).subtype = ⊥ := by
  have hc : (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ≤
      centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
    rintro x ⟨z,hz,rfl⟩ l ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz y)
  apply le_bot_iff.mp
  exact (inf_le_inf_left _ hc).trans_eq
    (s.movingLayer_inf_component_centralizer_eq_bot h)

end Source

namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)
include d

/-- The intrinsic original pair supplies its central-layer conclusion. -/
theorem original_nativeCentralLayer (h : IntrinsicMSPair d) :
    NativeCentralLayer (originalSource d h) :=
  ⟨(original_natural_layer d h).1,(original_natural_layer d h).2⟩

/-- The same conclusion holds on every actual characteristic replacement. -/
theorem reduced_nativeCentralLayer (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    NativeCentralLayer ((originalSource d h).reduce c) :=
  ⟨(reduced_natural_layer d h c).1,(reduced_natural_layer d h c).2⟩

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
