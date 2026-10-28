module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.EdgeGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear

/-!
# Compatible flags for an actual opposite section

Absorb the natural marking into the quotient projection, preserving both
coordinate maps and their conjugation actions. Transitivity on the seven
nonzero covectors then places any chosen dual vector on a parabolic-fixed
line. That parabolic has zero natural fixed space. Surjectivity of the
actual local residual onto the model parabolic transfers this last fact
back to the finite vertex stabilizer.

This supplies the marking and fixedness steps of the geometric seed
construction; it does not produce a native edge representative.
Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), pp.847--848,
and the contained case of (4.3.2)(5), p.884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
open RankOnePairing TerminalPairing
open RankOnePairing.Incidence
open FixedGeometry.ValueConstruction

variable {M : Type*} [Group M] {R : Subgroup M}

def markedOpposite {a : Vertex R} (o : OppositeSectionAt a) : OppositeSectionAt a where
  projection := o.naturalU.marking.toMonoidHom.comp o.projection
  surjective := o.naturalU.marking.surjective.comp o.surjective
  kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _ o.naturalU.marking.injective, o.kernel]
  naturalU := {
    marking := MulEquiv.refl SL
    coordinates := o.naturalU.coordinates
    surjective := o.naturalU.surjective
    kernel := o.naturalU.kernel
    normalized := o.naturalU.normalized
    action := o.naturalU.action }
  dual := {
    coordinates := o.dual.coordinates
    surjective := o.dual.surjective
    kernel := o.dual.kernel
    normalized := o.dual.normalized
    action := o.dual.action }

theorem line_fixed_bot (flag : SL) :
    fixedSpace (markedParabolic (MulEquiv.refl SL) flag true) = ⊥ := by
  have he : markedParabolic (MulEquiv.refl SL) flag true =
      Matrix.PSL3Two.lineParabolicSL.map (MulAut.conj flag).toMonoidHom := by
    simp [markedParabolic, modelParabolic]
  rw [he, ModelProof.fixedSpace_conj, ModelProof.line_fixed_bot, Subgroup.map_bot]

private theorem map_conj_aut (P : Subgroup SL) (f : MulAut SL) (g : SL) :
    (P.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom =
      (P.map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

private theorem marked_refl (flag : SL) :
    markedParabolic (MulEquiv.refl SL) flag true =
      Matrix.PSL3Two.lineParabolicSL.map (MulAut.conj flag).toMonoidHom := by
  simp [markedParabolic, modelParabolic]

theorem seedLine_conj (flag : SL) :
    DualGeometry.seedLine (MulEquiv.refl SL) flag true =
      (DualGeometry.seedLine (MulEquiv.refl SL) 1 true).map
        (vectorAction (BinaryLinearThree.AutomorphismAction.graph flag)).toMonoidHom := by
  have base : markedParabolic (MulEquiv.refl SL) 1 true = Matrix.PSL3Two.lineParabolicSL := by
    rw [marked_refl]
    have he : (MulAut.conj (1 : SL)).toMonoidHom = MonoidHom.id SL := by
      ext x
      simp
    rw [he, Subgroup.map_id]
  rw [DualGeometry.seedLine, DualGeometry.ModelProof.dual_marked, marked_refl,
    map_conj_aut, ModelProof.fixedSpace_conj]
  congr 1
  rw [DualGeometry.seedLine, DualGeometry.ModelProof.dual_marked, base]

theorem exists_flag_of_nonzero (v : VectorGroup) (hv : v ≠ 1) :
    ∃ flag : SL, v ∈ DualGeometry.seedLine (MulEquiv.refl SL) flag true := by
  let K := DualGeometry.seedLine (MulEquiv.refl SL) 1 true
  have hc : Nat.card K = 2 :=
    (DualGeometry.matrixGeometry_of_no_fixed _ _ _ (line_fixed_bot 1)).seed_card
  have hn : K ≠ ⊥ := by intro h; rw [h, card_bot] at hc; omega
  have hn' : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  obtain ⟨w, hw, hw1⟩ := K.exists_ne_one_of_nontrivial
  obtain ⟨flag, hf⟩ := DistanceFour.Linear.dual_orbit
    (show w.toAdd ≠ 0 from hw1) (show v.toAdd ≠ 0 from hv)
  refine ⟨flag, ?_⟩
  rw [seedLine_conj]
  refine ⟨w, hw, ?_⟩
  apply Multiplicative.toAdd.injective
  change (BinaryLinearThree.AutomorphismAction.graph flag).val.mulVec w.toAdd = v.toAdd
  exact hf

variable [Finite M] {L : Subgroup M}

theorem fixed_bot_of_model (source : LocalSource L R)
    {a : Vertex R} (ha : color R a = false) (o : OppositeSectionAt a)
    (flag : SL) (i : Bool)
    (hfixed : fixedSpace (markedParabolic o.naturalU.marking flag i) = ⊥) :
    (U R a).subgroupOf (stabilizer R a) ⊓
      centralizer (localResidual (localParabolic
        (vertexExtension source a ha o flag (binaryWeakBN flag)) i) :
          Set (stabilizer R a)) = ⊥ := by
  let := finite_stabilizer R a
  apply le_bot_iff.mp
  rintro u ⟨hu, hc⟩
  let u' : (U R a).subgroupOf (stabilizer R a) := ⟨u, hu⟩
  have hf : o.naturalU.coordinates u' ∈
      fixedSpace (markedParabolic o.naturalU.marking flag i) := by
    rintro g ⟨k, hk, rfl⟩
    obtain ⟨r, hr, he⟩ := (localResidual_map
      (vertexExtension source a ha o flag (binaryWeakBN flag)) i).symm ▸ hk
    have hconj : u = r * u * r⁻¹ := by
      rw [hc r hr, mul_inv_cancel_right]
    have hh := o.naturalU.action r (mem_top r) u' u' hconj
    apply Multiplicative.toAdd.injective
    change (o.naturalU.marking k).val.mulVec (o.naturalU.coordinates u').toAdd = _
    rw [← he]
    exact hh.symm
  have hz : o.naturalU.coordinates u' = 1 := mem_bot.mp (hfixed.le hf)
  have hu1 : u' = 1 := o.naturalU.equivOfBot.injective (hz.trans (map_one _).symm)
  exact congrArg Subtype.val hu1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
