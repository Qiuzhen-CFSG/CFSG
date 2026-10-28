module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.FlagMap
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.CoreSequences
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# A checked inverse for the Fano flag map

The coefficient at a flag (x,λ) of a tuple (c,a,b,A) is
c + a(x) + b(λ) + λ(Σ a(y)y) + (Σ b(μ)μ)(x) + λ(Ax).
The two weighted-sum corrections remove the cross terms between the cores.
Checking this formula on pairs of incident flags gives a left inverse; the
actual source and target both have dimension 21, so the map is bijective.

Source: the explicit decomposition of Aschbacher–Smith H.6.2(1), combined
manuscript of 1 March 2004, printed p.387.
-/

@[expose] public section
open Matrix Representation
namespace BinaryLinearThree.FanoDecomposition

/-- Explicit reconstruction of every flag coefficient from the four summands. -/
noncomputable def flagInverse : Target →ₗ[ZMod 2] BinaryPermutation.Full Flag where
  toFun v f := v.1 + v.2.1.val f.val.1 + v.2.2.1.val f.val.2 +
    lineFunctional f.val.2 (pointWeightedSum v.2.1) +
    lineWeightedSum v.2.2.1 f.val.1.val +
    lineFunctional f.val.2 (v.2.2.2.val f.val.1.val)
  map_add' v w := by
    funext f
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, map_add,
      LinearMap.add_apply]
    abel
  map_smul' c v := by
    funext f
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply,
      map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem point_spike_sum : ∀ p : Point, pointWeightedSum (pointSpike p) = p.val := by
  decide +kernel

private theorem line_spike_sum (l : Line) : lineWeightedSum (lineSpike l) = lineFunctional l := by
  change dotProductEquiv (ZMod 2) (Fin 3)
    (pointWeightedSum (coreDuality.symm (lineSpike l))) = _
  have hc : coreDuality.symm (lineSpike l) = pointSpike l.normal := by
    apply Subtype.ext
    funext p
    change (Pi.single l 1 : Line → ZMod 2) (Matrix.PSL3Two.Fano.duality p) + 1 = (Pi.single l.normal 1 : Point → ZMod 2) p + 1
    simp only [Pi.single_apply]
    congr 2
    exact propext Matrix.PSL3Two.Fano.duality.eq_symm_apply.symm
  rw [hc, point_spike_sum]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem flag_pair_certificate : ∀ f h : Flag,
    1 + ((Pi.single f.val.1 1 : Point → ZMod 2) h.val.1 + 1) +
      ((Pi.single f.val.2 1 : Line → ZMod 2) h.val.2 + 1) +
      lineFunctional h.val.2 f.val.1.val + lineFunctional f.val.2 h.val.1.val +
      lineFunctional f.val.2 h.val.1.val * lineFunctional h.val.2 f.val.1.val =
      (Pi.single f 1 : Flag → ZMod 2) h := by
  decide +kernel

/-- The inverse formula recovers each actual flag basis vector. -/
theorem flagInverse_value (f : Flag) : flagInverse (flagValue f) = Pi.single f 1 := by
  funext h
  change 1 + (pointSpike f.val.1).val h.val.1 + (lineSpike f.val.2).val h.val.2 +
    lineFunctional h.val.2 (pointWeightedSum (pointSpike f.val.1)) +
    lineWeightedSum (lineSpike f.val.2) h.val.1.val +
    lineFunctional h.val.2 ((flagRankOne f).val h.val.1.val) = _
  rw [point_spike_sum, line_spike_sum, flagRankOne_apply, map_smul]
  exact flag_pair_certificate f h

/-- Reconstruction is a left inverse on the whole flag permutation module. -/
theorem flagInverse_leftInverse : Function.LeftInverse flagInverse flagMap := by
  intro a
  rw [flagMap_apply, map_sum]
  simp only [map_smul, flagInverse_value]
  funext f
  simp [Finset.sum_apply, Pi.single_apply]

theorem flagMap_injective : Function.Injective flagMap := flagInverse_leftInverse.injective

/-- Dimension of the explicitly parenthesized target carrier. -/
theorem finrank_target : Module.finrank (ZMod 2) Target = 21 := by
  let : Nonempty Point := ⟨Matrix.PSL3Two.flagPoint⟩
  let : Nonempty Line := ⟨Matrix.PSL3Two.flagLine⟩
  simp [Target, Module.finrank_prod, Module.finrank_self, Core, LineCore,
    BinaryPermutation.finrank_core, Matrix.PSL3Two.Fano.card_line, finrank_steinberg]

private theorem linear_bijective (f : BinaryPermutation.Full Flag →ₗ[ZMod 2] Target)
    (hf : Function.Injective f) : Function.Bijective f := by
  have hd : Module.finrank (ZMod 2) (BinaryPermutation.Full Flag) =
      Module.finrank (ZMod 2) Target := by
    rw [BinaryPermutation.finrank_full, card_flags, finrank_target]
  exact ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ZMod 2) (V := BinaryPermutation.Full Flag) (V₂ := Target) hd (f := f)).mp hf⟩

/-- Bijectivity of the actual flag map, proved from its checked left inverse. -/
theorem flagMap_bijective : Function.Bijective flagMap := by
  exact linear_bijective flagLinearMap flagMap_injective

end BinaryLinearThree.FanoDecomposition
