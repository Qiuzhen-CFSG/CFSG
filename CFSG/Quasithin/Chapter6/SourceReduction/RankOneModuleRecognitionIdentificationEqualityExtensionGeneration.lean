module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionLayer
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Local generation and fixed points in the equality branch

Transitivity of SL₂(4) on the nonzero natural vectors, together with
C_M(z)=T, gives M=LT. The elementary centralizer D has fixed subgroup
C_D(T)=⟨z⟩, and [D,T∩L] lies in this central line. Natural-vector
transitivity also supplies the involution fusion within V used by transfer.

Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

omit [Finite G] in
private theorem natural_layer_transitive {V : Subgroup G}
    (hnatural : IsNaturalModule L V 2) {v w : G}
    (hv : v ∈ V) (hw : w ∈ V) (hvne : v ≠ 1) (hwne : w ≠ 1) :
    ∃ l ∈ L, l * v * l⁻¹ = w := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  have hfv : (f ⟨v, hv⟩).toAdd ≠ 0 := by
    intro hh
    apply hvne
    exact congrArg Subtype.val (f.injective
      ((Multiplicative.toAdd.injective hh).trans (map_one f).symm))
  have hfw : (f ⟨w, hw⟩).toAdd ≠ 0 := by
    intro hh
    apply hwne
    exact congrArg Subtype.val (f.injective
      ((Multiplicative.toAdd.injective hh).trans (map_one f).symm))
  obtain ⟨a, ha⟩ := Matrix.SL2.exists_mulVec_eq F _ _ hfv hfw
  obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) a
  change e (QuotientGroup.mk' (pCore 2 L) l) = a at hl
  refine ⟨l, l.property, ?_⟩
  have he := hf l ⟨v, hv⟩
  change (f.symm (Multiplicative.ofAdd
    (Matrix.mulVec (e (QuotientGroup.mk' (pCore 2 L) l)).val (f ⟨v, hv⟩).toAdd)) : G) =
    (l : G) * v * (l : G)⁻¹ at he
  rw [hl, ha] at he
  change (f.symm (f ⟨w, hw⟩) : G) = (l : G) * v * (l : G)⁻¹ at he
  rw [f.symm_apply_apply] at he
  exact he.symm

omit [Finite G] in
/-- The natural layer contributes one involution class to the transfer argument. -/
theorem equality_layer_involution_fusion
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    {v : G} (hv : v ∈ layer L R) (hvorder : orderOf v = 2) : IsConj z v := by
  obtain ⟨l, _, hl⟩ := natural_layer_transitive hnatural.2.1 hz.1 hv
    (by intro he; simp [he] at horder)
    (by intro he; simp [he] at hvorder)
  exact isConj_iff.mpr ⟨l, hl⟩

/-- Transitivity on the nonidentity natural vectors and C_M(z)=T give M=LT. -/
theorem LocalAnalysis.equality_maximal_eq_local
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    M = L ⊔ (T : Subgroup G) := by
  have hMV := A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch
  apply le_antisymm ?_ (sup_le h611.L_le h611.sylow_le)
  intro m hm
  have hzm : m * z * m⁻¹ ∈ layer L R :=
    (mem_normalizer_iff.mp (hMV hm) z).mp hz.1
  have hz1 : z ≠ 1 := by intro he; simp [he] at horder
  have hzm1 : m * z * m⁻¹ ≠ 1 := by
    intro he
    apply hz1
    apply (MulAut.conj m).injective
    exact he.trans (map_one (MulAut.conj m)).symm
  obtain ⟨l, hl, he⟩ := natural_layer_transitive hnatural.2.1 hz.1 hzm hz1 hzm1
  have hc : l⁻¹ * m ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun a : G => l⁻¹ * a * m) he
    have he' : z * (l⁻¹ * m) = (l⁻¹ * m) * z := by
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
    exact he'.symm
  have ht : l⁻¹ * m ∈ (T : Subgroup G) := by
    rw [← A.equality_intersection_eq_sylow h611 hnatural hz horder hTH hbranch]
    exact ⟨hc, M.mul_mem (M.inv_mem (h611.L_le hl)) hm⟩
  have hh := (L ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hl) (mem_sup_right ht)
  simpa only [mul_inv_cancel_left] using hh

/-- The local Sylow action on D has displacement in the marked central line. -/
theorem LocalAnalysis.equality_centralizer_sylow_commutator
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ⁅equalityCentralizer L R z, (T : Subgroup G) ⊓ L⁆ ≤ zpowers z := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let D := equalityCentralizer L R z
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hHD : H ≤ normalizer (D : Set G) := by
    change H ≤ normalizer ((centralizer (K : Set H)).map H.subtype : Set G)
    have hh := (centralizer (K : Set H)).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hD : ⁅D, (T : Subgroup G) ⊓ L⁆ ≤ D :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans (hTH.trans hHD))
  have hV : ⁅D, (T : Subgroup G) ⊓ L⁆ ≤ layer L R := by
    rw [← A.equality_local_core_commutator h611 hnatural hz horder hTH hbranch]
    exact commutator_mono (A.equality_centralizer_le_local_core h611 hnatural hz hTH)
      inf_le_right
  exact (le_inf hD hV).trans (A.equality_centralizer_inf_layer h611 hz hp.core_center).le

/-- The fixed subgroup of D under the whole Sylow group is exactly the
marked central line, without an order bound on D. -/
theorem LocalAnalysis.equality_centralizer_sylow_fixed
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    equalityCentralizer L R z ⊓ centralizer (T : Set G) = zpowers z := by
  let D := equalityCentralizer L R z
  let : IsElementaryAbelian 2 D :=
    A.equality_centralizer_elementary h611 hnatural hz horder hTH hbranch
  apply le_antisymm
  · intro d hd
    rw [← A.central_omega]
    apply (omegaOneAmbient_le_iff ((T : Subgroup G) ⊓ centralizer (T : Set G)) _).mp le_rfl d
      ⟨A.equality_centralizer_le_sylow hTH hd.1, hd.2⟩
    exact elemPow_eq_one_of_isElementaryAbelian d (show d ∈ D from hd.1)
  · apply le_inf (equality_line_le_centralizer z L R)
    apply zpowers_le.mpr
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hTH ht)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
