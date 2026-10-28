module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.CubicTransport
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Excluding the actual paired Suzuki component orbit

Choose factor coordinates aligned with the Sylow intersection T₀. The covered
omega calculation and B.2.3(5) show that the lifted Borel normalizes Baum(Tᵥ),
including its centralizing kernel. The earlier 13.6.4–5 inputs place this Borel
in C_{M_V}(v). The actual V-action and its kernel give the superscript residual
chain O²(B) ≤ O^{2,3}(C_{M_V}(v)) ≤ C_M(V), hence the two-core commutator bound.

Transport the given cubic automorphism through the two central-quotient markings.
The arbitrary cubic detector applies in the aligned marking, so no compatibility
between Sylow alignment and a pure field action is required. The field-action
corollary constructs the full quotient automorphism from an actual cubic element;
only its action on the first factor must be specified.

These are conditional branch exclusions. The parent 13.6.6 assembly supplies the
actual component pair, Sylow subgroup and cubic actor, the elementary-center
multiplier and involution-lifting clauses of I.1.3 and I.2.2(4), and the earlier
local normalizer, action and module-kernel facts. No omega geometry, Borel
containment, commutator bound or compatible alignment remains as an input.

Only Borel normalization of Baum(Tᵥ) is used. The stronger printed normal-in-B
clause would also require Baum(Tᵥ) ≤ B; it is unnecessary for this contradiction
and is not inferred by discarding C_{Tᵥ}(K₀).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 13.6.6,
printed p.927 / PDF p.944; I.2.2(4), printed pp.409–411 / PDF pp.420–422.
-/

public section
open Subgroup CFSG.Quasithin.ChapterB Stellmacher BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] [Finite G]

/-- Exclude the moving pair using its actual nontrivial cubic quotient action.
The marking is arbitrary: the proof constructs its own aligned Borel and
transports the action, retaining both factor images and the full central kernel. -/
theorem PairFactors.false_of_cubic_action
    {T K L M V : Subgroup G} {v : G} {d : Marking T K v} (f : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (hS : baumann T ≤ Tv T v)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M)
    (haction : IsPiGroup twoThreePrimes (localAction V v).range)
    (hLC : Lv L v ≤ normalizer (M ⊓ centralizer (V : Set G) : Set G))
    (hCL : M ⊓ centralizer (V : Set G) ≤ normalizer (Lv L v : Set G))
    (hkernel : Lv L v ⊓ (M ⊓ centralizer (V : Set G)) ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (α : MulAut (SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter))
    (hα : α ^ 3 = 1) (hαne : α ≠ 1)
    (hcubic : ∀ x : orbit T K v,
      d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x) =
        α (d.quotientMap x)) : False := by
  obtain ⟨d', f', _, _, ha⟩ := f.exists_aligned P hP hKG
  let := f.orbit_center_elementary hKG hK
  have hB := f'.borel_le_localNormalizer P hP hKG hK hlift ha hS h1325 h1226 hMV
  have hcomm := commutator_le_twoCore d' (IsElementaryAbelian.isPGroup 2 _)
    hB hMV haction hLC hCL hkernel
  let e := d.equiv.symm.trans d'.equiv
  let β := MulAut.congr e α
  have hβ : β ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have hβne : β ≠ 1 := by
    intro he
    exact hαne ((MulAut.congr e).injective (he.trans (map_one _).symm))
  have hq (x : orbit T K v) : e (d.quotientMap x) = d'.quotientMap x := by
    change d'.equiv (d.equiv.symm (d.equiv _)) = d'.equiv _
    rw [d.equiv.symm_apply_apply]
  apply cubic_contradiction d' c hc hcN β hβ hβne _ hcomm
  intro x
  rw [← hq, hcubic]
  change e (α (d.quotientMap x)) = e (α (e.symm (d'.quotientMap x)))
  rw [← hq, e.symm_apply_apply]

/-- Source-facing application for an actual cubic element of Lᵥ inducing a
nontrivial cubic field automorphism on K/Z(K). The action on the second factor
and the compatible action after Sylow alignment are constructed, not assumed. -/
theorem PairFactors.false_of_cubic_field_action
    {T K L M V : Subgroup G} {v : G} {d : Marking T K v} (f : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (hS : baumann T ≤ Tv T v)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M)
    (haction : IsPiGroup twoThreePrimes (localAction V v).range)
    (hLC : Lv L v ≤ normalizer (M ⊓ centralizer (V : Set G) : Set G))
    (hCL : M ⊓ centralizer (V : Set G) ≤ normalizer (Lv L v : Set G))
    (hkernel : Lv L v ⊓ (M ⊓ centralizer (V : Set G)) ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (hc3 : c ^ 3 = 1)
    (σ : BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * d.parameter + 1) ≃ₐ[ZMod 2]
      BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * d.parameter + 1))
    (hσ : orderOf σ = 3)
    (hfield : ∀ x : orbit T K v,
      (d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x)).1 =
        suzukiFieldAut d.parameter σ (d.quotientMap x).1) : False := by
  let a := (orbit T K v).normalizerMonoidHom ⟨c, hcN⟩
  let α := MulAut.centralQuotientAction d.equiv a
  have hcN3 : (⟨c, hcN⟩ : normalizer (orbit T K v : Set G)) ^ 3 = 1 :=
    Subtype.ext hc3
  have ha3 : a ^ 3 = 1 := by rw [← map_pow, hcN3, map_one]
  have hα : α ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hact (x : orbit T K v) : d.quotientMap (a x) = α (d.quotientMap x) :=
    (MulAut.centralQuotientAction_apply d.equiv a x).symm
  have hαne : α ≠ 1 := by
    intro he
    have hs : suzukiFieldAut d.parameter σ = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨x, hx⟩ := d.quotientMap_surjective (y, 1)
      have hf := hfield x
      change (d.quotientMap (a x)).1 = _ at hf
      rw [hact, he, MulAut.one_apply, hx] at hf
      exact hf.symm
    have hσone : σ = 1 := (suzukiFieldAutHom_injective d.parameter)
      (by simpa only [suzukiFieldAutHom_apply, map_one] using hs)
    have : (1 : ℕ) = 3 := by simpa only [hσone, orderOf_one] using hσ
    omega
  exact f.false_of_cubic_action P hP hKG hK hlift hS h1325 h1226 hMV
    haction hLC hCL hkernel c hc hcN α hα hαne hact

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
