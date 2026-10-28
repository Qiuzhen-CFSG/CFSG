module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionTransferGeometry
public import Theory.GroupTheory.ElementaryQuotientCocycles

/-!
# Lifting involution fusion through the natural layer

The natural normalizer has no binary transvections. Thus a nontrivial actor
fixes at most four vectors of V. For an involution, rank-nullity gives the
opposite square-root bound, so the fixed subgroup equals the displacement
subgroup. Every involution in the same V-coset is consequently conjugate
by V, without a splitting assumption for the extension.

These results are applied to the literal source quotient in
`RankOneModuleRecognitionIdentificationEqualityExtensionInvolutionFusion`.
Source: Aschbacher–Smith, proof of 6.2.13, printed p.688.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private theorem elementary_coset_fusion (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (han : a ∈ normalizer (V : Set G))
    (hc : Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ 4)
    (hab : b * a⁻¹ ∈ V) : IsConj a b := by
  let α := (V.normalizerMonoidHom ⟨a,han⟩).toMonoidHom
  have hα (v : V) : α (α v) = v := by
    apply Subtype.ext
    change a * (a * v.val * a⁻¹) * a⁻¹ = v.val
    calc
      _ = a ^ 2 * v.val * (a ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = v.val := by rw [ha]; simp
  have hi (v : V) : v⁻¹ = v := by
    apply inv_eq_of_mul_eq_one_left
    exact (show v*v=1 from by simpa only [pow_two] using
      (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val v.property) : v^2=1))
  let δ : V →* V := MonoidHom.id V / α
  have hk : δ.ker = α.eqLocus (MonoidHom.id V) := by
    ext v
    change v / α v = 1 ↔ α v = v
    rw [div_eq_one,eq_comm]
  have hr : δ.range ≤ δ.ker := by
    rintro _ ⟨v,rfl⟩
    change v / α v / α (v / α v) = 1
    rw [div_eq_one,map_div,hα]
    simp only [div_eq_mul_inv,hi,mul_comm]
  have hmap : (α.eqLocus (MonoidHom.id V)).map V.subtype =
      V ⊓ centralizer ({a} : Set G) := by
    ext v
    constructor
    · rintro ⟨v,hv,rfl⟩
      refine ⟨v.property,mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := congrArg Subtype.val hv
      change a*v.val*a⁻¹=v.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · rintro ⟨hv,hc⟩
      refine ⟨⟨v,hv⟩,?_,rfl⟩
      apply Subtype.ext
      change a*v*a⁻¹=v
      rw [(mem_centralizer_singleton_iff.mp hc).symm,mul_inv_cancel_right]
  have hkc : Nat.card δ.ker ≤ 4 := by
    rw [hk,←card_map_of_injective V.subtype_injective,hmap]
    exact hc
  have he : Nat.card (α.eqLocus (MonoidHom.id V)) ^ 2 = Nat.card V := by
    have hh := δ.ker.card_mul_index
    rw [index_ker,hV] at hh
    have hh' := card_le_of_le hr
    rw [←hk,hV]
    nlinarith
  let x : V := ⟨b*a⁻¹,hab⟩
  have hfix : α x = x := by
    have hx : x * α x = 1 := by
      apply Subtype.ext
      change (b*a⁻¹)*(a*(b*a⁻¹)*a⁻¹)=1
      calc
        _ = b^2*(a^2)⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [ha,hb]; simp
    exact (eq_inv_of_mul_eq_one_right hx).trans (hi x)
  obtain ⟨v,hv⟩ := elementary_fixed_is_coboundary α hα he x hfix
  apply isConj_iff.mpr
  refine ⟨v.val,?_⟩
  have hh := congrArg Subtype.val hv
  change b*a⁻¹=v.val*(a*v.val⁻¹*a⁻¹) at hh
  have hh' := congrArg (fun w : G => w*a) hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'.symm

/-- Every nontrivial involution actor on the natural layer fixes at most four points. -/
theorem LocalAnalysis.equality_involution_fixed_bound
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    {a : G} (ha : a ∈ M) (haQ : a ∉ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    Nat.card (layer L R ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ 4 := by
  let V := layer L R
  let B := V ⊓ centralizer ({a} : Set G)
  let C := zpowers a
  let := h611.layer_elementary
  have hn : C ≤ normalizer (V : Set G) := zpowers_le.mpr
    (A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch ha)
  have hlarge : ¬ 8 ≤ Nat.card B := by
    intro h8
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,show Nat.card V = 16 from hnatural.2.1.card] at hh
    have hi : B.relIndex V ≤ 2 := by nlinarith
    have hcor : ChapterE.subgroupCorank V B ≤ 1 := by
      unfold ChapterE.subgroupCorank
      interval_cases he : B.relIndex V <;> decide
    have hc : C ≤ centralizer (V : Set G) := by
      apply (ChapterE.inducedAutomizer_eq_bot_iff hn).mp
      apply eq_bot_iff.mpr
      intro x hx
      by_contra hne
      have hlo := natural_automizer_fixedCodim_ge hnatural.2.1
        (A.normalizer_layer.trans ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal))
        (show x ≠ 1 by simpa only [mem_bot] using hne)
      have hmid := ChapterE.fixedCodim_mono (ChapterE.automizerRepresentation V)
        (zpowers_le.mpr hx)
      have hhi : Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation V)
          (ChapterE.inducedAutomizer V C) ≤ ChapterE.subgroupCorank V B := by
        rw [ChapterE.fixedCodim_inducedAutomizer V C hn]
        apply ChapterE.Section06.subgroupCorank_antitone
        refine le_inf inf_le_left ?_
        intro b hb
        rintro c ⟨i,rfl⟩
        exact ((show Commute a b from (mem_centralizer_singleton_iff.mp hb.2).symm).zpow_left i).eq
      change 2 ≤ Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation V) (zpowers x) at hlo
      omega
    apply haQ
    have h : a ∈ M ⊓ centralizer (V : Set G) := ⟨ha,hc (mem_zpowers a)⟩
    rwa [A.equality_maximal_layer_centralizer h611 hnatural hz horder hTH hbranch] at h
  have hd : Nat.card B ∣ 16 := by
    have hh := card_dvd_of_le (show B ≤ V from inf_le_left)
    rwa [show Nat.card V = 16 from hnatural.2.1.card] at hh
  have harith : ∀ b : ℕ, b < 8 → b ∣ 16 → b ≤ 4 := by decide +kernel
  change Nat.card B ≤ 4
  exact harith _ (by omega) hd

/-- Lift involution conjugacy across the literal natural layer, without a splitting premise. -/
theorem LocalAnalysis.equality_involution_coset_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    {a b : G} (ha : a ∈ M) (haQ : a ∉ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (ha2 : a^2=1) (hb2 : b^2=1) (hab : b*a⁻¹ ∈ layer L R) : IsConj a b := by
  let := h611.layer_elementary
  exact elementary_coset_fusion (layer L R) hnatural.2.1.card a b ha2 hb2
    (A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch ha)
    (A.equality_involution_fixed_bound h611 hnatural hz horder hTH hbranch ha haQ) hab
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
