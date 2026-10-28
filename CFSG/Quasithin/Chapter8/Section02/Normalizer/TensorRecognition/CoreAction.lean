module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Kernel
public import Theory.GroupTheory.CentralizerModulo

/-!
# The canonical action and marked faithful quotient in 8.2.8(4)

The ambient group in this module is the local group Y = L_U I. Thus
normality of I and U is relative to Y, as in the source. Conjugation induces
a canonical action on the literal P/U, where P = O₂(I). Its kernel is the
preimage of the centralizer of the image of P in Y/U.

The earlier local calculations give the kernel on B/U, with B = V ∩ P;
E.2.14 gives C_I(P/U) = P and a centerless I/P. Together with two-conjugate
generation of P and 8.2.8(2), these imply O₂(Y) = P O₂(L_U) = C_Y(P/U).
We construct the faithful product image and then identify both factors with
their original two-core quotients. The final isomorphism sends the class of
r i to the pair of classes of r and i. No action or quotient equivalence is
assumed, and normality of L_U in Y follows from the commutator bound.

These are conditional deductions from the precise earlier inputs. Their
instantiation from the ambient Chapter 8 setup, and the noncubic tensor and
small-action recognition, remain with the source assembly.

Source: Aschbacher–Smith, Proposition 8.2.8(4), printed p.718 (PDF p.735).
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G : Type*} [Group G]
variable (I U : Subgroup G) [I.Normal] [U.Normal]
local instance : (I.pCoreIn 2).Normal := by unfold pCoreIn; infer_instance

private theorem core_quotient_conj_preserves (g : G) :
    (U.subgroupOf (I.pCoreIn 2)).map (MulAut.conjNormal g).toMonoidHom =
      U.subgroupOf (I.pCoreIn 2) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.Normal.conj_mem (inferInstance : U.Normal) _ hp g
  · intro p hp
    refine ⟨MulAut.conjNormal g⁻¹ p, Subgroup.Normal.conj_mem (inferInstance : U.Normal) _ hp g⁻¹, ?_⟩
    apply Subtype.ext
    change g * (g⁻¹ * (p : G) * (g⁻¹)⁻¹) * g⁻¹ = (p : G)
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-- Conjugation on the literal P/U with P=O₂(I). -/
def coreQuotientAction : G →* MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) where
  toFun g := QuotientGroup.congr _ _ (MulAut.conjNormal g) (core_quotient_conj_preserves I U g)
  map_one' := by
    ext p
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (I.pCoreIn 2)) p
    simp only [QuotientGroup.congr_mk', map_one, MulAut.one_apply]
  map_mul' g h := by
    ext p
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (I.pCoreIn 2)) p
    change QuotientGroup.mk' _ (MulAut.conjNormal (g * h) p) = _
    rw [map_mul]
    rfl

theorem coreQuotientAction_mk (g : G) (p : I.pCoreIn 2) :
    coreQuotientAction I U g (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p) =
      QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) (MulAut.conjNormal g p) := by
  exact QuotientGroup.congr_mk' _ _ (MulAut.conjNormal g)
    (core_quotient_conj_preserves I U g) p

theorem coreQuotientAction_kernel :
    (coreQuotientAction I U).ker = centralizerModulo ⊤ (I.pCoreIn 2) U := by
  ext g
  rw [mem_centralizerModulo_iff]
  simp only [mem_top, true_and]
  constructor
  · intro hg p hp
    have he := congrArg (fun a : MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) =>
      a (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) ⟨p, hp⟩))
      (MonoidHom.mem_ker.mp hg)
    rw [coreQuotientAction_mk] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    change (g * p * g⁻¹) / p ∈ U at hm
    have hc : ⁅g, p⁆ ∈ U := by simpa only [commutatorElement_def, div_eq_mul_inv] using hm
    simpa only [commutatorElement_inv] using U.inv_mem hc
  · intro hg
    apply MonoidHom.mem_ker.mpr
    ext q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (I.pCoreIn 2)) q
    rw [coreQuotientAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (g * (p : G) * g⁻¹) / (p : G) ∈ U
    have hc : ⁅g, (p : G)⁆ ∈ U := by
      simpa only [commutatorElement_inv] using U.inv_mem (hg p p.property)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hc

/-- E.2.14's literal centralizer equality gives the kernel of the restricted action. -/
theorem coreQuotientAction_restrict_kernel
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2) :
    ((coreQuotientAction I U).comp I.subtype).ker = pCore 2 I := by
  have he : I ⊓ (coreQuotientAction I U).ker = I.pCoreIn 2 := by
    rw [coreQuotientAction_kernel]
    simpa only [centralizerModulo, top_inf_eq] using hI
  apply (map_injective I.subtype_injective)
  change ((coreQuotientAction I U).ker.subgroupOf I).map I.subtype = _
  rw [subgroupOf_map_subtype, inf_comm]
  exact he

/-- The exact source kernel equality and faithful product image, with the action constructed. -/
theorem coreQuotientAction_recognition [Finite G]
    (R V : Subgroup G)
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2)
    (hcenter : center (I ⧸ pCore 2 I) = ⊥) :
    pCore 2 G = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
      centralizerModulo ⊤ (I.pCoreIn 2) U = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
      ∃ e : R.map (coreQuotientAction I U) × I.map (coreQuotientAction I U) ≃*
          (coreQuotientAction I U).range,
        ∀ r i, (e (r, i) : MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) =
          (r : MulAut _) * (i : MulAut _) := by
  let : R.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le R.le_normalizer
      (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 R)))))
  have hs := pairSection_kernel R I V U hgen h hP hcomm hB
    (coreQuotientAction I U) (coreQuotientAction_mk I U)
    (coreQuotientAction_restrict_kernel I U hI) hcenter
  rwa [coreQuotientAction_kernel] at hs

/-- The faithful quotient is the product of the two actual action images.
The displayed formula identifies the images of representatives from both factors. -/
theorem coreQuotientAction_faithful_product [Finite G]
    (R V : Subgroup G)
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2)
    (hcenter : center (I ⧸ pCore 2 I) = ⊥) :
    ∃ e : (G ⧸ pCore 2 G) ≃*
        R.map (coreQuotientAction I U) × I.map (coreQuotientAction I U),
      ∀ (r : R) (i : I), e (QuotientGroup.mk' (pCore 2 G) ((r : G) * (i : G))) =
        (⟨coreQuotientAction I U r, mem_map_of_mem _ r.property⟩,
          ⟨coreQuotientAction I U i, mem_map_of_mem _ i.property⟩) := by
  obtain ⟨hp, hc, e, he⟩ := coreQuotientAction_recognition I U R V hgen h hP hcomm hB hI hcenter
  let f := coreQuotientAction I U
  have hk : pCore 2 G = f.ker := hp.trans (hc.symm.trans (coreQuotientAction_kernel I U).symm)
  let q : (G ⧸ pCore 2 G) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange f)
  refine ⟨q.trans e.symm, ?_⟩
  intro r i
  apply e.injective
  change e (e.symm (q _)) = _
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change f ((r : G) * (i : G)) = _
  rw [he, map_mul]

/-- Both product factors are the literal two-core quotients, with their quotient maps marked. -/
theorem coreQuotientAction_quotient_product [Finite G]
    (R V : Subgroup G)
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2)
    (hcenter : center (I ⧸ pCore 2 I) = ⊥) :
    ∃ e : (G ⧸ pCore 2 G) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
      ∀ (r : R) (i : I), e (QuotientGroup.mk' (pCore 2 G) ((r : G) * (i : G))) =
        (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) i) := by
  let f := coreQuotientAction I U
  obtain ⟨hp, hc, _⟩ := coreQuotientAction_recognition I U R V hgen h hP hcomm hB hI hcenter
  have hfker : f.ker = I.pCoreIn 2 ⊔ R.pCoreIn 2 := (coreQuotientAction_kernel I U).trans hc
  have hR : (f.comp R.subtype).ker = pCore 2 R := by
    ext r
    constructor
    · intro hr
      apply (hB r).mp
      intro b
      have he := congrArg
        (fun a : MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) =>
          a (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) ⟨b, b.property.2⟩))
        (show f (r : G) = 1 from hr)
      rw [coreQuotientAction_mk] at he
      have hb := QuotientGroup.eq_iff_div_mem.mp he
      change ((r : G) * (b : G) * (r : G)⁻¹) / (b : G) ∈ U at hb
      simpa only [commutatorElement_def, div_eq_mul_inv] using hb
    · intro hr
      change (r : G) ∈ f.ker
      rw [hfker]
      exact mem_sup_right (mem_map_of_mem R.subtype hr)
  let eR : (R ⧸ pCore 2 R) ≃* R.map f :=
    (QuotientGroup.quotientMulEquivOfEq hR.symm).trans
      ((QuotientGroup.quotientKerEquivRange (f.comp R.subtype)).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))
  let eI : (I ⧸ pCore 2 I) ≃* I.map f :=
    (QuotientGroup.quotientMulEquivOfEq (coreQuotientAction_restrict_kernel I U hI).symm).trans
      ((QuotientGroup.quotientKerEquivRange (f.comp I.subtype)).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))
  obtain ⟨e, he⟩ := coreQuotientAction_faithful_product I U R V hgen h hP hcomm hB hI hcenter
  refine ⟨e.trans (eR.symm.prodCongr eI.symm), ?_⟩
  intro r i
  change (eR.symm.prodCongr eI.symm) (e _) = _
  rw [he]
  apply Prod.ext
  · change eR.symm _ = _
    apply eR.injective
    rw [eR.apply_symm_apply]
    rfl
  · change eI.symm _ = _
    apply eI.injective
    rw [eI.apply_symm_apply]
    rfl
end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
