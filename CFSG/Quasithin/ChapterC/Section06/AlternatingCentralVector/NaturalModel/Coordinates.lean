module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.Quotient
public import Theory.Representation.BinaryPermutation.SevenMarkedAction
public import Theory.Representation.BinaryPermutationMulAction

/-!
# The original S₇ marking on the actual A₇ block module

Vanishing of the fixed layer lifts the defining block coordinates to U.
The supplied quotient map induces a marking of K/O₂(K); Aut(A₇)=S₇ then
aligns the lifted coordinates with it. Triviality of the natural commutant
extends this exact action formula from K to K S.

Source: Aschbacher–Smith C.1.13(c), B.3.3(1), C.6.4, pp.167–168.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

theorem Input.quotientMap_block_ker (d : Input K R S Λ) :
    (d.quotientMap.comp (inclusion (show K ≤ K ⊔ S from le_sup_left))).ker = pCore 2 K := by
  ext k
  change d.quotientMap (inclusion le_sup_left k) = 1 ↔ k ∈ pCore 2 K
  have hk : d.quotientMap (inclusion le_sup_left k) = 1 ↔
      (k : G) ∈ (K ⊔ S).pCoreIn 2 := by
    change inclusion le_sup_left k ∈ d.quotientMap.ker ↔ _
    rw [d.quotientMap_ker]
    constructor
    · exact fun h => mem_map_of_mem (K ⊔ S).subtype h
    · rintro ⟨v,hv,he⟩
      exact (Subtype.ext he : v = inclusion le_sup_left k) ▸ hv
  rw [hk, d.core_eq_full_centralizer, mem_inf,
    and_iff_right (show (k : G) ∈ K ⊔ S from (show K ≤ K ⊔ S from le_sup_left) k.property),
    ← d.block.2.1.centralizer_blockU]
  constructor
  · intro h u hu
    exact Subtype.ext (h u (mem_map_of_mem K.subtype hu))
  · intro h u hu
    obtain ⟨v,hv,rfl⟩ := hu
    exact congrArg Subtype.val (h v hv)

/-- The block quotient marking induced by the specified S₇ quotient. -/
def Input.blockQuotientIso (d : Input K R S Λ) :
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) := by
  let b := d.quotientMap.comp (inclusion (show K ≤ K ⊔ S from le_sup_left))
  have hb : b.range = alternatingGroup (Fin 7) := by
    rw [← d.quotientMap_block]
    ext g
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨inclusion le_sup_left k,k.property,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq d.quotientMap_block_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange b).trans (MulEquiv.subgroupCongr hb))

theorem Input.blockQuotientIso_mk (d : Input K R S Λ) (k : K) :
    (d.blockQuotientIso (QuotientGroup.mk' (pCore 2 K) k) : Equiv.Perm (Fin 7)) =
      d.quotientMap (inclusion le_sup_left k) := rfl

/-- Coordinates on the actual U, with precisely the supplied quotient marking on K. -/
theorem Input.exists_marked_block_coordinates (d : Input K R S Λ) :
    ∃ e : (blockU K).map K.subtype ≃* Multiplicative (core (Fin 7)),
      ∀ (k : K) (v : (blockU K).map K.subtype),
        (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 7)
          (d.quotientMap (inclusion le_sup_left k)) (e v).toAdd)) : G) =
          (k : G) * (v : G) * (k : G)⁻¹ := by
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := d.block.2.2
  let a := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let eU := (blockU K).equivMapOfInjective K.subtype K.subtype_injective
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed K)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', d.block.seven_fixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let eQ := MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed K)) hq
  let e₀ := eU.symm.trans (eQ.trans m.moduleIso)
  have he₀ (k : K) (v : (blockU K).map K.subtype) :
      e₀ (eU (blockConjugate K k (eU.symm v))) = naturalMulAction (Fin 7) (a k).val (e₀ v) := by
    change m.moduleIso (eQ (eU.symm (eU (blockConjugate K k (eU.symm v))))) = _
    rw [eU.symm_apply_apply]
    change m.moduleIso (QuotientGroup.mk' _ (blockConjugate K k (eU.symm v))) = _
    rw [m.intertwining]
    apply Multiplicative.toAdd.injective
    exact hρ (a k) (e₀ v)
  let θ : MulAut (alternatingGroup (Fin 7)) := m.quotientIso.symm.trans d.blockQuotientIso
  obtain ⟨σ,hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).2 θ
  have hmark (k : K) : d.quotientMap (inclusion le_sup_left k) =
      σ * (a k).val * σ⁻¹ := by
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin 7)) => (f (a k)).val) hσ
    change σ * (a k).val * σ⁻¹ = (d.blockQuotientIso (m.quotientIso.symm (a k))).val at h
    simpa only [a, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      m.quotientIso.symm_apply_apply, d.blockQuotientIso_mk] using h.symm
  let c := (coreEquivNatural (Fin 7) (by decide)).toAddEquiv.toMultiplicative
  let e := (e₀.trans (naturalMulAction (Fin 7) σ)).trans c.symm
  refine ⟨e, ?_⟩
  intro k v
  have he (w : Multiplicative (core (Fin 7))) (g : Equiv.Perm (Fin 7)) :
      c (Multiplicative.ofAdd (coreRepresentation (Fin 7) g w.toAdd)) =
        naturalMulAction (Fin 7) g (c w) := by
    apply Multiplicative.toAdd.injective
    exact coreEquivNatural_equivariant (Fin 7) (by decide) g w.toAdd
  have hev : e (eU (blockConjugate K k (eU.symm v))) =
      Multiplicative.ofAdd (coreRepresentation (Fin 7)
        (d.quotientMap (inclusion le_sup_left k)) (e v).toAdd) := by
    apply c.injective
    rw [he]
    change c (c.symm (naturalMulAction (Fin 7) σ (e₀ _))) =
      naturalMulAction (Fin 7) _ (c (c.symm (naturalMulAction (Fin 7) σ (e₀ v))))
    rw [c.apply_symm_apply, c.apply_symm_apply, he₀, hmark]
    change ((naturalMulAction (Fin 7) σ) * (naturalMulAction (Fin 7) (a k).val)) (e₀ v) =
      ((naturalMulAction (Fin 7) (σ * (a k).val * σ⁻¹)) * naturalMulAction (Fin 7) σ) (e₀ v)
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  rw [← hev,e.symm_apply_apply]
  have hv : (((eU.symm v : blockU K) : K) : G) = v :=
    congrArg Subtype.val (eU.apply_symm_apply v)
  change (k : G) * (((eU.symm v : blockU K) : K) : G) * (k : G)⁻¹ = _
  rw [hv]

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector

namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
open BinaryPermutation.SevenMarkedAction
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

omit [Finite G] in
theorem Input.normalizes_module (d : Input K R S Λ) :
    K ⊔ S ≤ normalizer ((blockU K).map K.subtype : Set G) :=
  d.normalizes_block.trans (normalizer_le_normalizer_characteristic_image K (blockU K))

/-- The actual H-conjugation action in coordinates with the original quotient marking. -/
theorem Input.exists_marked_coordinates (d : Input K R S Λ) :
    ∃ e : (blockU K).map K.subtype ≃* Multiplicative (core (Fin 7)),
      ∀ (h : (K ⊔ S : Subgroup G)) (v : (blockU K).map K.subtype),
        (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 7)
          (d.quotientMap h) (e v).toAdd)) : G) =
          (h : G) * (v : G) * (h : G)⁻¹ := by
  obtain ⟨e,he⟩ := d.exists_marked_block_coordinates
  let U := (blockU K).map K.subtype
  let α : (K ⊔ S : Subgroup G) →* MulAut (Multiplicative (core (Fin 7))) :=
    (MulAut.congr e).toMonoidHom.comp
      (U.normalizerMonoidHom.comp (inclusion d.normalizes_module))
  let : (K.subgroupOf (K ⊔ S)).Normal := normal_subgroupOf_of_le_normalizer d.normalizes_block
  have hα : ∀ k : K.subgroupOf (K ⊔ S), α k = coreAction (d.quotientMap k) := by
    intro k
    let k₀ : K := ⟨k.val,k.property⟩
    apply MulEquiv.ext
    intro v
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e (U.normalizerMonoidHom (inclusion d.normalizes_module k.val) (e.symm v))) : G) = _
    rw [e.symm_apply_apply]
    exact (he k₀ (e.symm v)).symm.trans (by rw [e.apply_symm_apply]; rfl)
  have ha := extension_eq (K.subgroupOf (K ⊔ S)) d.quotientMap d.quotientMap_block α hα
  refine ⟨e, ?_⟩
  intro h v
  have hh := DFunLike.congr_fun (DFunLike.congr_fun ha h) (e v)
  change e (U.normalizerMonoidHom (inclusion d.normalizes_module h) (e.symm (e v))) = _ at hh
  rw [e.symm_apply_apply] at hh
  change (e.symm (coreAction (d.quotientMap h) (e v)) : G) = _
  simp only [MonoidHom.comp_apply] at hh
  rw [← hh,e.symm_apply_apply]
  rfl

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
