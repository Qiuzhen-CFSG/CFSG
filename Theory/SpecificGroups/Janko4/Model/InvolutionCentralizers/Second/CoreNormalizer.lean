module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualElementary
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.GroupTheory.SylowKernelCore

/-!
# The normalizer of the full second J₄ centralizer core

The original two-core embeds as the literal order-2048 max1 kernel. Its
normalizer is the native Mathieu local subgroup. A normal overgroup of this
kernel which is not a two-group surjects onto the simple M₂₄ quotient, and
therefore equals that whole local subgroup. The marked involution then has
centralizer index 276.

Native involution fusion transports the calculation to every involution
whose full centralizer core has order 2048, and to specified isomorphic
carriers. The full core and the original involution remain aligned.

Source: GLS3 Table 5.3i; Aschbacher–Smith 4.4.3, printed p.623. The actual
ATLAS matrices and local subgroup words retain their attribution through
the imported native centralizer and normalizer calculations.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.InvolutionCentralizers.Second
open Janko4 Cardinality
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed

 private theorem embedded_core : (pCore 2 ambientCentralizer).map ambientCentralizer.subtype =
    max1Kernel.map Local.subtype := by
  rw [ambient_twoCore_eq_kernel,ambientKernel_eq_map,map_map]
  have he : ambientCentralizer.subtype.comp ambientEquivLocal.symm.toMonoidHom =
      Local.subtype.comp localCentralizer.subtype := rfl
  rw [he,←map_map,map_subgroupOf_eq_of_le max1Kernel_le_localCentralizer]

 private theorem core_normalizer : normalizer ((pCore 2 ambientCentralizer).map
    ambientCentralizer.subtype : Set Model) = Local := by
  rw [embedded_core]
  apply le_antisymm LocalStructure.normalizer_embedded_localKernel_le_max1
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    max1Kernel.le_normalizer_map Local.subtype

 private theorem normal_core_overgroup_eq (F : Subgroup Model)
    (hEF : max1Kernel.map Local.subtype ≤ F)
    (hFM : F ≤ Local) (hn : Local ≤ normalizer (F : Set Model))
    (hF : ¬ IsPGroup 2 F) : F = Local := by
  let U := F.subgroupOf Local
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let q := (LocalStructure.localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' max1Kernel)
  have hq : Function.Surjective q := (LocalStructure.localQuotientEquivM24 _ _).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = max1Kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _ (LocalStructure.localQuotientEquivM24 _ _).injective,
      QuotientGroup.ker_mk']
  let := Sporadic.Mathieu.m24_isSimpleGroup
  let : (U.map q).Normal := (inferInstance : U.Normal).map q hq
  have ht : U.map q = ⊤ := (inferInstance : (U.map q).Normal).eq_bot_or_eq_top.resolve_left (by
    intro hb
    have hu : U ≤ max1Kernel := hk ▸ (map_eq_bot_iff U).mp hb
    have hp : IsPGroup 2 U := (IsPGroup.of_card (n := 11) (localKernel_card _ _)).to_le hu
    exact hF (hp.of_equiv (subgroupOfEquivOfLe hFM)))
  have hu : U = ⊤ := by
    have hh := congrArg (comap q) ht
    rw [comap_map_eq,hk,sup_eq_left.mpr (fun x hx => hEF (mem_map_of_mem Local.subtype hx)),comap_top] at hh
    exact hh
  have hh := congrArg (map Local.subtype) hu
  rwa [map_subgroupOf_eq_of_le hFM,←MonoidHom.range_eq_map,range_subtype] at hh

end Janko4.InvolutionCentralizers.Second
namespace Janko4.InvolutionCentralizers
open Cardinality
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed
private theorem seed_conjugacy : IsConj (Second.seed : Model) ((a * b * a * b * b)^5) := by
  obtain ⟨g,hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha,hb] at hg
  have hw : Simplicity.word a b "ababb" = a*b*a*b*b := by simp [Simplicity.word,mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g,hg.symm⟩

 private theorem second_marking_of_core_card (z : Model) (hz : orderOf z = 2)
    (hcard : Nat.card (pCore 2 (centralizer ({z} : Set Model))) = 2048) :
    ∃ b : MulAut Model, b z = (Second.seed : Model) := by
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hz with hc | hc
  · obtain ⟨g,hg⟩ := isConj_iff.mp hc.symm
    let b := MulAut.conj g
    have he : (centralizer ({z} : Set Model)).map b.toMonoidHom = First.centralizer := by
      rw [map_centralizer_equiv,Set.image_singleton]
      exact congrArg (fun t : Model => centralizer ({t} : Set Model)) hg
    let d := (b.subgroupMap (centralizer ({z} : Set Model))).trans (MulEquiv.subgroupCongr he)
    have hh := congrArg (fun P : Subgroup First.centralizer => Nat.card P) (pCore_map_iso 2 d)
    rw [card_map_of_injective d.injective,First.centralizer_twoCore_card,hcard] at hh
    norm_num at hh
  · obtain ⟨g,hg⟩ := isConj_iff.mp (seed_conjugacy.trans hc).symm
    exact ⟨MulAut.conj g,hg⟩
end Janko4.InvolutionCentralizers
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel Cardinality.localKernelSeed
/-- The marked centralizer has index 276 in the full normalized overgroup. -/
theorem core_normalizer_overgroup_index (z : Model) (hz : orderOf z = 2)
    (hcard : Nat.card (pCore 2 (centralizer ({z} : Set Model))) = 2048)
    (F : Subgroup Model)
    (hEF : (centralizer ({z} : Set Model)).pCoreIn 2 ≤ F)
    (hFN : F ≤ normalizer ((centralizer ({z} : Set Model)).pCoreIn 2 : Set Model))
    (hnF : normalizer ((centralizer ({z} : Set Model)).pCoreIn 2 : Set Model) ≤ normalizer (F : Set Model))
    (hF : ¬ IsPGroup 2 F) : (centralizer ({z} : Set Model)).relIndex F = 276 := by
  obtain ⟨b,hb⟩ := second_marking_of_core_card z hz hcard
  let C := centralizer ({z} : Set Model)
  have hC : C.map b.toMonoidHom = Second.ambientCentralizer := by
    rw [map_centralizer_equiv,Set.image_singleton,hb]
    rfl
  have hE : (C.pCoreIn 2).map b.toMonoidHom = Second.max1Kernel.map Second.Local.subtype := by
    rw [map_pCoreIn_of_injective 2 _ _ b.injective,hC]
    exact Second.embedded_core
  have hN : (normalizer (C.pCoreIn 2 : Set Model)).map b.toMonoidHom = Second.Local := by
    rw [Subgroup.map_equiv_normalizer_eq,hE,←Second.embedded_core,Second.core_normalizer]
  have hFm : F.map b.toMonoidHom = Second.Local := by
    apply Second.normal_core_overgroup_eq
    · exact hE ▸ map_mono hEF
    · exact hN ▸ map_mono hFN
    · rw [←hN,←Subgroup.map_equiv_normalizer_eq]
      exact map_mono hnF
    · intro hp
      exact hF (hp.of_equiv (b.subgroupMap F).symm)
  have hi := relIndex_map_map_of_injective (f := b.toMonoidHom) C F b.injective
  rw [hC,hFm] at hi
  rw [←hi]
  have hh := (Second.ambientCentralizer.subgroupOf Second.Local).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe Second.ambient_le_max1).toEquiv,
    Second.ambient_card,Cardinality.max1Subgroup_card] at hh
  change (Second.ambientCentralizer.subgroupOf Second.Local).index = 276
  omega
end Janko4.InvolutionCentralizers
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB
/-- Transport the index with the entire core and the original involution. -/
theorem core_normalizer_overgroup_index_of_equiv {X : Type*} [Group X] [Finite X]
    (e : X ≃* Model) (z : X) (hz : orderOf z = 2)
    (hcard : Nat.card (pCore 2 (centralizer ({z} : Set X))) = 2048)
    (F : Subgroup X)
    (hEF : (centralizer ({z} : Set X)).pCoreIn 2 ≤ F)
    (hFN : F ≤ normalizer ((centralizer ({z} : Set X)).pCoreIn 2 : Set X))
    (hnF : normalizer ((centralizer ({z} : Set X)).pCoreIn 2 : Set X) ≤ normalizer (F : Set X))
    (hF : ¬ IsPGroup 2 F) : (centralizer ({z} : Set X)).relIndex F = 276 := by
  let C := centralizer ({z} : Set X)
  have hC : C.map e.toMonoidHom = centralizer ({e z} : Set Model) := by
    rw [map_centralizer_equiv,Set.image_singleton]
  have hE : (C.pCoreIn 2).map e.toMonoidHom = (centralizer ({e z} : Set Model)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ e.injective,hC]
  have hN := (C.pCoreIn 2).map_equiv_normalizer_eq e
  rw [hE] at hN
  let d := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  have hsize : Nat.card (pCore 2 (centralizer ({e z} : Set Model))) = 2048 := by
    rw [←pCore_map_iso 2 d,card_map_of_injective d.injective,hcard]
  have hh := core_normalizer_overgroup_index (e z) ((e.orderOf_eq z).trans hz) hsize
    (F.map e.toMonoidHom) (hE ▸ map_mono hEF) (hN ▸ map_mono hFN)
    (by rw [←hN,←Subgroup.map_equiv_normalizer_eq]; exact map_mono hnF)
    (fun hp => hF (hp.of_equiv (e.subgroupMap F).symm))
  rw [←hC,relIndex_map_map_of_injective (f := e.toMonoidHom) C F e.injective] at hh
  exact hh
end Janko4.InvolutionCentralizers
