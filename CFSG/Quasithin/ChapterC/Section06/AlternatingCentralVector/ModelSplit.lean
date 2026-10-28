module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.Definitions
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.CoreSplit
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The ordinary A₇ core split in C.6.4

The residual hypothesis makes K normal in H = K S. The short-block
centralizer calculation identifies O₂(H) with C_H(U). Vanishing first
cohomology for the ordinary A₇ natural module splits that core as
U times its block centralizer. All subgroups retain their original
ambient embeddings; the quotient map retains the supplied S₇ marking.

Source: Aschbacher–Smith C.1.13(c), C.6.2–4, printed pp.125,166–168.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- The actual quotient map, with the marking supplied by the input. -/
def Input.quotientMap (d : Input K R S Λ) :
    (K ⊔ S : Subgroup G) →* Equiv.Perm (Fin 7) :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K ⊔ S : Subgroup G)))

omit [Finite G] in
theorem Input.normalizes_block (d : Input K R S Λ) :
    K ⊔ S ≤ normalizer (K : Set G) := by
  have h := (pResidual 2 (K ⊔ S : Subgroup G)).le_normalizer_map (K ⊔ S).subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
    d.residual] using h

omit [Finite G] in
theorem Input.normalizes_core (_d : Input K R S Λ) :
    K ⊔ S ≤ normalizer ((K ⊔ S).pCoreIn 2 : Set G) :=
  (K ⊔ S).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

private theorem normal_short_extension_centralizer (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) :
    (K ⊔ T) ⊓ centralizer ((blockU K).map K.subtype : Set G) = (K ⊔ T).pCoreIn 2 := by
  let A := K ⊔ T
  let C := A ⊓ centralizer ((blockU K).map K.subtype : Set G)
  have hAK : A ≤ normalizer (K : Set G) := sup_le K.le_normalizer hn
  have hAQ : A ≤ normalizer (A.pCoreIn 2 : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hAU : A ≤ normalizer ((blockU K).map K.subtype : Set G) :=
    hAK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hQC : A.pCoreIn 2 ≤ centralizer ((blockU K).map K.subtype : Set G) :=
    hK.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 A)
      (le_sup_left.trans hAQ) ((pCoreIn_le 2 A).trans hAK)
  refine le_antisymm ?_ (le_inf (pCoreIn_le 2 A) hQC)
  let K₀ := K.subgroupOf A
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hAK
  have hgen : K₀ ⊔ T.subgroupOf A = ⊤ := by
    change K.subgroupOf A ⊔ T.subgroupOf A = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self A
  have hquot : IsPGroup 2 (A ⧸ K₀) :=
    isPGroup_quotient_of_sup_eq_top K₀ (T.subgroupOf A) hT.comap_subtype hgen
  have hLC : K ⊓ centralizer ((blockU K).map K.subtype : Set G) ≤ K.pCoreIn 2 := by
    rintro k ⟨hk,hc⟩
    refine ⟨⟨k,hk⟩,hK.centralizer_blockU.le ?_,rfl⟩
    intro u hu
    exact Subtype.ext (hc u (mem_map_of_mem K.subtype hu))
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨n,hn⟩ := hquot (QuotientGroup.mk' K₀ ⟨c,c.property.1⟩)
    have hcK : (c : G) ^ 2 ^ n ∈ K := by
      have hh : (⟨c,c.property.1⟩ : A) ^ 2 ^ n ∈ K₀ := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' K₀ ((⟨c,c.property.1⟩ : A) ^ 2 ^ n) = 1
        rwa [map_pow]
      exact hh
    have hcO := hLC ⟨hcK,(centralizer ((blockU K).map K.subtype : Set G)).pow_mem c.property.2 _⟩
    obtain ⟨m,hm⟩ := isPGroup_pCoreIn 2 K ⟨_,hcO⟩
    refine ⟨n+m,Subtype.ext ?_⟩
    change (c : G) ^ 2 ^ (n+m) = 1
    rw [pow_add,pow_mul]
    exact congrArg Subtype.val hm
  exact le_pCoreIn_of_normalizes hCp inf_le_left
    ((le_inf A.le_normalizer (hAU.trans (normalizer_le_normalizer_centralizer ((blockU K).map K.subtype)))).trans
      inf_normalizer_le_normalizer_inf)

/-- The core is exactly the module centralizer inside the source overgroup. -/
theorem Input.core_eq_full_centralizer (d : Input K R S Λ) :
    (K ⊔ S).pCoreIn 2 =
      (K ⊔ S) ⊓ centralizer ((blockU K).map K.subtype : Set G) :=
  (normal_short_extension_centralizer K S d.block.2.1 d.S_two
    (le_sup_right.trans d.normalizes_block)).symm

/-- C.6.3(3)(a), on the original subgroup R. -/
theorem Input.core_eq_centralizer (d : Input K R S Λ) :
    (K ⊔ S).pCoreIn 2 = R ⊓ centralizer ((blockU K).map K.subtype : Set G) := by
  have h := d.core_eq_full_centralizer
  exact le_antisymm (le_inf d.core_le (h.le.trans inf_le_right))
    ((inf_le_inf (d.R_le_S.trans le_sup_right) le_rfl).trans h.ge)

/-- The original U lies in the two-core, hence in R. -/
theorem Input.module_le_core (d : Input K R S Λ) :
    (blockU K).map K.subtype ≤ (K ⊔ S).pCoreIn 2 := by
  let : IsElementaryAbelian 2 ((blockU K).map K.subtype) := d.block.2.1.elementary.map K.subtype
  rw [d.core_eq_full_centralizer]
  exact le_inf ((map_subtype_le _).trans le_sup_left) (le_centralizer _)

/-- The literal centralizer D lies in Q. -/
theorem Input.block_centralizer_le_core (d : Input K R S Λ) :
    R ⊓ centralizer (K : Set G) ≤ (K ⊔ S).pCoreIn 2 := by
  rw [d.core_eq_centralizer]
  exact inf_le_inf le_rfl (centralizer_le (map_subtype_le _))

/-- C.6.4(2), the product and directness assertions preceding the escape argument. -/
theorem Input.core_direct_split (d : Input K R S Λ) :
    (K ⊔ S).pCoreIn 2 =
        (R ⊓ centralizer (K : Set G)) ⊔ (blockU K).map K.subtype ∧
      Disjoint (R ⊓ centralizer (K : Set G)) ((blockU K).map K.subtype) ∧
      ⁅R ⊓ centralizer (K : Set G), (blockU K).map K.subtype⁆ = ⊥ := by
  have hD : (K ⊔ S).pCoreIn 2 ⊓ centralizer (K : Set G) =
      R ⊓ centralizer (K : Set G) :=
    le_antisymm (inf_le_inf d.core_le le_rfl)
      (le_inf d.block_centralizer_le_core inf_le_right)
  refine ⟨?_, ?_, commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le (map_subtype_le _)))⟩
  · rw [d.block.seven_normalizer_twoCore_eq_module_sup_centralizer
      (show K ≤ K ⊔ S from le_sup_left) d.normalizes_block, hD, sup_comm]
  · apply disjoint_def.mpr
    intro u hu hU
    obtain ⟨v,hv,rfl⟩ := hU
    have hc : v ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (hu.2 k k.property)
    have hf : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := hc
    rw [d.block.seven_fixed_eq_bot, mem_bot] at hf
    exact congrArg (fun z : blockU K => ((z : K) : G)) hf

omit [Finite G] in
/-- Normality is relative to R. -/
theorem Input.core_normal_in_R (d : Input K R S Λ) :
    (((K ⊔ S).pCoreIn 2).subgroupOf R).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((d.R_le_S.trans le_sup_right).trans d.normalizes_core)

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
