module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedSource
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer

/-!
# Literal core and normalization facts for the reduced marking

In a normal short-block extension KT, the module centralizer is the full
two-core: the quotient by K is a two-group, and the intrinsic module
centralizer in K is O₂(K). The reverse inclusion is the short-block
core-action theorem. Since T normalizes both K and Baum(T), the latter
block extension is normal in KT. Its core is the actual intersection
with O₂(KT), and lies in the specified Sylow T.

Source: Aschbacher–Smith C.1.11 and C.5.4, pp.124 and155.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem normal_short_extension_centralizer (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) :
    (K ⊔ T) ⊓ centralizer (U K : Set G) = (K ⊔ T).pCoreIn 2 := by
  let A := K ⊔ T
  let C := A ⊓ centralizer (U K : Set G)
  have hAK : A ≤ normalizer (K : Set G) := sup_le K.le_normalizer hn
  have hAQ : A ≤ normalizer (A.pCoreIn 2 : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hAU : A ≤ normalizer (U K : Set G) :=
    hAK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hQC : A.pCoreIn 2 ≤ centralizer (U K : Set G) :=
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
  have hLC : K ⊓ centralizer (U K : Set G) ≤ K.pCoreIn 2 := by
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
    have hcO := hLC ⟨hcK,(centralizer (U K : Set G)).pow_mem c.property.2 _⟩
    obtain ⟨m,hm⟩ := isPGroup_pCoreIn 2 K ⟨_,hcO⟩
    refine ⟨n+m,Subtype.ext ?_⟩
    change (c : G) ^ 2 ^ (n+m) = 1
    rw [pow_add,pow_mul]
    exact congrArg Subtype.val hm
  exact le_pCoreIn_of_normalizes hCp inf_le_left
    ((le_inf A.le_normalizer (hAU.trans (normalizer_le_normalizer_centralizer (U K)))).trans
      inf_normalizer_le_normalizer_inf)

theorem reduced_baumann_core (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (hSylow : ∃ P : Sylow 2 (K ⊔ T : Subgroup G),
      (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T) :
    let B := K ⊔ S T
    S T ≤ normalizer (K : Set G) ∧ U K ≤ B.pCoreIn 2 ∧ B.pCoreIn 2 ≤ T ∧
      B.pCoreIn 2 = B ⊓ (K ⊔ T).pCoreIn 2 ∧
      B.pCoreIn 2 = B ⊓ centralizer (U K : Set G) ∧
      T ⊓ centralizer (U K : Set G) = (K ⊔ T).pCoreIn 2 := by
  let A := K ⊔ T
  let B := K ⊔ S T
  have hBA : B ≤ A := sup_le_sup_left (show S T ≤ T from inf_le_left) K
  have hAB : A ≤ normalizer (B : Set G) := by
    apply sup_le (le_sup_left.trans B.le_normalizer)
    exact (le_inf hn (T.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann T))).trans
      (K.normalizer_inf_normalizer_le_normalizer_sup (S T))
  have hQB : B.pCoreIn 2 ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B) ((pCoreIn_le 2 B).trans hBA)
      (hAB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hQAT : A.pCoreIn 2 ≤ T := by
    obtain ⟨P,hP⟩ := hSylow
    exact hP ▸ pCoreIn_le_sylow A P
  have hQeq : B.pCoreIn 2 = B ⊓ A.pCoreIn 2 := by
    refine le_antisymm (le_inf (pCoreIn_le 2 B) hQB) ?_
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 A).to_le inf_le_right) inf_le_left
    exact (le_inf B.le_normalizer (hBA.trans (A.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A))))).trans inf_normalizer_le_normalizer_inf
  have hBS := normal_short_extension_centralizer K (S T) hK (hT.to_le inf_le_left) (inf_le_left.trans hn)
  have hAS := normal_short_extension_centralizer K T hK hT hn
  have hUQ : U K ≤ B.pCoreIn 2 := by
    let : IsElementaryAbelian 2 (U K) := hK.elementary.map K.subtype
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (U K))
      ((map_subtype_le _).trans le_sup_left)
      ((sup_le K.le_normalizer (inf_le_left.trans hn)).trans
        (normalizer_le_normalizer_characteristic_image K (blockU K)))
  refine ⟨inf_le_left.trans hn,hUQ,hQB.trans hQAT,hQeq,hBS.symm,?_⟩
  exact le_antisymm ((inf_le_inf le_sup_right le_rfl).trans hAS.le)
    (le_inf hQAT (hAS.ge.trans inf_le_right))
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
