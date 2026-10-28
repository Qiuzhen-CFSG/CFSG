module
public import Theory.GroupTheory.CentralProductProjection
public import Stellmacher.ElementaryAbelianMaxFamilyMap
/-! # The faithful crossing core inside the component Sylow quotient
The Thompson product and conjugation-invariance place the crossing core in
that product. Projection along the centralizer kills precisely the original
core, so disjointness gives a faithful map. Its image remains in the literal
component Sylow image in the center quotient, with no abstract carrier swap.
Source: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G:Type*} [Group G]
theorem crossing_thompson_core_embedding (S K:Subgroup G)
    (hJ:elementaryAbelianMaxJ S=(S⊓K)⊔
      (elementaryAbelianMaxJ S⊓centralizer (K:Set G)))
    (x:G) (hx:x∈normalizer (S:Set G))
    (hd:Disjoint (S⊓centralizer (K:Set G)) ((S⊓centralizer (K:Set G)).conjBy x)) :
    ∃j:((elementaryAbelianMaxJ S⊓centralizer (K:Set G)).conjBy x)→*(K⧸center K),
      Function.Injective j ∧
      j.range≤(S.subgroupOf K).map (QuotientGroup.mk' (center K)) := by
  let R:=elementaryAbelianMaxJ S
  let SK:=S⊓K
  let C:=R⊓centralizer (K:Set G)
  have hJR:R=SK⊔C:=hJ
  have hRS:R≤S:=sSup_le fun _ hA=>hA.1
  have hKR:SK≤R:=hJR.symm ▸ (show SK≤SK⊔C from le_sup_left)
  have hC:R⊓centralizer (K:Set G)≤S⊓centralizer (K:Set G):=
    inf_le_inf_right _ hRS
  have hCS:C≤S:=inf_le_left.trans hRS
  have hc:SK≤centralizer (C:Set G):=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (show SK≤K from inf_le_right)))
  let q:SK→*(K⧸center K):=(QuotientGroup.mk' (center K)).comp (inclusion inf_le_right)
  have hk:q.ker=C.subgroupOf SK:=by
    ext k
    change QuotientGroup.mk' (center K) (inclusion inf_le_right k)=1 ↔ (k:G)∈C
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    constructor
    · intro hk
      refine ⟨hKR k.property,?_⟩
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp hk ⟨a,ha⟩)
    · intro hk
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hk.2 a a.property)
  have hxR:R.conjBy x=R:=by
    change R.map (MulAut.conj x).toMonoidHom=R
    have hxs:S.map (MulAut.conj x).toMonoidHom=S:=mem_normalizer_iff_map_conj_eq.mp hx
    rw [←elementaryAbelianMaxJ_map_injective _ (MulAut.conj x).injective,hxs]
  have hDR:C.conjBy x≤R:=hxR ▸ map_mono (show C≤R from inf_le_left)
  have hDC:Disjoint (C.conjBy x) C:=
    (hd.mono hC (map_mono hC)).symm
  obtain ⟨π,hπ,hker⟩:=Subgroup.exists_sup_projection SK C hc q hk
  let j:=π.comp (inclusion (hJR ▸ hDR))
  have hj:Function.Injective j:=by
    rw [←MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro d hd'
    have he:inclusion (hJR ▸ hDR) d∈π.ker:=hd'
    rw [hker] at he
    exact Subtype.ext (disjoint_def.mp hDC d.property he)
  refine ⟨j,hj,?_⟩
  rintro _ ⟨d,rfl⟩
  have hdKC:(d:G)∈(SK:Set G)*(C:Set G):=by
    rw [←coe_mul_of_left_le_normalizer_right SK C (hc.trans (Subgroup.centralizer_le_normalizer _))]
    exact (hJR ▸ hDR) d.property
  obtain ⟨k,hk,c,hc',hkc⟩:=hdKC
  have hkc':inclusion (hJR ▸ hDR) d=
      (inclusion le_sup_left (⟨k,hk⟩:SK))*(inclusion le_sup_right (⟨c,hc'⟩:C)):=
    Subtype.ext hkc.symm
  have hcπ:π (inclusion le_sup_right (⟨c,hc'⟩:C))=1:=by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact hc'
  change π (inclusion (hJR ▸ hDR) d)∈_
  rw [hkc',map_mul,hπ,hcπ,mul_one]
  exact ⟨⟨k,hk.2⟩,hk.1,rfl⟩
end Stellmacher
