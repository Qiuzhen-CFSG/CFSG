module
public import Stellmacher.SectionTen.TenOneSmallCentralizerOddCore
public import Stellmacher.SectionTen.TenOneSmallCentralizerNormalizer
public import Stellmacher.SectionTen.TenOneSmallLocalCentralizerCore
public import Theory.GroupTheory.AbelianNormalizerCore
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Solvable small-case involution centralizers lie in the middle stabilizer

Let a be an actual Wstar point outside the middle center in the small
first-module case. If its full ambient centralizer C_H(embedding a) is
solvable, then it lies in the image of the middle stabilizer. Solvability
is required only for this chosen full ambient centralizer.

The proved odd-core elimination and the solvable Fitting-centralizer
theorem give characteristic two for C. The mapped Wstar is elementary and
lies in C. Source (9) identifies its full ambient normalizer with the
middle stabilizer. Transporting the exact local point-centralizer core
through the embedding then identifies the two-core of its normalizer
inside C. The abelian normalizer-core theorem forces Wstar, on the C
carrier, to equal O2(C). Thus Wstar is C-normal, and source (9) puts C in
the middle stabilizer. A private injective-map lemma records the two-core
transport, while the centralizer intersection is identified pointwise.

Source: Stellmacher (10.1)(a3), printed p.62, assertion (10). This is its
pointwise consequence under solvability, used by the subsequent fusion
and path contradiction. Every centralizer and map retains the original
ambient H and the supplied graph embedding.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

private theorem map_core_of_injective
    {G K : Type*} [Group G] [Group K]
    (L : Subgroup G) (f : G →* K) (hf : Function.Injective f) :
    (twoCoreIn L).map f=twoCoreIn (L.map f) := by
  let e : L ≃* L.map f := L.equivMapOfInjective f hf
  have he : (L.map f).subtype.comp e.toMonoidHom=f.comp L.subtype := rfl
  unfold twoCoreIn
  rw [←pCore_map_iso 2 e,map_map,map_map,he]

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_solvable_centralizer_le_middle
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a : G) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    a ∈ Wstar → a ∉ ZAt ctx.Γ middle →
      Group.IsSolvable (Subgroup.centralizer ({embedding a} : Set H)) →
        Subgroup.centralizer ({embedding a} : Set H) ≤ (GAt ctx.Γ middle).map embedding := by
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  let M := (GAt ctx.Γ middle).map embedding
  let W := Wstar.map embedding
  let C := centralizer ({embedding a} : Set H)
  change a ∈ Wstar → a ∉ ZAt ctx.Γ middle → Group.IsSolvable C → C≤M
  intro haW haZ hsolv
  have hodd : pPrimeCore 2 C=⊥ := ten_one_small_centralizer_odd_core
    ctx middle hpath hsmall hmodel a haW haZ
  have hfit : fittingSubgroup C=pCore 2 C := Fitting_eq_pcore C 2 hodd
  have hchar : centralizer (pCore 2 C:Set C)≤pCore 2 C := by
    rw [←hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  have hnormalizer : normalizer (W:Set H)=M :=
    ten_one_small_centralizer_normalizer ctx middle hpath hsmall hmodel
  let _ : IsElementaryAbelian 2 Wstar :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.1
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map embedding
  have hWC : W≤C := by
    rintro _ ⟨w,hw,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg embedding (setLike_mul_comm hw haW)
  let WC := W.subgroupOf C
  let _ : IsElementaryAbelian 2 WC := IsElementaryAbelian.subgroupOf hWC
  let N := normalizer (WC:Set C)
  have hNmap : N.map C.subtype=M⊓C := by
    rw [show N=(normalizer (W:Set H)).subgroupOf C from
      (subgroupOf_normalizer_eq hWC).symm,subgroupOf_map_subtype,hnormalizer]
  let L := GAt ctx.Γ middle ⊓ centralizer ({a}:Set G)
  have hLmap : L.map embedding=M⊓C := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      refine ⟨mem_map_of_mem embedding hg.1,?_⟩
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using congrArg embedding (mem_centralizer_singleton_iff.mp hg.2)
    · rintro h ⟨⟨g,hg,hgh⟩,hh⟩
      refine ⟨g,⟨hg,?_⟩,hgh⟩
      apply mem_centralizer_singleton_iff.mpr
      apply ctx.embedding_injective
      simpa only [map_mul,hgh] using mem_centralizer_singleton_iff.mp hh
  have hcoreH : twoCoreIn (M⊓C)=W := by
    rw [←hLmap,←map_core_of_injective L embedding ctx.embedding_injective]
    rw [show twoCoreIn L=Wstar from ten_one_small_local_centralizer_core
      ctx middle hpath hsmall hmodel a haW haZ]
  have hNcore : (pCore 2 N).map N.subtype≤WC := by
    apply (map_le_map_iff_of_injective (f:=C.subtype) C.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWC]
    change (twoCoreIn N).map C.subtype≤W
    rw [map_core_of_injective N C.subtype C.subtype_injective,hNmap,hcoreH]
  have hWCcore : WC=pCore 2 C := eq_pCore_of_abelian_normalizer_core_le WC
    (IsElementaryAbelian.isPGroup 2 WC) hchar hNcore
  let _ : WC.Normal := hWCcore.symm ▸ inferInstance
  have hCN : C≤normalizer (W:Set H) := le_normalizer_of_normal_subgroupOf hWC
  exact hCN.trans_eq hnormalizer

end Stellmacher.SectionTen