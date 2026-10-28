module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# The chosen moved section in the literal central quotient

Pullback through I/Z(I) preserves the invariant interval of an irreducible
reduced section. The original component core still centralizes the moved
image: its central kernel lies in O₂(L), so the actual two-core quotient is
unchanged. These statements retain C_[V,L](L) and allow nonsplit extensions.

Source: Aschbacher--Smith 10.2.9, printed p.750. The J₄ natural-section
comparison applies both statements to the original component embedding.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
theorem marked_moved_irreducible_interval
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} [ρ.IsIrreducible]
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    {I : Subgroup G} (hLI : L ≤ I) {H : Type*} [Group H] [Finite H]
    (eI : (I ⧸ center I) ≃* H) :
    let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let B := (L.subgroupOf I).map q
    ∀ K : Subgroup H, E ⊓ centralizer (B : Set _) ≤ K → K ≤ E →
      B ≤ normalizer (K : Set _) → K = E ⊓ centralizer (B : Set _) ∨ K = E := by
  let W := ⁅D.fullModule,L⁆
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let E := (W.subgroupOf I).map q
  let B := (L.subgroupOf I).map q
  have hWI : W ≤ I := (source_full_moved_le_component D).trans hLI
  change ∀ K : Subgroup H, E ⊓ centralizer (B : Set _) ≤ K → K ≤ E →
    B ≤ normalizer (K : Set _) → K = E ⊓ centralizer (B : Set _) ∨ K = E
  intro K hz hw hn
  let J := (W.subgroupOf I ⊓ K.comap q).map I.subtype
  have hJW : J ≤ W := by
    exact (map_mono inf_le_left).trans (map_subgroupOf_eq_of_le hWI).le
  have hCJ : (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ≤ J := by
    intro c hc
    have hcI : c ∈ I := hWI hc.1
    refine mem_map.mpr ⟨⟨c,hcI⟩,⟨hc.1,?_⟩,rfl⟩
    apply hz
    refine ⟨mem_map.mpr ⟨⟨c,hcI⟩,hc.1,rfl⟩,?_⟩
    rintro _ ⟨l,hl,rfl⟩
    simpa only [map_mul] using congrArg q
      (show l * (⟨c,hcI⟩ : I) = (⟨c,hcI⟩ : I) * l from Subtype.ext (hc.2 l hl))
  have hLJ : L ≤ normalizer (J : Set G) := by
    have h1 : L.subgroupOf I ≤ normalizer (W.subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq hWI]
      exact comap_mono (normalizer_commutator_ge_right _ _)
    have h2 : L.subgroupOf I ≤ normalizer (K.comap q : Set I) :=
      ((map_le_iff_le_comap.mp hn).trans (le_normalizer_comap q))
    have h3 := (le_inf h1 h2).trans inf_normalizer_le_normalizer_inf
    have h4 := (map_mono h3).trans (le_normalizer_map I.subtype)
    rwa [map_subgroupOf_eq_of_le hLI] at h4
  have hJK : (J.subgroupOf I).map q = K := by
    have hpre : J.subgroupOf I = W.subgroupOf I ⊓ K.comap q := by
      exact comap_map_eq_self_of_injective I.subtype_injective _
    rw [hpre]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro x hx
      obtain ⟨w,hwE,he⟩ := hw hx
      exact mem_map.mpr ⟨w,⟨hwE,show q w ∈ K from he.symm ▸ hx⟩,he⟩
  rcases d.eq_kernel_or_section J hCJ hJW hLJ with hc | he
  · left
    apply le_antisymm ?_ hz
    refine le_inf hw ?_
    rw [←hJK,hc]
    rintro _ ⟨c,hc,rfl⟩ _ ⟨l,hl,rfl⟩
    simpa only [map_mul] using congrArg q
      (show l * c = c * l from Subtype.ext (hc.2 l hl))
  · right
    simpa only [he] using hJK.symm

theorem marked_moved_core_centralizes
    {I : Subgroup G} (hLI : L ≤ I) {H : Type*} [Group H] [Finite H]
    (eI : (I ⧸ center I) ≃* H) :
    let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let B := (L.subgroupOf I).map q
    B.pCoreIn 2 ≤ centralizer (E : Set H) := by
  let W := ⁅D.fullModule,L⁆
  let A := L.subgroupOf I
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let B := A.map q
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f : L →* B := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change q (inclusion hLI l) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp
      (eI.injective (hh.trans (map_one eI).symm))
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  have hzc : center L ≤ pCore 2 L := center_le_twoCore D
  have hp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hk.trans hzc)
  have hcore : (pCore 2 L).map f = pCore 2 B := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hp,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  let N := (W.subgroupOf L).map f
  have hNc : pCore 2 B ≤ centralizer (N : Set B) := by
    intro b hb
    rw [←hcore] at hb
    obtain ⟨r,hr,rfl⟩ := hb
    rintro _ ⟨w,hw,rfl⟩
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    have hh : w*r=r*w := Subtype.ext
      (source_component_core_centralizes_fullModule D (mem_map_of_mem L.subtype hr)
        w (hWV hw))
    simpa only [map_mul] using congrArg f hh
  have hmap : N.map B.subtype = (W.subgroupOf I).map q := by
    rw [map_map]
    have hcomp : B.subtype.comp f = q.comp (inclusion hLI) := rfl
    rw [hcomp,←map_map]
    congr 1
    apply map_injective I.subtype_injective
    rw [map_map,subtype_comp_inclusion,
      map_subgroupOf_eq_of_le (source_full_moved_le_component D),
      map_subgroupOf_eq_of_le ((source_full_moved_le_component D).trans hLI)]
  change (pCore 2 B).map B.subtype ≤ centralizer ((W.subgroupOf I).map q : Set _)
  rw [←hmap]
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr hNc,Subgroup.map_bot]


end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
