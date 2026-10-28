module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleMovedCard
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointInterval

/-!
# The original tensor moved section through a containing center

The literal diagonal moved subgroup has the nonsingular point hyperplane
as its coordinate image. The additive matrix interval proves that it is
irreducible modulo its fixed field line. Pulling an invariant subgroup of
the containing central quotient back to the original moved subgroup preserves
that interval, even when the quotient creates additional fixed vectors.

The final consumer is the Janko4 local exclusion in original9.4.1. These
statements concern the original residual and the actual quotient by the
containing subgroup's center, without an independent irreducibility premise.
Source: Aschbacher--Smith9.1.2(4),9.4.1, printed pp.729,735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix PointOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem interval_image_normalized (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (U : Subgroup G) (hUV : U ≤ D.fullModule)
    (hU : m.tensorPointResidual v ≤ normalizer (U : Set G)) :
    ∀ g : pointStabilizer (m.sectionData.coordinates v).toAdd,
      ∀ w ∈ m.sectionData.imageSpace U, matrixAction g.val w ∈ m.sectionData.imageSpace U := by
  intro g w hw
  obtain ⟨r,hr⟩ := m.tensorPointResidualQuotient_surjective v hv g
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  have he := m.sectionData.imageSpace_conjBy U hUV rO
  rw [show U.conjBy (rO : G) = U from
    mem_normalizer_iff_map_conj_eq.mp (hU r.property)] at he
  have hm : sourceA5TensorAction m.quotient rO w ∈ m.sectionData.imageSpace U := by
    rw [he]
    exact Submodule.mem_map.mpr ⟨w,hw,rfl⟩
  change matrixAction (m.quotient rO) w ∈ m.sectionData.imageSpace U at hm
  have hq : m.quotient rO = g.val := congrArg Subtype.val hr
  rwa [hq] at hm

/-- The actual moved hyperplane is irreducible modulo its fixed field line. -/
theorem tensorPoint_moved_irreducible_interval (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (N : Subgroup G)
    (hfix : ⁅D.fullModule,m.tensorPointResidual v⁆ ⊓
      centralizer (m.tensorPointResidual v : Set G) ≤ N)
    (hNW : N ≤ ⁅D.fullModule,m.tensorPointResidual v⁆)
    (hN : m.tensorPointResidual v ≤ normalizer (N : Set G)) :
    N = ⁅D.fullModule,m.tensorPointResidual v⁆ ⊓
      centralizer (m.tensorPointResidual v : Set G) ∨
      N = ⁅D.fullModule,m.tensorPointResidual v⁆ := by
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)
  have hlo : (Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V)).toAddSubgroup ≤
      (m.sectionData.imageSpace N).toAddSubgroup := by
    intro w hw
    obtain ⟨z,hz⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
    have hzcoord : (m.sectionData.coordinates z).toAdd = w := congrArg Multiplicative.toAdd hz
    have hzW : (z : G) ∈ W := by
      apply (m.tensorPoint_moved_coordinates_iff v hv z).mpr
      rw [hzcoord]
      exact pointLine_le_pointHyperplane _ hv hw
    have hzC : (z : G) ∈ centralizer (m.tensorPointResidual v : Set G) := by
      apply (m.tensorPointResidual_fixed_iff v z hv).mpr
      rwa [hzcoord]
    exact (m.sectionData.mem_imageSpace_iff N w).mpr ⟨z,hfix ⟨hzW,hzC⟩,hzcoord⟩
  have hhi : (m.sectionData.imageSpace N).toAddSubgroup ≤
      (pointHyperplane (m.sectionData.coordinates v).toAdd).toAddSubgroup := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := (m.sectionData.mem_imageSpace_iff N w).mp hw
    exact (m.tensorPoint_moved_coordinates_iff v hv z).mp (hNW hz)
  rcases pointHyperplane_interval (m.sectionData.coordinates v).toAdd hv
    (m.sectionData.imageSpace N).toAddSubgroup (m.interval_image_normalized v hv N (hNW.trans hWV) hN)
    hlo hhi with hline | hplane
  · left
    apply le_antisymm ?_ hfix
    refine le_inf hNW ?_
    intro z hz
    let zV : D.fullModule := ⟨z,hWV (hNW hz)⟩
    apply (m.tensorPointResidual_fixed_iff v zV hv).mpr
    have hm := (m.sectionData.mem_imageSpace_iff N (m.sectionData.coordinates zV).toAdd).mpr
      ⟨zV,hz,rfl⟩
    change (m.sectionData.coordinates zV).toAdd ∈
      (Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V)).toAddSubgroup
    rw [←hline]
    exact hm
  · right
    apply le_antisymm hNW
    intro z hz
    let zV : D.fullModule := ⟨z,hWV hz⟩
    have hp := (m.tensorPoint_moved_coordinates_iff v hv zV).mp hz
    have hn : (m.sectionData.coordinates zV).toAdd ∈ m.sectionData.imageSpace N := by
      change (m.sectionData.coordinates zV).toAdd ∈ (m.sectionData.imageSpace N).toAddSubgroup
      rw [hplane]
      exact hp
    obtain ⟨w,hw,he⟩ := (m.sectionData.mem_imageSpace_iff N _).mp hn
    have hwz : w = zV := m.coordinates_injective (Multiplicative.toAdd.injective he)
    have hwz' : (w : G) = z := congrArg (fun a : D.fullModule => (a : G)) hwz
    exact hwz' ▸ hw

/-- Central quotienting preserves the invariant interval of the original
moved subgroup, even if the quotient introduces additional fixed vectors. -/
theorem tensorPoint_containing_moved_irreducible_interval (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    let q := QuotientGroup.mk' (center I)
    let E := ((⁅D.fullModule,m.tensorPointResidual v⁆).subgroupOf I).map q
    let B := ((m.tensorPointResidual v).subgroupOf I).map q
    ∀ K : Subgroup (I ⧸ center I), E ⊓ centralizer (B : Set _) ≤ K → K ≤ E →
      B ≤ normalizer (K : Set _) → K = E ⊓ centralizer (B : Set _) ∨ K = E := by
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  let q := QuotientGroup.mk' (center I)
  let E := (W.subgroupOf I).map q
  let B := ((m.tensorPointResidual v).subgroupOf I).map q
  have hWL : W ≤ m.tensorPointResidual v := le_normalizer_iff_commutator_le_right.mp
    (m.tensorPointResidual_fullModule_normalized v)
  have hWI : W ≤ I := hWL.trans hLI
  change ∀ K : Subgroup (I ⧸ center I), E ⊓ centralizer (B : Set _) ≤ K → K ≤ E →
    B ≤ normalizer (K : Set _) → K = E ⊓ centralizer (B : Set _) ∨ K = E
  intro K hz hw hn
  let J := (W.subgroupOf I ⊓ K.comap q).map I.subtype
  have hJW : J ≤ W :=
    (map_mono inf_le_left).trans (map_subgroupOf_eq_of_le hWI).le
  have hCJ : W ⊓ centralizer (m.tensorPointResidual v : Set G) ≤ J := by
    intro c hc
    have hcI : c ∈ I := hWI hc.1
    refine mem_map.mpr ⟨⟨c,hcI⟩,⟨hc.1,?_⟩,rfl⟩
    apply hz
    refine ⟨mem_map.mpr ⟨⟨c,hcI⟩,hc.1,rfl⟩,?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact congrArg q (Subtype.ext (hc.2 l hl))
  have hLJ : m.tensorPointResidual v ≤ normalizer (J : Set G) := by
    have h1 : (m.tensorPointResidual v).subgroupOf I ≤ normalizer (W.subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq hWI]
      exact comap_mono (normalizer_commutator_ge_right _ _)
    have h2 : (m.tensorPointResidual v).subgroupOf I ≤ normalizer (K.comap q : Set I) :=
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
  rcases m.tensorPoint_moved_irreducible_interval v hv J hCJ hJW hLJ with hc | he
  · left
    apply le_antisymm ?_ hz
    refine le_inf hw ?_
    rw [←hJK,hc]
    rintro _ ⟨c,hc,rfl⟩ _ ⟨l,hl,rfl⟩
    exact congrArg q (Subtype.ext (hc.2 l hl))
  · right
    simpa only [he] using hJK.symm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
