module

public import Stellmacher.SectionThree.PrimitiveDihedralExtraction
public import Stellmacher.SectionThree.GeneratedDihedralImage

/-!
# The image of the extracted generated subgroup

The primitive extraction package supplies an odd cyclic rotation, an
inverting involution in the quotient, and a centralizing actor coatom.
Here the elementary actor image and its factorization are transported
through the quotient map. The two conjugate actor images generate exactly
the rotation and actor, so the dihedral-product lemma applies. Residual
functoriality also shows that the rotation image coming from `O²(L)` is
normal in the image of `L`; this is shared by the orbit and core arguments.
The shared Frattini-image lemma derives the elementary actor hypothesis
from the original local assumptions for both the Section 3 and 7 assemblies.

This is Stellmacher (3.6)(a), Journal of Algebra 190 (1997), p. 22, with
the barred subgroup interpreted as its image in `P/O₂(P)`. The central
actor factor is preserved. Residual and orbit-action clauses are assembled
in the parent module.
-/

open scoped Pointwise

namespace Stellmacher.SectionThree

/-- The actor's Frattini containment makes its image modulo the local 2-core elementary abelian. -/
public theorem elementary_actor_image
    {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) (hAP : A ≤ P) (hA2 : IsPGroup 2 A)
    (hPhiA : frattiniAmbient A ≤ twoCoreAmbient P) :
    IsElementaryAbelian 2
      ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := pCore 2 P
  let qO := QuotientGroup.mk' O
  let fA : A →* P ⧸ O := qO.comp (Subgroup.inclusion hAP)
  have hPhiKerA : frattini A ≤ fA.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' O (Subgroup.inclusion hAP x) = 1
    apply (QuotientGroup.eq_one_iff (N := O) (Subgroup.inclusion hAP x)).2
    have hxamb : (x : G) ∈ frattiniAmbient A :=
      Subgroup.mem_map_of_mem A.subtype hx
    rcases hPhiA hxamb with ⟨y, hy, hyx⟩
    have hxy : (⟨(x : G), hAP x.property⟩ : P) = y := Subtype.ext hyx.symm
    simpa [Subgroup.inclusion, hxy] using hy
  have hrange := elementaryAbelian_range_of_frattini_le_ker fA hA2 hPhiKerA
  have hEq : (A.subgroupOf P).map qO = fA.range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨(x : G), hx⟩ : A), rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(⟨(x : G), hAP x.property⟩ : P), x.property, rfl⟩
  rw [hEq]
  exact hrange

private theorem extracted_actor_image_factor
    {G : Type*} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P) (a : G) (haA : a ∈ A)
    (d : PrimitiveDihedralExtractionData P T A hAP a haA) :
    let q := QuotientGroup.mk' (pCore 2 P)
    ((A.subgroupOf P).map q : Set (P ⧸ pCore 2 P)) =
      (Subgroup.zpowers (q ⟨a, hAP haA⟩) : Set (P ⧸ pCore 2 P)) *
      ((d.A₀.subgroupOf P).map q : Set (P ⧸ pCore 2 P)) := by
  let q := QuotientGroup.mk' (pCore 2 P)
  let aP : P := ⟨a, hAP haA⟩
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hbprod : (b : G) ∈ (Subgroup.zpowers a : Set G) * (d.A₀ : Set G) :=
      d.A_factor ▸ hb
    obtain ⟨u, hu, c, hc, huc⟩ := hbprod
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    let cP : P := ⟨c, hAP (d.A₀_le hc)⟩
    refine ⟨q (aP ^ k), ?_, q cP, ?_, ?_⟩
    · exact Subgroup.mem_zpowers_iff.mpr ⟨k, (map_zpow q aP k).symm⟩
    · exact Subgroup.mem_map_of_mem q hc
    · change q (aP ^ k) * q cP = q b
      rw [← map_mul]
      apply congrArg q
      exact Subtype.ext huc
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨c, hc, rfl⟩ := hv
    change q aP ^ k * q c ∈ (A.subgroupOf P).map q
    rw [← map_zpow, ← map_mul]
    apply Subgroup.mem_map_of_mem q
    exact (A.subgroupOf P).mul_mem
      ((A.subgroupOf P).zpow_mem (show aP ∈ A.subgroupOf P from haA) k)
      (d.A₀_le hc)

public theorem extracted_generated_quotient_image
    {G : Type*} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P) (a : G) (haA : a ∈ A)
    (d : PrimitiveDihedralExtractionData P T A hAP a haA)
    (hAelem : IsElementaryAbelian 2
      ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))) :
    let q := QuotientGroup.mk' (pCore 2 P)
    ((A.subgroupOf P) ⊔ (A.subgroupOf P).conjBy d.x).map q =
      (d.F₀.subgroupOf P).map q ⊔ (A.subgroupOf P).map q := by
  let q := QuotientGroup.mk' (pCore 2 P)
  let Ab := (A.subgroupOf P).map q
  let ab := q ⟨a, hAP haA⟩
  have hab : ab ∈ Ab := Subgroup.mem_map_of_mem q haA
  have hpR : IsPGroup d.p (Subgroup.zpowers (q d.x)) := by
    rw [← d.rotation_eq]
    exact IsPGroup.of_card d.rotation_card
  let _ : Fact d.p.Prime := ⟨d.prime_p⟩
  dsimp only
  rw [Subgroup.map_sup, map_conjBy]
  rw [sup_conjBy_eq_zpowers_sup_of_reflection Ab (q d.x) ab d.odd_p hpR hAelem hab]
  · rw [← d.rotation_eq]
  · exact d.reflected (q d.x) (by rw [d.rotation_eq]; exact Subgroup.mem_zpowers _)

public theorem extracted_generated_image_product
    {G : Type*} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P) (a : G) (haA : a ∈ A)
    (d : PrimitiveDihedralExtractionData P T A hAP a haA)
    (hAelem : IsElementaryAbelian 2
      ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))) :
    let q := QuotientGroup.mk' (pCore 2 P)
    let AP := A.subgroupOf P
    let L := (AP ⊔ AP.conjBy d.x).map P.subtype
    ∃ E : Subgroup (P ⧸ pCore 2 P),
      Nonempty (E ≃* DihedralGroup (d.p ^ d.n)) ∧
        IsInternalDirectProductFamily ((L.subgroupOf P).map q)
          (fun i : Bool => if i then E else (d.A₀.subgroupOf P).map q) := by
  classical
  let q := QuotientGroup.mk' (pCore 2 P)
  let R := (d.F₀.subgroupOf P).map q
  let Ab := (A.subgroupOf P).map q
  let C := (d.A₀.subgroupOf P).map q
  let ab := q ⟨a, hAP haA⟩
  let AP := A.subgroupOf P
  let LP := AP ⊔ AP.conjBy d.x
  let L := LP.map P.subtype
  have hRcard : Nat.card R = d.p ^ d.n := d.rotation_card
  have hRcyclic : IsCyclic R := by rw [show R = Subgroup.zpowers (q d.x) from d.rotation_eq]; infer_instance
  have hRodd : Odd (Nat.card R) := by rw [hRcard]; exact d.odd_p.pow
  have hRne : Nat.card R ≠ 1 := by
    rw [hRcard]
    exact ne_of_gt (Nat.one_lt_pow (Nat.ne_of_gt d.n_pos) d.prime_p.one_lt)
  have hCAb : C ≤ Ab := Subgroup.map_mono (Subgroup.subgroupOf_mono P d.A₀_le)
  have hab : ab ∈ Ab := Subgroup.mem_map_of_mem q haA
  have hcentral : ∀ c : P ⧸ pCore 2 P, c ∈ C →
      ∀ r : P ⧸ pCore 2 P, r ∈ R → c * r = r * c := by
    rintro c ⟨b, hb, rfl⟩ r hr
    exact d.A₀_centralizes_rotation b hb r hr
  have hprod := elementary_actor_dihedral_product R Ab C hRcyclic hRodd hRne
    hAelem hCAb ab hab d.reflection_involution
    (extracted_actor_image_factor P T A hAP a haA d) d.reflected hcentral
  have himage : (L.subgroupOf P).map q = R ⊔ Ab := by
    have hsub : L.subgroupOf P = LP := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le LP)]
    rw [hsub]
    exact extracted_generated_quotient_image P T A hAP a haA d hAelem
  refine ⟨R ⊔ Subgroup.zpowers ab, ?_, ?_⟩
  · rw [← hRcard]
    exact hprod.1
  · rw [himage]
    exact hprod.2

public theorem residual_image_normal
    {G : Type*} [Group G] [Finite G]
    (P L : Subgroup G) (hLP : L ≤ P) :
    let q := QuotientGroup.mk' (pCore 2 P)
    let J := (L.subgroupOf P).map q
    let R := ((twoResidualAmbient L).subgroupOf P).map q
    R ≤ J ∧ (R.subgroupOf J).Normal := by
  let q := QuotientGroup.mk' (pCore 2 P)
  let LP := L.subgroupOf P
  let J := LP.map q
  have hresLe : twoResidualAmbient L ≤ L := Subgroup.map_subtype_le _
  have hsub : (twoResidualAmbient L).subgroupOf P = twoResidualAmbient LP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (hresLe.trans hLP)]
    symm
    exact map_twoResidualAmbient_of_subgroup_image LP P.subtype L
      (Subgroup.map_subgroupOf_eq_of_le hLP)
  have hR : ((twoResidualAmbient L).subgroupOf P).map q = twoResidualAmbient J := by
    rw [hsub]
    exact map_twoResidualAmbient_of_subgroup_image LP q J rfl
  dsimp only
  rw [hR]
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  unfold twoResidualAmbient
  rw [subgroupOf_map_subtype_eq]
  rw [twoResidualSubgroup_eq_hktPResidual']
  exact BenderSuzuki.External.hktPResidual_normal

end Stellmacher.SectionThree
