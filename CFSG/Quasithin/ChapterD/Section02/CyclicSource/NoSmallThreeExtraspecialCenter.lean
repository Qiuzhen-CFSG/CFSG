module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeSource
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
/-!
# The characteristic cubic center in the extraspecial branch

Let F = [O₃(G),t] be extraspecial and suppose C_{O₃(G)}(t) is cyclic.
Coprime decomposition makes O₃(G)/F cyclic. The center of F is then
the intrinsic subgroup O₃(G)′ ∩ Z(O₃(G)), so it is normal in G.
The finaltheorem supplies cyclicity from the original SQTK cover.
Source: Aschbacher–Smith, proof after D.2.29, printed p.192.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterD.CyclicSource

theorem normal_extraspecial_derived_center
    {P : Type*} [Group P] [Finite P] (hp : IsPGroup 3 P)
    (D : Subgroup P) [D.Normal] [IsExtraspecial 3 D]
    [IsMulCommutative (P ⧸ D)] :
    _root_.commutator P ⊓ center P = (center D).map D.subtype := by
  have hder : _root_.commutator P ≤ D :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hZnorm : ((center D).map D.subtype).Normal := by
    rw [← normalizer_eq_top_iff]
    apply top_unique
    simpa only [D.normalizer_eq_top] using
      normalizer_le_normalizer_characteristic_image D (center D)
  let := hZnorm
  have hZcenter : (center D).map D.subtype ≤ center P :=
    hp.normal_le_center_of_card_dvd_prime _ (by
      rw [card_map_of_injective D.subtype_injective, IsExtraspecial.center_order_p 3 D])
  apply le_antisymm
  · intro x hx
    refine ⟨⟨x,hder hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
    intro d
    exact Subtype.ext (mem_center_iff.mp hx.2 d)
  · apply le_inf _ hZcenter
    rw [← IsExtraspecial.commutator_eq_center (p := 3), map_subtype_commutator]
    exact commutator_mono le_top le_top

theorem cyclic_supplement_quotient
    {P : Type*} [Group P] (D C : Subgroup P) [D.Normal] [IsCyclic C]
    (hgen : D ⊔ C = ⊤) : IsCyclic (P ⧸ D) := by
  let q := QuotientGroup.mk' D
  let f := q.comp C.subtype
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective D x
  obtain ⟨d,hd,c,hc,he⟩ := mem_sup_of_normal_left.mp
    (show g ∈ D ⊔ C by rw [hgen]; trivial)
  refine ⟨⟨c,hc⟩,?_⟩
  change q c = q g
  rw [←he,map_mul,show q d = 1 from (QuotientGroup.eq_one_iff _).mpr hd,one_mul]

theorem extraspecial_commutator_center_normal
    {G : Type*} [Group G] [Finite G] (R : Subgroup G) [R.Normal]
    (hp : IsPGroup 3 R) (t : G) (ht : orderOf t = 2)
    (hC : IsCyclic (R ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hF : IsExtraspecial 3 (⁅R,zpowers t⁆ : Subgroup G)) :
    ((center (⁅R,zpowers t⁆ : Subgroup G)).map (⁅R,zpowers t⁆ : Subgroup G).subtype).Normal := by
  let F := ⁅R,zpowers t⁆
  let D := F.subgroupOf R
  let C := R ⊓ centralizer ({t} : Set G)
  have hFR : F ≤ R := commutator_le_left R (zpowers t)
  let : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left R (zpowers t))
  let : IsExtraspecial 3 D := IsExtraspecial.of_mulEquiv
    (subgroupOfEquivOfLe hFR).symm hF
  let : IsCyclic C := hC
  let : IsCyclic (C.subgroupOf R) := isCyclic_of_injective
    (subgroupOfEquivOfLe (show C ≤ R from inf_le_left)).toMonoidHom
    (subgroupOfEquivOfLe (show C ≤ R from inf_le_left)).injective
  have hcop : Nat.Coprime (Nat.card (zpowers t)) (Nat.card R) := by
    rw [Nat.card_zpowers,ht]
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  let : Group.IsNilpotent R := hp.isNilpotent
  have hct : centralizer (zpowers t : Set G) = centralizer ({t} : Set G) := by
    ext x
    constructor
    · intro hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx t (mem_zpowers t)).symm
    · intro hx
      rw [mem_centralizer_iff]
      rintro y ⟨n,rfl⟩
      exact ((show Commute x t from mem_centralizer_singleton_iff.mp hx).zpow_right n).eq.symm
  have hgen : R = F ⊔ C := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime R (zpowers t)
      (le_normalizer_of_normal (H := R)) inferInstance hcop
    simpa only [hct] using hh
  have hgenR : D ⊔ C.subgroupOf R = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hFR,
      map_subgroupOf_eq_of_le (show C ≤ R from inf_le_left),←MonoidHom.range_eq_map,R.range_subtype]
    exact hgen.symm
  let : IsCyclic (R ⧸ D) := cyclic_supplement_quotient D (C.subgroupOf R) hgenR
  have hderived := normal_extraspecial_derived_center hp D
  have hcentermap : ((center D).map D.subtype).map R.subtype = (center F).map F.subtype := by
    ext z
    constructor
    · rintro ⟨r,⟨d,hd,rfl⟩,rfl⟩
      refine ⟨⟨d.val.val,d.property⟩,mem_center_iff.mpr ?_,rfl⟩
      intro y
      exact Subtype.ext (congrArg (fun x : D => x.val.val)
        (mem_center_iff.mp hd ((subgroupOfEquivOfLe hFR).symm y)))
    · rintro ⟨f,hf,rfl⟩
      let d : D := (subgroupOfEquivOfLe hFR).symm f
      refine ⟨d.val,⟨d,mem_center_iff.mpr ?_,rfl⟩,rfl⟩
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : F => x.val) (mem_center_iff.mp hf ((subgroupOfEquivOfLe hFR) y))
  change ((center F).map F.subtype).Normal
  rw [←hcentermap,←hderived,←normalizer_eq_top_iff]
  apply top_unique
  simpa only [R.normalizer_eq_top] using
    normalizer_le_normalizer_characteristic_image R (_root_.commutator R ⊓ center R)
/-- The original SQTK cover makes the extraspecial commutator center normal
in the original ambient group. -/
theorem CoreHypotheses.extraspecial_center_normal
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (h : CoreHypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (t : G) (ht : orderOf t = 2)
    (hF : IsExtraspecial 3 (⁅pCore 3 G,zpowers t⁆ : Subgroup G)) :
    ((center (⁅pCore 3 G,zpowers t⁆ : Subgroup G)).map
      (⁅pCore 3 G,zpowers t⁆ : Subgroup G).subtype).Normal :=
  extraspecial_commutator_center_normal (pCore 3 G) pCore_isPGroup t ht
    (h.involution_threeCore_centralizer_cyclic hH f honto hfive t ht) hF

end CFSG.Quasithin.ChapterD.CyclicSource
