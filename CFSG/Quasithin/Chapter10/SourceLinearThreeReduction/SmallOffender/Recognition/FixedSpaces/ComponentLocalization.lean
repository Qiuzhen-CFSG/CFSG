module
public import Theory.GroupTheory.PerfectSimpleImageOrder
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerResidual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Quotient

/-!
# The original component in a nonfixed point centralizer

Use the literal two-component quotient of L₀. A copy of L fixing a vector
fixed by L has either trivial or full image in the other simple factor.
Full image would make all of L₀ fix the vector. Trivial image puts the copy
inside L O₂(L₀), and perfectness removes the two-group supplement.

This supplies the component inclusion needed by 10.2.10 without the stronger
claim that every proper subgroup of L/O₂(L) is solvable. No natural module
marking is used. Source: Aschbacher--Smith 10.2.10, printed p.753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- An isomorphic original component in a nonfixed point centralizer lies in the fixed factor. -/
theorem isomorphic_component_point_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule)
    (hvL : v ∈ centralizer (L : Set G))
    (hvnot : v ∉ centralizer (localOrbit T L : Set G))
    (A : Subgroup G) (eA : A ≃* L)
    (hAR : A ≤ localOrbit T L) (hAC : A ≤ centralizer ({v} : Set G)) : A ≤ L := by
  let R := localOrbit T L
  let Q := L ⧸ pCore 2 L
  let E := L.subgroupOf R
  let B := A.subgroupOf R
  let C := (centralizer ({v} : Set G)).subgroupOf R
  have hLR : L ≤ R := le_componentOrbit L T
  let : E.Normal := normal_subgroupOf_of_le_normalizer (source_nonnormal_orbit_le_normalizer D hn)
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := eA.symm.toMonoidHom) eA.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAR).symm.toMonoidHom) (subgroupOfEquivOfLe hAR).symm.surjective
  let : IsSimpleGroup Q := quotient_simple D hn
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨q,hq,hker,hfirst,hsecond⟩ := source_nonnormal_original_product_quotient D hn ht htn
  let p : R →* Q := (MonoidHom.snd Q Q).comp q
  let f : B →* Q := p.comp B.subtype
  let eB : B ≃* L := (subgroupOfEquivOfLe hAR).trans eA
  let qB : B →* Q := (QuotientGroup.mk' (pCore 2 L)).comp eB.toMonoidHom
  have hqB : Function.Surjective qB := (QuotientGroup.mk'_surjective _).comp eB.surjective
  have hqker : IsPGroup 2 qB.ker := by
    rw [show qB = (QuotientGroup.mk' (pCore 2 L)).comp eB.toMonoidHom from rfl,
      ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective eB.toMonoidHom eB.injective
  let : Group.IsNilpotent qB.ker := hqker.isNilpotent
  have hEC : E ≤ C := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hBC : B ≤ C := fun a ha => hAC ha
  have hcoreC : pCore 2 R ≤ C := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      ((source_fullModule_orbit_core_centralizes D (mem_map_of_mem R.subtype hk)) v hv).symm
  have first_surj (s : Q) : ∃ l : E, q l = (s,1) := by
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) s
    refine ⟨⟨⟨l,hLR l.property⟩,l.property⟩,?_⟩
    exact (hfirst l).trans (by rw [hl])
  rcases hom_eq_one_or_surjective_of_simple_quotient qB hqB f with hz | hs
  · have hmap : B.map q ≤ E.map q := by
      rintro x ⟨b,hb,rfl⟩
      obtain ⟨l,hl⟩ := first_surj (q b).1
      refine ⟨l,l.property,?_⟩
      have hbzero : (q b).2 = 1 := DFunLike.congr_fun hz (⟨b,hb⟩ : B)
      exact hl.trans (by ext <;> simp [hbzero])
    have hsup : B ≤ E ⊔ pCore 2 R := by
      have hh := map_le_iff_le_comap.mp hmap
      rwa [comap_map_eq,hker] at hh
    have hBE := perfect_le_of_le_sup_two B E (pCore 2 R) pCore_isPGroup hsup
    intro a ha
    exact hBE (show (⟨a,hAR ha⟩ : R) ∈ B from ha)
  · have hmap : (E ⊔ B).map q = ⊤ := by
      apply eq_top_iff.mpr
      rintro ⟨s,u⟩ _
      obtain ⟨a,ha⟩ := hs u
      obtain ⟨l,hl⟩ := first_surj (s * (q a).1⁻¹)
      refine ⟨l * a,mul_mem_sup l.property a.property,?_⟩
      rw [map_mul,hl]
      have ha' : (q a).2 = u := ha
      ext <;> simp [ha']
    have hgen : (E ⊔ B) ⊔ pCore 2 R = ⊤ := by
      have hh := congrArg (comap q) hmap
      rwa [comap_map_eq,comap_top,hker] at hh
    have hRC : (⊤ : Subgroup R) ≤ C := hgen ▸ sup_le (sup_le hEC hBC) hcoreC
    exact (hvnot (by
      intro r hr
      exact mem_centralizer_singleton_iff.mp (hRC (mem_top (⟨r,hr⟩ : R))))).elim

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces

