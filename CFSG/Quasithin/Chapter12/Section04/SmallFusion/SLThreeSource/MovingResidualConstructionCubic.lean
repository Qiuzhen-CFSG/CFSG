module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionBase
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionGeometry
public import Theory.GroupTheory.PResidual.SylowIndexThree

/-!
# The cubic quotient of the original plane residual

The marked action on the sixteen-element module makes the point stabilizer
have index fourteen in L. Since E is the fixed line plus that point, this is
also C_L(E). Its image in SL₃(2) has order twelve, so its Sylow two-subgroups
have index three. The residual/core comparison then gives the literal
O²(C_L(E))/O₂(O²(C_L(E))) quotient of order three.

Source: Aschbacher–Smith, proof of 12.4.6, printed p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The nonfixed-point orbit under L itself has fourteen elements. -/
theorem component_point_centralizer_index (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (v : G)
    (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V) :
    (centralizer ({v} : Set G)).relIndex L = 14 := by
  let : MulAction L G := {
    smul := fun g v => MulAut.conj (g : G) v
    one_smul := by intro v; change (1 : G) * v * 1⁻¹ = v; group
    mul_smul := by
      intro g k v
      change ((g : G) * (k : G)) * v * ((g : G) * (k : G))⁻¹ =
        (g : G) * ((k : G) * v * (k : G)⁻¹) * (g : G)⁻¹
      group }
  have ho : MulAction.orbit L v = (V : Set G) \ (fixedSubgroup L V : Set G) := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨(mem_normalizer_iff.mp (D.normalizes g.property) v).mp hvV, ?_⟩
      have hLF : L ≤ normalizer (fixedSubgroup L V : Set G) :=
        (le_inf D.normalizes
          (L.le_normalizer.trans (normalizer_le_normalizer_centralizer L))).trans
          inf_normalizer_le_normalizer_inf
      exact fun hw => hv ((mem_normalizer_iff.mp (hLF g.property) v).mpr hw)
    · intro hw
      obtain ⟨l, hl, he⟩ := ext.transitive_nonfixed hne v w hvV hw.1 hv hw.2
      exact ⟨⟨l, hl⟩, he⟩
  have hs : MulAction.stabilizer L v = (centralizer ({v} : Set G)).subgroupOf L := by
    ext g
    change MulAut.conj (g : G) v = v ↔ (g : G) ∈ centralizer ({v} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul
  change ((centralizer ({v} : Set G)).subgroupOf L).index = 14
  rw [← hs, MulAction.index_stabilizer, ho, Set.ncard_sdiff (show
    (fixedSubgroup L V : Set G) ⊆ V from inf_le_left)]
  change Nat.card V - Nat.card (fixedSubgroup L V) = 14
  rw [module_card_sixteen ext hne, ext.fixed_card_eq_two hne]

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The fixed line is contained in the chosen plane in the escape branch. -/
theorem fixed_le_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    fixedSubgroup L V ≤ d.E := by
  obtain ⟨hZ, _, _, _, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  rw [← d.fixed_plane]
  apply le_inf inf_le_left
  change fixedSubgroup L V ≤ centralizer (d.R : Set G)
  rw [← hZ]
  exact fun x hx => centralizer_le (show d.R ≤ T from inf_le_left)
    ((mem_omegaCenterIn_iff _ _).mp hx).2.1

/-- A nonfixed vector supplements the fixed line to the entire four-plane. -/
theorem plane_eq_fixed_sup_point (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E) :
    d.E = fixedSubgroup L V ⊔ zpowers d.v := by
  let B := fixedSubgroup L V ⊔ zpowers d.v
  have hBE : B ≤ d.E := sup_le hFE (zpowers_le.mpr d.mem_plane)
  have hc := card_dvd_of_le hBE
  rw [d.card_plane] at hc
  have hFB : fixedSubgroup L V ≤ B := le_sup_left
  have hlo : 2 < Nat.card B := by
    by_contra hb
    have he : fixedSubgroup L V = B := eq_of_le_of_card_ge hFB
      (by rw [ext.fixed_card_eq_two hne]; omega)
    exact d.nonfixed (he.symm ▸ (show d.v ∈ B from
      (le_sup_right : zpowers d.v ≤ B) (mem_zpowers _)))
  have hB4 : Nat.card B = 4 := by
    have hd := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show Nat.card B ∣ 2 ^ 2 from hc)
    obtain ⟨k, hk, he⟩ := hd
    interval_cases k
    · rw [he] at hlo
      norm_num at hlo
    · rw [he] at hlo
      norm_num at hlo
    · exact he
  exact (eq_of_le_of_card_ge hBE (by rw [hB4, d.card_plane])).symm

/-- The literal plane centralizer in L is the point stabilizer. -/
theorem component_plane_centralizer_eq_point (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E) :
    L ⊓ centralizer (d.E : Set G) = L ⊓ centralizer ({d.v} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left L (centralizer_le (Set.singleton_subset_iff.mpr d.mem_plane))
  · intro l hl
    refine ⟨hl.1, ?_⟩
    rw [d.plane_eq_fixed_sup_point ext hne hFE]
    have hF : l ∈ centralizer (fixedSubgroup L V : Set G) :=
      le_centralizer_iff.mp (show fixedSubgroup L V ≤ centralizer (L : Set G)
        from inf_le_right) hl.1
    have hz : zpowers d.v ≤ centralizer ({l} : Set G) := by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hl.2).symm
    have hline : l ∈ centralizer (zpowers d.v : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hz hx)
    rw [sup_eq_closure, centralizer_closure]
    intro x hx
    rcases hx with hx | hx
    · exact hF x hx
    · exact hline x hx

/-- For any group of order twelve its Sylow two-subgroups have index three. -/
private theorem sylow_index_of_card_twelve {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 12) (S : Sylow 2 H) : (S : Subgroup H).index = 3 := by
  have hs := S.card_eq_multiplicity
  have hfac : (Nat.factorization 12) 2 = 2 := by decide +kernel
  rw [hc, hfac] at hs
  norm_num at hs
  have hi := (S : Subgroup H).index_mul_card
  rw [hs, hc] at hi
  omega

/-- The two-core quotient of the original O²(C_L(E)) has order three. -/
theorem lineResidual_quotient_card (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E) :
    Nat.card (d.L₁ ⧸ pCore 2 d.L₁) = 3 := by
  let _ := D.elementary
  let C : Subgroup L := (centralizer ({d.v} : Set G)).subgroupOf L
  let q : L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ext.quotientEquiv.injective,
      QuotientGroup.ker_mk']
  have hkC : q.ker ≤ C := by
    intro l hl
    have he := ext.conjugation l (Additive.ofMul ⟨d.v, d.le_module d.mem_plane⟩)
    have hq1 : q l = 1 := hl
    change ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 at hq1
    rw [hq1, map_one] at he
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hi : C.index = 14 :=
    component_point_centralizer_index ext hne d.v (d.le_module d.mem_plane) d.nonfixed
  have hiq : (C.map q).index = 14 := (C.index_map_eq hq hkC).trans hi
  have hcq : Nat.card (C.map q) = 12 := by
    have hh := (C.map q).index_mul_card
    rw [hiq, Matrix.PSL3Two.card_SL] at hh
    omega
  let S : Sylow 2 C := Classical.choice inferInstance
  let f := q.subgroupMap C
  have hf : Function.Surjective f := q.subgroupMap_surjective C
  have hfk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap, hk]
    exact pCore_isPGroup.comap_subtype
  have hkerS : f.ker ≤ (S : Subgroup C) := hfk.le_sylow_of_normal S
  have hSi : (S : Subgroup C).index = 3 := by
    have hh := sylow_index_of_card_twelve hcq (S.mapSurjective hf)
    change ((S : Subgroup C).map f).index = 3 at hh
    rwa [(S : Subgroup C).index_map_eq hf hkerS] at hh
  have hres := residual_core_quotient_card_of_sylow_index_three S hSi
  let e₀ : C ≃* (L ⊓ centralizer ({d.v} : Set G) : Subgroup G) := {
    toFun := fun x => ⟨x, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let e : C ≃* (L ⊓ centralizer (d.E : Set G) : Subgroup G) :=
    e₀.trans (MulEquiv.subgroupCongr
      (d.component_plane_centralizer_eq_point ext hne hFE).symm)
  let er : pResidual 2 C ≃* pResidual 2 (L ⊓ centralizer (d.E : Set G) : Subgroup G) :=
    (e.subgroupMap (pResidual 2 C)).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))
  let ei : pResidual 2 (L ⊓ centralizer (d.E : Set G) : Subgroup G) ≃* d.L₁ :=
    (pResidual 2 _).equivMapOfInjective _ (L ⊓ centralizer (d.E : Set G)).subtype_injective
  let eq := QuotientGroup.congr _ _ (er.trans ei) (pCore_map_iso 2 (er.trans ei))
  exact (Nat.card_congr eq.toEquiv).symm.trans hres

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
