module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Kernel.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Fitting

/-!
# The two-group kernel of the original residual projection

Restrict the proved Sylow R₁ in O∞(KzR₁) to Kz, then pass through its
literal two-core quotient. The elementary-extension normalizer calculation
bounds the radical intersection there. Pulling back through O₂(Kz) and
restricting to N_Kz(R₁)^∞ proves that the existing residualProjection has
two-group kernel. Every restriction uses relative normality and the original
ambient inclusions; no kernel, Sylow or normalizer lifting premise is added.

The elementary-extension row remains a model input to be obtained from the
complete catalogue by this task's final assembly.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Kernel
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_radical_restrict (J K R : Subgroup G)
    (hKJ : K ≤ J) (hn : J ≤ normalizer (K : Set G))
    (hs : Chapter1.IsSylowIn 2 R ((solvableRadical J).map J.subtype)) :
    Chapter1.IsSylowIn 2 (R.subgroupOf K) (solvableRadical K) := by
  let A := K.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let e : A ≃* K := subgroupOfEquivOfLe hKJ
  let D := (solvableRadical J).map J.subtype
  have hrad : (solvableRadical K).map K.subtype = K ⊓ D := by
    have he : (solvableRadical A).map A.subtype = solvableRadical J ⊓ A := by
      rw [← radical_subgroupOf_normal A,subgroupOf_map_subtype]
    have hm := congrArg (map J.subtype) he
    rw [map_map,map_inf _ _ _ J.subtype_injective,map_subgroupOf_eq_of_le hKJ] at hm
    rw [← map_solvableRadical_equiv e,map_map]
    exact hm.trans (inf_comm _ _)
  have hDN : D ≤ normalizer (K ⊓ D : Set G) :=
    (le_inf ((map_subtype_le _).trans hn) D.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hnormal : ((K ⊓ D).subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer hDN
  have hh := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs
    (show K ⊓ D ≤ D from inf_le_right) hnormal.isSubnormal
  have hRD : R ≤ D := (Chapter1.isSylowIn_iff.mp hs).2.1
  have hint : R ⊓ (K ⊓ D) = R ⊓ K := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hRD))
  rw [hint] at hh
  apply (Chapter1.IsSylowIn.map_iff K.subtype K.subtype_injective).mp
  rw [subgroupOf_map_subtype,hrad]
  exact hh

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The elementary extension gives the two-group kernel of the actual
inclusion-induced residual projection. The radical/Sylow conclusions are
obtained from the existing source proof, not assumed. -/
theorem ofFlag_residualProjection_kernel_isPGroup (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (he : Chapter1.Section02.LocalModels.HasExtension
      ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    IsPGroup 2 (residualProjection (ofFlag S f X z H)).ker := by
  let E := ofFlag S f X z H
  let J := pointRadicalJoin E
  have hp3 : 3 < p := by
    have hpl := hp.1.two_le
    have h5 := hp.2.1
    omega
  let : Fact p.Prime := ⟨hp.1⟩
  have hm := twoFitting_sl2_of_elementary_extension hp3 he
  have hR := ofFlag_sylow_in_join_radical_of_prime_model S f X z H h hA hseed
    hp3 (radical_model_of_fitting_sl2 hp3 hm)
  have hRT : E.R₁ ≤ (T : Subgroup G) := by
    change (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hTK : (T : Subgroup G) ≤ normalizer (E.Kz : Set G) :=
    h.sylow_le_pointCentralizer.trans (le_normalizer_conjugateSpanBy _ _)
  have hJK : J ≤ normalizer (E.Kz : Set G) :=
    sup_le E.Kz.le_normalizer (hRT.trans hTK)
  have hs := sylow_radical_restrict J E.Kz E.R₁ le_sup_left hJK hR
  let q := QuotientGroup.mk' (pCore 2 E.Kz)
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsPerfect E.Kz := Radical.relative_component_perfect h.point_component
  let : Group.IsPerfect (E.Kz ⧸ pCore 2 E.Kz) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have htwo := radical_inf_normalizer_of_two_kernel q (QuotientGroup.mk'_surjective _)
    hq hp3 hn he (E.R₁.subgroupOf E.Kz) hs
  let i := inclusion (normalizerResidual_le (E := E))
  have hbound : (residualProjection E).ker ≤
      (solvableRadical E.Kz ⊓ normalizer (E.R₁.subgroupOf E.Kz : Set E.Kz)).comap i := by
    intro x hx
    refine ⟨(QuotientGroup.eq_one_iff (i x)).mp hx,?_⟩
    have hxn : (x : G) ∈ normalizer (E.R₁ : Set G) :=
      (Closure.residualIn_le _ x.property).2
    apply mem_normalizer_iff.mpr
    intro r
    exact (mem_normalizer_iff.mp hxn r.val)
  exact (htwo.comap_of_injective i (inclusion_injective _)).to_le hbound

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Kernel
