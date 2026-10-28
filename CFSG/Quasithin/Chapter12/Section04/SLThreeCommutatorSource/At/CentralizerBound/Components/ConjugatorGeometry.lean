module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.Models
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Same-conjugator plane geometry for 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

Two distinct hyperplanes of the original binary four-space generate V and
intersect in a plane. If the square of the chosen conjugator fixes U, it
normalizes this very intersection. A cubic normalizing both hyperplanes is
faithful on their intersection by the proved local-centralizer equality.
Source: Aschbacher--Smith, 12.4.8, printed p.815.
-/
public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The square condition refers to the same l used in the literal intersection. -/
theorem Configuration.conjugate_plane_geometry (c : Configuration T L V U)
    {l : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G)) :
    let U₀ := U ⊓ U.map (MulAut.conj l).toMonoidHom
    U ⊔ U.map (MulAut.conj l).toMonoidHom = V ∧
      Nat.card U₀ = 4 ∧ subgroupCorank U U₀ = 1 ∧
      l ∈ normalizer (U₀ : Set G) := by
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.le_module
  let W := U.map (MulAut.conj l).toMonoidHom
  let U₀ := U ⊓ W
  have hVfix := mem_normalizer_iff_map_conj_eq.mp (c.chosen.normalizes hl)
  have hWV : W ≤ V := (map_mono c.le_module).trans hVfix.le
  have hU := hyperplane_card c.extension c.fixed_nontrivial c.le_module c.corank
  have hV := module_card c.extension c.fixed_nontrivial
  have hW : Nat.card W = 8 := (card_map_of_injective (MulAut.conj l).injective).trans hU
  have hne : W ≠ U := fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he)
  have hsup : U ⊔ W = V := by
    have hd : Nat.card (U ⊔ W : Subgroup G) ∣ 16 := hV ▸ card_dvd_of_le (sup_le c.le_module hWV)
    have hlo : 8 ≤ Nat.card (U ⊔ W : Subgroup G) := hU ▸ card_le_of_le le_sup_left
    have hneq : Nat.card (U ⊔ W : Subgroup G) ≠ 8 := by
      intro hc
      have he : U = U ⊔ W := eq_of_le_of_card_ge le_sup_left (by omega)
      exact hne (eq_of_le_of_card_ge (he ▸ (le_sup_right : W ≤ U ⊔ W)) (by omega))
    have he : Nat.card (U ⊔ W : Subgroup G) = 16 := by
      have hd' : Nat.card (U ⊔ W : Subgroup G) ∈ Nat.divisors 16 :=
        Nat.mem_divisors.mpr ⟨hd,by decide⟩
      have ht : Nat.divisors 16 = {1,2,4,8,16} := by decide
      rw [ht] at hd'
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd'
      omega
    exact eq_of_le_of_card_ge (sup_le c.le_module hWV) (by omega)
  have hn : W ≤ normalizer (U : Set G) := by
    apply (show W ≤ centralizer (U : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro w hw u hu
    exact setLike_mul_comm (c.le_module hu) (hWV hw)
  have hc : Nat.card U₀ = 4 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U W hn
    rw [hU,hW,hsup,hV] at hh
    change 8 * 8 = Nat.card U₀ * 16 at hh
    omega
  have hcor : subgroupCorank U U₀ = 1 := by
    have hi : U₀.relIndex U = 2 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) U₀ U bot_le inf_le_left
      simp only [relIndex_bot_left] at hh
      rw [hc,hU] at hh
      omega
    rw [relIndex_eq_two_pow_quotient_finrank,← subgroupCorank_eq_quotient_finrank] at hi
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hi)
  have hs : W.map (MulAut.conj l).toMonoidHom = U := by
    have he : (MulAut.conj l).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
        (MulAut.conj (l ^ 2)).toMonoidHom := by
      ext x
      change l * (l * x * l⁻¹) * l⁻¹ = (l ^ 2) * x * (l ^ 2)⁻¹
      simp only [pow_two]
      group
    change (U.map _).map _ = U
    rw [map_map,he]
    exact mem_normalizer_iff_map_conj_eq.mp hsq
  refine ⟨hsup,hc,hcor,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  change (U ⊓ W).map (MulAut.conj l).toMonoidHom = U ⊓ W
  rw [Subgroup.map_inf U W _ (MulAut.conj l).injective,hs]
  exact inf_comm W U

/-- The cubic remains faithful on the actual intersection plane. -/
theorem Configuration.cubic_on_conjugate_plane (c : Configuration T L V U)
    {l x : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G))
    (hxL : x ∈ L) (hxN : x ∈ normalizer (U : Set G))
    (hxU : x ∉ centralizer (U : Set G))
    (hlX : l ∈ normalizer (zpowers x : Set G)) :
    let U₀ := U ⊓ U.map (MulAut.conj l).toMonoidHom
    x ∈ normalizer (U₀ : Set G) ∧ x ∉ centralizer (U₀ : Set G) := by
  let U₀ := U ⊓ U.map (MulAut.conj l).toMonoidHom
  have hg := c.conjugate_plane_geometry hl hm hsq
  have hnX : zpowers x ≤ normalizer (U : Set G) := zpowers_le.mpr hxN
  have hnW : zpowers x ≤ normalizer (U.map (MulAut.conj l).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj l).toMonoidHom) hnX
    have hX : (zpowers x).map (MulAut.conj l).toMonoidHom = zpowers x :=
      mem_normalizer_iff_map_conj_eq.mp hlX
    rw [hX] at hh
    exact hh.trans (U.le_normalizer_map (MulAut.conj l).toMonoidHom)
  refine ⟨inf_normalizer_le_normalizer_inf ⟨hxN,hnW (mem_zpowers x)⟩,?_⟩
  intro hx
  have he := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2
      U₀ inf_le_left hg.2.2.1
  have hxV := he.2.2.1.le ⟨c.chosen.normalizes hxL,hx⟩
  exact hxU ((centralizer_le c.le_module) hxV)

/-- The existing seed-layer theorem applies to this very intersection,
without an independently chosen plane or conjugator. -/
theorem Configuration.component_le_conjugate_plane_layer (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {l : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G)) :
    let U₀ := U ⊓ U.map (MulAut.conj l).toMonoidHom
    IsSQTK KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
      K ≤ (componentLayer (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype := by
  apply c.component_le_plane_layer hK _ inf_le_left
  intro he
  have hc := (c.conjugate_plane_geometry hl hm hsq).2.1
  rw [he,card_bot] at hc
  omega
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
