module
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.QuadraticSource
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# A quadratic four-group from a component mover of small displacement

If an involution moves a simple component and displaces at most two binary
dimensions, its perfect norm diagonal acts trivially on that displacement
space. A nontrivial involution of the diagonal therefore supplies a second
generator for the four-group in GLS2 25.14. The resulting group has trivial
centralizer on the original component and remains in its two-factor orbit
extended by the original moving involution.

This handles the rank-one moving actor in Aschbacher–Smith D.3.7, printed
p.197, using the literal displacement and without a field-degree comparison.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentNormalization.QuadraticSource
open Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : Subgroup G} {a : G}

omit [Finite G] in
private theorem diagonal_fixes_small_displacement (hK : IsComponent G K)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) (ha : a ^ 2 = 1)
    (hd : fixedCodim ρ (zpowers a) ≤ 2) :
    ∀ c ∈ (componentSwapNorm hK hm).range, ∀ v : V,
      ρ c (ρ a v - v) = ρ a v - v := by
  let N := (componentSwapNorm hK hm).range
  let : IsQuasisimple N := componentSwapNorm_range_quasisimple hK hm
  have hcomm (c : N) : Commute (c : G) a :=
    mem_centralizer_singleton_iff.mp
      (componentSwapNorm_range_le_centralizer hK hm ha c.property)
  let W : Subrepresentation (ρ.comp N.subtype) := {
    toSubmodule := LinearMap.range (ρ a - LinearMap.id)
    apply_mem_toSubmodule := by
      rintro c v ⟨w,rfl⟩
      refine ⟨ρ c w,?_⟩
      change ρ a (ρ c w) - ρ c w = ρ c (ρ a w - w)
      rw [map_sub]
      exact congrArg (fun z : V => z - ρ c w)
        (LinearMap.congr_fun ((ρ.map_mul a c).symm.trans
          ((congrArg ρ (hcomm c).eq.symm).trans (ρ.map_mul c a))) w) }
  have hdim : Module.finrank (ZMod 2) W.toSubmodule ≤ 2 := by
    change Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2
    rwa [← fixedCodim_zpowers_eq_displacement_rank]
  intro c hc v
  exact congrArg Subtype.val (PerfectInvolutionExtension.small_action_trivial
    W.toRepresentation hdim ⟨c,hc⟩ ⟨ρ a v - v,⟨v,rfl⟩⟩)

theorem small_mover_fourGroup (hρ : Function.Injective ρ)
    (hK : IsComponent G K) [IsSimpleGroup K]
    (ha : orderOf a = 2) (han : a ∉ normalizer (K : Set G))
    (hd : fixedCodim ρ (zpowers a) ≤ 2) :
    ∃ F : Subgroup G, Hypotheses ρ K F a ∧
      F ≤ K ⊔ K.map (MulAut.conj a).toMonoidHom ⊔ zpowers a := by
  let := hK.2
  have hm : K.map (MulAut.conj a).toMonoidHom ≠ K :=
    fun h => han (mem_normalizer_iff_map_conj_eq.mpr h)
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hz : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    have ho : Odd (Nat.card K) := by rw [Nat.odd_iff]; omega
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K ho)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 heven
  let c := componentSwapNorm hK hm u
  have hc : c ∈ (componentSwapNorm hK hm).range := ⟨u,rfl⟩
  have hco : orderOf c = 2 :=
    (orderOf_injective _ (NormPair.norm_injective_of_simple hK hm) u).trans hu
  have hca : Commute c a := mem_centralizer_singleton_iff.mp
    (componentSwapNorm_range_le_centralizer hK hm ha2 hc)
  have hpairC : K.map (MulAut.conj a).toMonoidHom ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hK.map_conj a).commutator_eq_bot_of_ne hK hm)
  have hcN : c ∈ normalizer (K : Set G) := mul_mem (K.le_normalizer u.property)
    (Subgroup.centralizer_le_normalizer _ (hpairC (mem_map_of_mem _ u.property)))
  have hcnot : c ∉ centralizer (K : Set G) := by
    intro h
    have huC : (u : G) ∈ centralizer (K : Set G) := by
      have hh := (centralizer (K : Set G)).mul_mem h
        ((centralizer (K : Set G)).inv_mem (hpairC (mem_map_of_mem
          (MulAut.conj a).toMonoidHom u.property)))
      change (u : G) * (a * u * a⁻¹) * (a * u * a⁻¹)⁻¹ ∈ centralizer (K : Set G) at hh
      simpa only [mul_inv_cancel_right] using hh
    have huz : u ∈ center K := mem_center_iff.mpr fun x =>
      Subtype.ext (mem_centralizer_iff.mp huC x x.property)
    rw [hz,mem_bot] at huz
    simp [huz] at hu
  have hac : a ≠ c := fun h => han (h ▸ hcN)
  let F := closure ({a,c} : Set G)
  have hfour : IsKleinFour F := isKleinFour_closure_pair_of_orderOf a c ha hco hac hca.symm
  let := hfour
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have ha_sq : a * a = 1 := by simpa only [pow_two] using ha2
  have hc_sq : c * c = 1 := by simpa only [pow_two,hco] using pow_orderOf_eq_one c
  have hcases (x : G) (hx : x ∈ F) : x = 1 ∨ x = a ∨ x = c ∨ x = a*c :=
    (mem_closure_pair_iff a c ha_sq hc_sq hca.symm x).mp hx
  have hquad : FixesDisplacements ρ a F := by
    have hfa := involution_fixes_displacement ρ ha_sq
    have hfc := diagonal_fixes_small_displacement ρ hK hm ha2 hd c hc
    intro x hx v
    rcases hcases x hx with rfl | rfl | rfl | rfl
    · simp
    · exact hfa v
    · exact hfc v
    · rw [map_mul,Module.End.mul_apply,hfc,hfa]
  have hcent : F ⊓ centralizer (K : Set G) = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hx,hxc⟩
    rw [mem_bot]
    rcases hcases x hx with rfl | rfl | rfl | rfl
    · rfl
    · exact (han (Subgroup.centralizer_le_normalizer _ hxc)).elim
    · exact (hcnot hxc).elim
    · have hh := (normalizer (K : Set G)).mul_mem (Subgroup.centralizer_le_normalizer _ hxc)
        ((normalizer (K : Set G)).inv_mem hcN)
      exact (han (by simpa only [mul_inv_cancel_right] using hh)).elim
  refine ⟨F,⟨hρ,hK,inferInstance,hfour.card_four,subset_closure (by simp),ha,hm,hquad,hcent⟩,?_⟩
  apply (closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact mem_sup_right (mem_zpowers _)
  · exact mem_sup_left (NormPair.norm_le_pair hK hm hc)

end CFSG.Quasithin.ChapterB.ComponentNormalization.QuadraticSource
