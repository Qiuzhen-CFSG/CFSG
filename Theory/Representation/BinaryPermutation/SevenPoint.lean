module
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.GroupAction.AbelianPermutationOrbitBound
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryPermutation.TransvectionCoreMap
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections.Linear
public import Theory.SpecificGroups.AlternatingSeven.ConjugatePairs
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
import Mathlib.Tactic

/-!
# Arbitrary faithful binary modules between A₇ and S₇

A nonswap involution has an even conjugate whose product has order five or six.
Two transvections cannot have that product order, so any transvection is a
literal transposition. Its conjugate centers construct an equivariant map from
the augmentation core. The odd-degree core is simple, making this map injective.
No semisimplicity or irreducibility of the given module is required.

For strong offenders, the natural-core embedding supplies the ordinary orbit
bound whenever a transvection exists. Otherwise every nonidentity involution
has displacement at least two. The elementary rank bound reduces a strict
offender to rank three and fixed codimension two. Two explicit centralizer
conjugates then contradict the common fixed-space identity.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.3–B.4
and the arbitrary faithful-module argument in 13.8.24, printed pp.958–959
(PDF pp.975–976, combined manuscript, 1 March 2004).
-/

public section
open scoped IsMulCommutative
namespace BinaryPermutation.SevenPoint
open Equiv Subgroup Representation Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every transvection involution is a transposition in the literal marking. -/
theorem isSwap_of_fixedCodim_one (J : Subgroup (Perm (Fin 7)))
    (hJ : alternatingGroup (Fin 7) ≤ J) (ρ : Representation (ZMod 2) J V)
    (hf : Function.Injective ρ) (a : J) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hc : fixedCodim ρ (zpowers a) = 1) : (a : Perm (Fin 7)).IsSwap := by
  let φ : J →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      ρ.asGroupHom
  have hφ : Function.Injective φ := fun x y h => hf (congrArg LinearEquiv.toLinearMap h)
  have ht : φ a ∈ LinearEquiv.transvections (ZMod 2) V := by
    apply Representation.SymmetricEightTransvections.Linear.of_small_displacement
    exact (TransvectionCoreMap.rank_displacement_eq_fixedCodim ρ a).trans hc |>.le
  by_contra hn
  have ho : orderOf (a : Perm (Fin 7)) = 2 := by
    exact (Subgroup.orderOf_coe a).trans (orderOf_eq_prime ha2 ha)
  obtain ⟨k, hk⟩ := AlternatingSeven.ConjugatePairs.nonswap_pair a ho hn
  let x : J := ⟨k, hJ k.property⟩
  let b : J := x * a * x⁻¹
  have hb : φ b ∈ LinearEquiv.transvections (ZMod 2) V := by
    simpa only [b, map_mul, map_inv] using
      Representation.SymmetricEightTransvections.Linear.conjugate (φ x) (φ a) ht
  have horder : orderOf (φ a * φ b) = orderOf
      ((a : Perm (Fin 7)) * ((k : Perm (Fin 7)) * a * (k : Perm (Fin 7))⁻¹)) := by
    rw [← map_mul, orderOf_injective φ hφ,
      ← orderOf_injective J.subtype Subtype.val_injective]
    rfl
  rcases Representation.SymmetricEightTransvections.Linear.product_cube_or_fourth
      (φ a) (φ b) ht hb with h3 | h4
  · have hd := orderOf_dvd_of_pow_eq_one h3
    rw [horder] at hd
    rcases hk with hk | hk <;> rw [hk] at hd <;> norm_num at hd
  · have hd := orderOf_dvd_of_pow_eq_one h4
    rw [horder] at hd
    rcases hk with hk | hk <;> rw [hk] at hd <;> norm_num at hd

private theorem eq_top_of_swap (J : Subgroup (Perm (Fin 7)))
    (hJ : alternatingGroup (Fin 7) ≤ J) (a : J) (ha : (a : Perm (Fin 7)).IsSwap) : J = ⊤ := by
  have hout : (a : Perm (Fin 7)) ∉ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, ha.sign_eq]
    decide
  apply top_unique
  intro g _
  by_cases hg : g ∈ alternatingGroup (Fin 7)
  · exact hJ hg
  · have he : g * (a : Perm (Fin 7))⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
      exact iff_of_false hg hout
    simpa only [inv_mul_cancel_right] using J.mul_mem (hJ he) a.property

omit [FiniteDimensional (ZMod 2) V] in
private theorem coreMap_injective
    (σ : Representation (ZMod 2) (Perm (Fin 7)) V) (hf : Function.Injective σ)
    (hr : ∀ i j : Fin 7, i ≠ j →
      Module.finrank (ZMod 2) (LinearMap.range (σ (swap i j) - LinearMap.id)) = 1) :
    Function.Injective (TransvectionCoreMap.coreMap σ hr 0) := by
  let f := TransvectionCoreMap.coreMap σ hr 0
  let W := f.ker.map (core (Fin 7)).subtype
  have hW : ∀ g : alternatingGroup (Fin 7), ∀ v ∈ W,
      representation (Fin 7) g.val v ∈ W := by
    rintro g v ⟨u, hu, rfl⟩
    refine ⟨coreRepresentation (Fin 7) g.val u, ?_, rfl⟩
    change f (coreRepresentation (Fin 7) g.val u) = 0
    rw [TransvectionCoreMap.coreMap_equivariant σ hr hf]
    change f u = 0 at hu
    rw [hu, map_zero]
  rcases invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card (Fin 7)) W hW with h | h
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp
      (core_isCompl_constants (Fin 7) (by decide)).disjoint v.val v.property
      (h ⟨v, hv, rfl⟩)
  · have hz : f (TransvectionCoreMap.pair 0 1) = 0 := by
      obtain ⟨v, hv, he⟩ := h (TransvectionCoreMap.pair 0 1).property
      have he' : v = TransvectionCoreMap.pair 0 1 := Subtype.ext he
      exact he' ▸ hv
    exact False.elim ((TransvectionCoreMap.center_spec σ hr 0 1 (by decide)).1
      ((TransvectionCoreMap.coreMap_pair σ hr hf 0 0 1).symm.trans hz))

/-- Transvection centers embed the natural module without any semisimplicity premise. -/
theorem exists_core_embedding (J : Subgroup (Perm (Fin 7)))
    (hJ : alternatingGroup (Fin 7) ≤ J) (ρ : Representation (ZMod 2) J V)
    (hf : Function.Injective ρ) (a : J) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hc : fixedCodim ρ (zpowers a) = 1) :
    ∃ j : core (Fin 7) →ₗ[ZMod 2] V, Function.Injective j ∧
      ∀ (g : J) v, j (coreRepresentation (Fin 7) (g : Perm (Fin 7)) v) = ρ g (j v) := by
  have hs := isSwap_of_fixedCodim_one J hJ ρ hf a ha ha2 hc
  have htop := eq_top_of_swap J hJ a hs
  subst J
  let e : (⊤ : Subgroup (Perm (Fin 7))) ≃* Perm (Fin 7) := Subgroup.topEquiv
  let σ := ρ.comp e.symm.toMonoidHom
  have hfσ : Function.Injective σ := hf.comp e.symm.injective
  have hd : Module.finrank (ZMod 2) (LinearMap.range (σ (e a) - LinearMap.id)) = 1 := by
    have he : σ (e a) = ρ a := by simp [σ]
    rw [he, TransvectionCoreMap.rank_displacement_eq_fixedCodim, hc]
  let hr := TransvectionCoreMap.swap_rank_one σ hs hd
  refine ⟨TransvectionCoreMap.coreMap σ hr 0, coreMap_injective σ hfσ hr, ?_⟩
  intro g v
  have he := TransvectionCoreMap.coreMap_equivariant σ hr hfσ 0 (e g) v
  change _ = ρ (e.symm (e g)) _ at he
  rw [e.symm_apply_apply] at he
  simpa only [e, Subgroup.topEquiv_apply] using he

end BinaryPermutation.SevenPoint

namespace BinaryPermutation.SevenPoint
open Equiv Subgroup Representation Representation.BinaryOffender

private theorem rank_three_obstruction (A : Subgroup (Perm (Fin 7)))
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    ∃ b ∈ A, b ≠ 1 ∧ b ∈ alternatingGroup (Fin 7) ∧
      ∃ a ∈ A, ∃ g ∈ alternatingGroup (Fin 7),
        Commute b g ∧ ¬ Commute a (g * a * g⁻¹) := by
  let b : Perm (Fin 7) := swap 0 1 * swap 2 3
  let a : Perm (Fin 7) := swap 4 5
  let g : Perm (Fin 7) := swap 0 1 * swap 5 6
  have hb1 : b ≠ 1 := by decide +kernel
  have hb : b ∈ alternatingGroup (Fin 7) := by rw [Perm.mem_alternatingGroup]; decide +kernel
  have hg : g ∈ alternatingGroup (Fin 7) := by rw [Perm.mem_alternatingGroup]; decide +kernel
  have hbg : Commute b g := by unfold Commute SemiconjBy; decide +kernel
  have hbad : ¬ Commute a (g * a * g⁻¹) := by unfold Commute SemiconjBy; decide +kernel
  obtain ⟨x, hx⟩ := AlternatingSevenConjugatePair.ElementaryGeometry.elementary_rank_three_conjugacy A hA hr
  have hba : b ∈ A.map (MulAut.conj x).toMonoidHom ∧
      a ∈ A.map (MulAut.conj x).toMonoidHom := by
    rcases hx with hx | hx <;> rw [hx] <;> constructor
    · exact ⟨(1, 1, 0), by decide +kernel⟩
    · exact ⟨(0, 0, 1), by decide +kernel⟩
    · exact ⟨(1, 0, 0), by decide +kernel⟩
    · exact ⟨(0, 0, 1), by decide +kernel⟩
  let e := MulAut.conj x⁻¹
  have hmem (z : Perm (Fin 7)) (hz : z ∈ A.map (MulAut.conj x).toMonoidHom) : e z ∈ A := by
    obtain ⟨w, hw, rfl⟩ := hz
    change x⁻¹ * (x * w * x⁻¹) * x ∈ A
    have he : x⁻¹ * (x * w * x⁻¹) * x = w := by group
    rw [he]
    exact hw
  have heven (z : Perm (Fin 7)) (hz : z ∈ alternatingGroup (Fin 7)) :
      e z ∈ alternatingGroup (Fin 7) :=
    (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem z hz x⁻¹
  refine ⟨e b, hmem b hba.1, fun h => hb1 (e.injective (h.trans e.map_one.symm)),
    heven b hb, e a, hmem a hba.2, e g, heven g hg, hbg.map e, ?_⟩
  intro h
  apply hbad
  apply e.injective
  simpa only [map_mul, map_inv] using h.eq

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem commute_of_common_fixedSpace (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (b t u : G) (hb : b * b = 1)
    (hbt : Commute b t) (hbu : Commute b u)
    (ht : ∀ v, ρ b v = v → ρ t v = v)
    (hu : ∀ v, ρ b v = v → ρ u v = v) : Commute t u := by
  have hdisp (s : G) (hbs : Commute b s)
      (hs : ∀ v, ρ b v = v → ρ s v = v) (v : V) :
      ρ b (ρ s v - v) = ρ s v - v := by
    have hbb : ρ b (ρ b v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, hb, map_one, Module.End.one_apply]
    have hn (w : V) : -w = w := neg_eq_of_add_eq_zero_left (ZModModule.add_self w)
    have hbv : ρ b (ρ b v - v) = ρ b v - v := by
      rw [map_sub, hbb]; simp only [sub_eq_add_neg, hn, add_comm]
    have hc : ρ b (ρ s v) = ρ s (ρ b v) := by
      simpa only [map_mul, Module.End.mul_apply] using
        congrArg (fun f : Module.End (ZMod 2) V => f v) (congrArg ρ hbs.eq)
    have hv := hs (ρ b v - v) hbv
    rw [map_sub] at hv
    rw [map_sub, hc]
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      have := sub_eq_sub_iff_add_eq_add.mp hv
      abel_nf at this ⊢
      exact this)
  apply hf
  ext v
  have ht' := ht (ρ u v - v) (hdisp u hbu hu v)
  have hu' := hu (ρ t v - v) (hdisp t hbt ht v)
  simp only [map_sub] at ht' hu'
  simp only [map_mul, Module.End.mul_apply]
  calc
    ρ t (ρ u v) = (ρ u v - v) + ρ t v := sub_eq_iff_eq_add.mp ht'
    _ = (ρ t v - v) + ρ u v := by abel
    _ = ρ u (ρ t v) := (sub_eq_iff_eq_add.mp hu').symm

/-- Fixing the fixed space of an involution forces commuting centralizer conjugates. -/
theorem commute_conjugate_of_fixes_fixedSpace (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (b a g : G) (hb : b * b = 1)
    (hba : Commute b a) (hbg : Commute b g)
    (ha : ∀ v, ρ b v = v → ρ a v = v) : Commute a (g * a * g⁻¹) := by
  apply commute_of_common_fixedSpace ρ hf b a (g * a * g⁻¹) hb hba
    ((hbg.mul_right hba).mul_right hbg.inv_right) ha
  intro v hv
  have hgv : ρ b (ρ g⁻¹ v) = ρ g⁻¹ v := by
    have hc := congrArg (fun f : Module.End (ZMod 2) V => f v)
      (congrArg ρ hbg.inv_right.eq)
    simpa only [map_mul, Module.End.mul_apply, hv] using hc
  simp only [map_mul, Module.End.mul_apply, ha _ hgv, ρ.self_inv_apply]

end BinaryPermutation.SevenPoint

namespace BinaryPermutation.SevenPoint
open Equiv Subgroup Representation Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem codim_le {G : Type*} [Group G] (ρ : Representation (ZMod 2) G V)
    {A B : Subgroup G} (h : A ≤ B) : fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ h)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private theorem no_strong_of_embedding (J : Subgroup (Perm (Fin 7)))
    (ρ : Representation (ZMod 2) J V)
    (j : core (Fin 7) →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (heq : ∀ (g : J) v, j (coreRepresentation (Fin 7) g.val v) = ρ g (j v)) :
    ¬ IsStrongFFModule ρ := by
  let R : Subrepresentation ρ := {
    toSubmodule := LinearMap.range j
    apply_mem_toSubmodule := by
      rintro g v ⟨u, rfl⟩
      exact ⟨coreRepresentation _ g.val u, heq g u⟩ }
  let e : core (Fin 7) ≃ₗ[ZMod 2] R.toSubmodule := LinearEquiv.ofInjective j hj
  have he : ∀ g v, e ((coreRepresentation (Fin 7)).comp J.subtype g v) =
      R.toRepresentation g (e v) := fun g v => Subtype.ext (heq g v)
  rintro ⟨A, hA, hlt⟩
  let : IsElementaryAbelian 2 A := hA.2
  let B := A.map J.subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map J.subtype
  have hB : IsElementaryTwo B := by
    refine ⟨?_, inferInstance⟩
    intro he
    apply hA.1
    apply Subgroup.map_injective J.subtype_injective
    simpa only [Subgroup.map_bot] using he
  have hr : rank B = rank A := rank_map_injective J.subtype J.subtype_injective A
  have hcard : Nat.card B = 2 ^ rank B := hB.card_eq_two_pow_rank
  have hbound : rank B ≤ fixedCodim (representation (Fin 7)) B := by
    apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
    rw [← hcard, fixedCodim_full_eq_card_sub_card_orbits]
    exact AbelianPermutation.card_le_two_pow_degree_sub_orbits B
  have hc := OddTransport.fixedCodim_eq_of_equivariant
    ((coreRepresentation (Fin 7)).comp J.subtype) R.toRepresentation e he A
  have hb := fixedCodim_subrepresentation_le ρ R A
  have ho := fixedCodim_core_eq_full_odd (Fin 7) (by decide) B
  have ht : fixedCodim ((coreRepresentation (Fin 7)).comp J.subtype) A =
      fixedCodim (coreRepresentation (Fin 7)) B := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  omega

/-- No faithful binary module for a seven-point intermediate group has a strict offender. -/
theorem no_strong (J : Subgroup (Perm (Fin 7)))
    (hJ : alternatingGroup (Fin 7) ≤ J) (ρ : Representation (ZMod 2) J V)
    (hf : Function.Injective ρ) : ¬ IsStrongFFModule ρ := by
  by_cases htrans : ∃ a : J, a ≠ 1 ∧ a ^ 2 = 1 ∧ fixedCodim ρ (zpowers a) = 1
  · obtain ⟨a, ha, ha2, hc⟩ := htrans
    obtain ⟨j, hj, he⟩ := exists_core_embedding J hJ ρ hf a ha ha2 hc
    exact no_strong_of_embedding J ρ j hj he
  rintro ⟨A, hA, hlt⟩
  let : IsElementaryAbelian 2 A := hA.2
  let B := A.map J.subtype
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.map J.subtype⟩
    intro he
    apply hA.1
    apply Subgroup.map_injective J.subtype_injective
    simpa only [Subgroup.map_bot] using he
  have hrB : rank B = rank A := rank_map_injective J.subtype J.subtype_injective A
  have hr := AlternatingSevenConjugatePair.ElementaryGeometry.rank_le_three B hB
  have hlower (a : J) (ha : a ∈ A) (hne : a ≠ 1) :
      2 ≤ fixedCodim ρ (zpowers a) := by
    have hp := fixedCodim_pos_of_faithful ρ hf (by simpa using hne : zpowers a ≠ ⊥)
    have hn : fixedCodim ρ (zpowers a) ≠ 1 := fun he =>
      htrans ⟨a, hne, elemPow_eq_one_of_isElementaryAbelian a ha, he⟩
    omega
  obtain ⟨c, hc, hc1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have h2 := (hlower c hc hc1).trans (codim_le ρ (zpowers_le.mpr hc))
  have hthree : rank B = 3 := by omega
  have hcodim : fixedCodim ρ A = 2 := by omega
  obtain ⟨b, hb, hb1, _, a, ha, g, hg, hbg, hbad⟩ := rank_three_obstruction B hB hthree
  obtain ⟨b', hb', hbe⟩ := hb
  obtain ⟨a', ha', hae⟩ := ha
  change (b' : Perm (Fin 7)) = b at hbe
  change (a' : Perm (Fin 7)) = a at hae
  let g' : J := ⟨g, hJ hg⟩
  have hb1' : b' ≠ 1 := by intro he; apply hb1; rw [← hbe, he]; rfl
  have hb2 : b' * b' = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b' hb'
  have hba : Commute b' a' := by
    exact congrArg Subtype.val (show (⟨b', hb'⟩ : A) * ⟨a', ha'⟩ = ⟨a', ha'⟩ * ⟨b', hb'⟩ from mul_comm _ _)
  have hbg' : Commute b' g' := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, hbe, g'] using hbg.eq
  have heq : fixedSpace ρ A = fixedSpace ρ (zpowers b') := by
    apply fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr hb')
    have hlow := hlower b' hb' hb1'
    have hupp := codim_le ρ (zpowers_le.mpr hb')
    omega
  have hfix : ∀ v, ρ b' v = v → ρ a' v = v := by
    intro v hv
    have hm := (mem_fixedSpace_zpowers_iff ρ b' v).mpr hv
    rw [← heq] at hm
    exact hm ⟨a', ha'⟩
  have hcomm := commute_conjugate_of_fixes_fixedSpace ρ hf b' a' g' hb2 hba hbg' hfix
  apply hbad
  change a * (g * a * g⁻¹) = (g * a * g⁻¹) * a
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hae, g'] using congrArg Subtype.val hcomm.eq

end BinaryPermutation.SevenPoint
