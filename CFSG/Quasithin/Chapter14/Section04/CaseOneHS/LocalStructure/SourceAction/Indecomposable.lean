module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Component
public import Theory.ElementaryAbelian.AnisotropicQuadratic
public import Theory.ElementaryAbelian.Injective

/-!
# Indecomposability of the original tilded HS module

An invariant complement to the tilded center would identify its square form
with an invariant quadratic form on the transitive natural module. The binary
anisotropic bound supplies a nonzero singular vector. Transitivity then makes
the square form zero everywhere, contradicting the nonzero commutator form.
Since the center has order four and the marked point has order two, the kernel
of Ũ → Û has order two. Thus every invariant subgroup surjecting onto Û is
all of Ũ, and the canonical component acts indecomposably on Ũ.

The original natural coordinates remain explicit; their source construction
belongs to qt-d-hs-action-source. CoreMovement proves the core commutator bound,
and SourceAction assembles all component clauses.
Source: Aschbacher--Smith, 14.3.32(4), printed p.1004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

private theorem invariant_uhat_alternatives (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) (A : Subgroup F.Uhat)
    (hA : ∀ h : F.H, (h : G) ∈ sourceComponent F → ∀ x ∈ A, F.uhatAction h x ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  by_cases hb : A = ⊥
  · exact Or.inl hb
  right
  obtain ⟨x, hx, hxn⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hb)
  apply top_unique
  intro y _
  by_cases hy : y = 1
  · exact hy ▸ A.one_mem
  obtain ⟨h, hh, he⟩ := hc.sourceComponent_transitive F x y hxn hy
  exact he ▸ hA h hh x hx

private theorem no_invariant_complement [IsMulCommutative V] (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) (hne : ¬ IsMulCommutative F.U)
    (A : Subgroup (F.tilde F.U))
    (hA : ∀ h : F.H, (h : G) ∈ sourceComponent F →
      A.map ((F.localTildeAction F.H le_rfl) h).toMonoidHom = A)
    (hfull : A.map (F.tildeToUhat (by decide)) = ⊤)
    (hdis : Disjoint A (F.tildeToUhat (by decide)).ker) : False := by
  let := F.tilde_elementary_of_point htwo hphi
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective A.subtype A.subtype_injective
  let : IsElementaryAbelian 2 (Multiplicative (ZMod 2)) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide) }
  let f := (F.tildeToUhat (by decide)).comp A.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, he⟩ := show y ∈ A.map (F.tildeToUhat (by decide)) by rw [hfull]; trivial
    exact ⟨⟨a, ha⟩, he⟩
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro a ha
    exact Subtype.ext (hdis.le_bot ⟨a.property, ha⟩)
  let e := MulEquiv.ofBijective f ⟨hi, hf⟩
  let mark := SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) hphi)
  let sq (a : A) : Multiplicative (ZMod 2) := mark (F.tildeSquare (by decide) htwo hphi a)
  let pol (a b : A) : Multiplicative (ZMod 2) := mark (F.tildePolar (by decide) htwo hphi a b)
  have hs1 : sq 1 = 1 := by
    have he : F.tildeSquare (by decide) htwo hphi 1 = 1 := by
      apply Subtype.ext
      simpa only [map_one, one_pow, coe_one] using F.tildeSquare_apply_map (by decide) htwo hphi 1
    exact (congrArg mark he).trans (map_one mark)
  have hsq (a b : A) : sq (a * b) = sq a * sq b * pol a b := by
    dsimp [sq, pol]
    rw [F.tildeSquare_mul, map_mul, map_mul]
  have hpol (a b c : A) : pol (a * b) c = pol a c * pol b c := by
    dsimp [pol]
    rw [F.tildePolar_mul_left, map_mul]
  have hAc : Nat.card A = 16 := (Nat.card_congr e.toEquiv).trans (hc.card_uhat F)
  obtain ⟨a, ha, has⟩ : ∃ a : A, a ≠ 1 ∧ sq a = 1 := by
    by_contra! hn
    have hb := IsElementaryAbelian.card_le_sq_of_anisotropic_quadratic sq pol hs1 hsq hpol
      (fun a ha => by_contra fun hn' => hn a hn' ha)
    have hc2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
    rw [hAc, hc2] at hb
    norm_num at hb
  have hs (b : A) : sq b = 1 := by
    by_cases hb : b = 1
    · simpa only [hb] using hs1
    have hfa : f a ≠ 1 := fun h => ha (hi (by simpa only [map_one] using h))
    have hfb : f b ≠ 1 := fun h => hb (hi (by simpa only [map_one] using h))
    obtain ⟨h, hh, he⟩ := hc.sourceComponent_transitive F (f a) (f b) hfa hfb
    have haA : F.localTildeAction F.H le_rfl h (a : F.tilde F.U) ∈ A :=
      (hA h hh).le (mem_map_of_mem _ a.property)
    have hab : (⟨F.localTildeAction F.H le_rfl h (a : F.tilde F.U), haA⟩ : A) = b := by
      apply hi
      exact (F.tildeToUhat_equivariant (by decide) h a).trans he
    have hhq := F.tildeSquare_invariant (by decide) htwo hphi h a
    have hv : sq ⟨F.localTildeAction F.H le_rfl h (a : F.tilde F.U), haA⟩ = sq a := congrArg mark hhq
    rw [hab, has] at hv
    exact hv
  have hp (a b : A) : F.tildePolar (by decide) htwo hphi a b = 1 := by
    apply mark.injective
    have hh := hsq a b
    rw [hs, hs, hs, one_mul, one_mul] at hh
    exact hh.symm.trans (map_one mark).symm
  obtain ⟨x, y, hxy⟩ := F.uhatCommutator_nonzero (by decide) htwo hphi hne
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  exact hxy ((F.uhatCommutator_tildeToUhat (by decide) htwo hphi a b).trans (hp a b))

omit [Finite G] in
private theorem tildeToUhat_ker_card [IsMulCommutative V] (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hZ : Nat.card (center F.U) = 4) :
    Nat.card (F.tildeToUhat (by decide)).ker = 2 := by
  let m := F.tildeMap F.U F.U_le_H
  have hm := m.ker.card_mul_index
  have hmc : Nat.card m.ker = 2 := by
    rw [F.tildeMap_U_ker, ← hphi]
    exact F.frattini_card_two_of_point (by decide) hphi
  rw [hmc, index_ker, MonoidHom.range_eq_top.mpr (F.tildeMap_surjective F.U F.U_le_H), card_top] at hm
  have hU := (center F.U).card_eq_card_quotient_mul_card_subgroup
  rw [hZ, hc.card_uhat F] at hU
  have hp := (F.tildeToUhat (by decide)).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (F.tildeToUhat_surjective (by decide)),
    card_top, hc.card_uhat F] at hp
  omega

theorem NaturalCoordinates.invariant_tilde_surjection_eq_top [IsMulCommutative V]
    (F : InvariantFlag T V 3) (hc : NaturalCoordinates F) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) (hne : ¬ IsMulCommutative F.U)
    (hZ : Nat.card (center F.U) = 4) (A : Subgroup (F.tilde F.U))
    (hA : ∀ h : F.H, (h : G) ∈ sourceComponent F →
      A.map ((F.localTildeAction F.H le_rfl) h).toMonoidHom = A)
    (hfull : A.map (F.tildeToUhat (by decide)) = ⊤) : A = ⊤ := by
  by_cases hd : Disjoint A (F.tildeToUhat (by decide)).ker
  · exact (no_invariant_complement F hc htwo hphi hne A hA hfull hd).elim
  have hn : A ⊓ (F.tildeToUhat (by decide)).ker ≠ ⊥ := by
    simpa only [disjoint_iff] using hd
  have hcard := (one_lt_card_iff_ne_bot _).mpr hn
  have he : A ⊓ (F.tildeToUhat (by decide)).ker = (F.tildeToUhat (by decide)).ker :=
    eq_of_le_of_card_ge inf_le_right (by
      rw [tildeToUhat_ker_card F hc hphi hZ]
      exact hcard)
  have hk : (F.tildeToUhat (by decide)).ker ≤ A := he ▸ inf_le_left
  have hh := congrArg (comap (F.tildeToUhat (by decide))) hfull
  rwa [comap_map_eq, comap_top, sup_eq_left.mpr hk] at hh

theorem NaturalCoordinates.invariant_tilde_image [IsMulCommutative V] (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) (A : Subgroup (F.tilde F.U))
    (hA : ∀ h : F.H, (h : G) ∈ sourceComponent F →
      A.map ((F.localTildeAction F.H le_rfl) h).toMonoidHom = A) :
    A.map (F.tildeToUhat (by decide)) = ⊥ ∨ A.map (F.tildeToUhat (by decide)) = ⊤ := by
  apply invariant_uhat_alternatives F hc
  intro h hh x hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨F.localTildeAction F.H le_rfl h a, ?_, F.tildeToUhat_equivariant (by decide) h a⟩
  rw [← hA h hh]
  exact mem_map_of_mem _ ha

theorem NaturalCoordinates.tildeIndecomposable [IsMulCommutative V]
    (F : InvariantFlag T V 3) (hc : NaturalCoordinates F) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) (hne : ¬ IsMulCommutative F.U)
    (hZ : Nat.card (center F.U) = 4) : TildeIndecomposable F (sourceComponent F) := by
  intro A B hA hB hcompl
  rcases NaturalCoordinates.invariant_tilde_image F hc A hA with hzero | hfull
  · have hb : B.map (F.tildeToUhat (by decide)) = ⊤ := by
      have hh := congrArg (map (F.tildeToUhat (by decide))) hcompl.sup_eq_top
      rwa [Subgroup.map_sup, hzero, bot_sup_eq, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (F.tildeToUhat_surjective (by decide))] at hh
    have htop := NaturalCoordinates.invariant_tilde_surjection_eq_top F hc htwo hphi hne hZ B hB hb
    left
    simpa only [htop, inf_top_eq] using hcompl.inf_eq_bot
  · have htop := NaturalCoordinates.invariant_tilde_surjection_eq_top F hc htwo hphi hne hZ A hA hfull
    right
    simpa only [htop, top_inf_eq] using hcompl.inf_eq_bot

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
