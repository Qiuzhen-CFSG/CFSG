module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Transport
public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The single symmetric-three alternative

For B.5.6(2), the nontrivial two-perfect subgroup X is the cubic residual
of the offender actor. The specified binary two-dimensional moved space
is its own commutator support. The Sylow Thompson image contributes an
even subgroup, while X contributes a cubic subgroup; together these
force the global Thompson image to be the whole actor. Taking its full
preimage proves the literal Thompson equality in 13.6.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(2), printed p.105, and 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G]

private theorem residual_eq_of_nontrivial_twoPerfect [Finite G]
    (H X : Subgroup G) (e : H ≃* Equiv.Perm (Fin 3))
    (hX : IsPPerfect 2 X) (hXH : X ≤ H) (hne : X ≠ ⊥) :
    (pResidual 2 H).map H.subtype = X := by
  have he := subgroupOfEquivOfLe hXH
  have hp : IsPPerfect 2 (X.subgroupOf H) :=
    hX.of_surjective he.symm.toMonoidHom he.symm.surjective
  have hle : X ≤ (pResidual 2 H).map H.subtype := by
    rw [← map_subgroupOf_eq_of_le hXH]
    exact map_mono (le_pResidual_of_isPPerfect _ hp)
  have hc := Theory.GroupTheory.NormalSymmetricThreeMarked.residual_card H e
  have hd : Nat.card X ∣ 3 := hc ▸ card_dvd_of_le hle
  have hxc : Nat.card X = 3 := (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left
    (fun h => hne (card_eq_one.mp h))
  exact (eq_of_le_of_card_ge hle (by rw [hc, hxc])).symm

private theorem moved_twice_of_split {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hsplit : subspaceCommutator ρ ⊤ ⊤ ⊔ ρ.invariants = ⊤) :
    subspaceCommutator ρ (subspaceCommutator ρ ⊤ ⊤) ⊤ = subspaceCommutator ρ ⊤ ⊤ := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨g, hg, w, _, rfl⟩
    exact ⟨g, hg, w, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, _, rfl⟩
    have hw : w ∈ subspaceCommutator ρ ⊤ ⊤ ⊔ ρ.invariants := by rw [hsplit]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    have hb' : ρ g b = b := hb g
    rw [map_add, hb', add_sub_add_right_eq_sub]
    exact Submodule.subset_span ⟨g, hg, a, ha, rfl⟩

theorem symmetricThree_residual_eq [Finite G] (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v)
    (c : ChapterB.SourceInduction.SymmetricThreeCase
      (FFFactors.offenderRepresentation (starRepresentation z v))) :
    (pResidual 2 (FFFactors.offenderActor (starRepresentation z v))).map
      (FFFactors.offenderActor (starRepresentation z v)).subtype = X :=
  residual_eq_of_nontrivial_twoPerfect _ X c.equiv
    (XFamily_isPPerfect L T z v hX) (XFamily_le_star_offender L T z v hz S hS hX)
    hX.1.2.2.1

theorem symmetricThree_support [Finite G] (z v : G)
    [IsElementaryAbelian 2 (Uv z v)]
    (c : ChapterB.SourceInduction.SymmetricThreeCase
      (FFFactors.offenderRepresentation (starRepresentation z v))) :
    let H := FFFactors.offenderActor (starRepresentation z v)
    factorSupport z v H H = movedSubgroup z v H ∧
      Nat.card (movedSubgroup z v H) = 4 := by
  dsimp only
  let H := FFFactors.offenderActor (starRepresentation z v)
  let ρ := starRepresentation z v
  let σ := FFFactors.offenderRepresentation ρ
  have ht : H.subgroupOf H = ⊤ := subgroupOf_self H
  have hm (W : Submodule (ZMod 2) (Additive (Uv z v))) :
      subspaceCommutator σ W ⊤ = subspaceCommutator ρ W H := by
    have hh := FFFactors.marked_commutator ρ H le_rfl W
    change subspaceCommutator σ W (H.subgroupOf H) = _ at hh
    rwa [ht] at hh
  have hsplit : subspaceCommutator σ ⊤ ⊤ ⊔ σ.invariants = ⊤ := c.decomposition.sup_eq_top
  have hd := moved_twice_of_split σ hsplit
  rw [hm, hm] at hd
  refine ⟨?_, ?_⟩
  · rw [← support_ambientSpace, hd, moved_ambientSpace]
  · rw [← moved_ambientSpace, ambientSpace_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← hm]
    change 2 ^ Module.finrank (ZMod 2) (ChapterB.QuasisimpleSource.moved σ ⊤) = 4
    rw [c.dimension]
    rfl

private theorem thompson_eq_of_between [Finite G] (N : Subgroup G)
    (hN : Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ N) :
    Stellmacher.elementaryAbelianMaxJ N = Stellmacher.elementaryAbelianMaxJ ⊤ := by
  obtain ⟨h₁, hJ₁⟩ := Stellmacher.elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le ⊤ N hN
  obtain ⟨h₂, hJ₂⟩ := Stellmacher.elementaryAbelianMaxOrder_le_and_j_le_of_eq N ⊤ le_top
  exact le_antisymm (hJ₂ (le_antisymm h₂ h₁)) (hJ₁ (le_antisymm h₁ h₂))

private theorem thompson_preimage_eq [Finite G] (z v : G)
    (H : Subgroup (Gstar z v)) (hH : JGstar z v = H) :
    starImage z v (Stellmacher.elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  have he : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map
      (starMk z v) = JGstar z v :=
    starImage_intrinsic_thompson z v ⊤ (Gv v)
      (by rw [← MonoidHom.range_eq_map, range_subtype])
  have hle : Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Gv v)) ≤ H.comap (starMk z v) :=
    map_le_iff_le_comap.mp ((he.trans hH).le)
  rw [← starImage_intrinsic_thompson z v (H.comap (starMk z v)) (starPreimage z v H) rfl,
    thompson_eq_of_between _ hle, he, hH]

theorem symmetricThree_thompson_eq [Finite G] (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v)
    (c : ChapterB.SourceInduction.SymmetricThreeCase
      (FFFactors.offenderRepresentation (starRepresentation z v))) :
    let H := FFFactors.offenderActor (starRepresentation z v)
    starImage z v (Stellmacher.elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  dsimp only
  let H := FFFactors.offenderActor (starRepresentation z v)
  let A := starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))
  let J := JGstar z v
  let : J.Normal := JGstar_normal z v
  have hAH : A ≤ H := thompson_le_star_offender T z v hz S hS
  have hAJ : A ≤ J := by
    change A ≤ JGstar z v
    rw [JGstar_eq_conjugateSpan T z v ⟨S, hS⟩]
    exact le_conjugateSpanBy A ⊤
  have hJH : J ≤ H := by
    change JGstar z v ≤ H
    rw [JGstar_eq_conjugateSpan T z v ⟨S, hS⟩]
    exact conjugateSpanBy_le hAH (by rw [normalizer_eq_top])
  have hXJ : X ≤ J := X0_le_normal_of_thompson_le L T z v hX.1 J hAJ
  have hAc : IsPGroup 2 A := by
    have he := starImage_intrinsic_thompson z v (S : Subgroup (Gv v)) (Tv T v) hS
    change IsPGroup 2 (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    rw [← he]
    exact (S.isPGroup'.to_le (sSup_le fun _ h => h.1)).map (starMk z v)
  have hAne : A ≠ ⊥ := by
    intro hb
    have hh := hX.1.2.2.2
    change ⁅X, A⁆ = X at hh
    rw [hb, commutator_bot_right] at hh
    exact hX.1.2.2.1 hh.symm
  have htwo : 2 ∣ Nat.card J :=
    (hAc.card_eq_or_dvd.resolve_left (fun h => hAne (card_eq_one.mp h))).trans (card_dvd_of_le hAJ)
  have hxc : Nat.card X = 3 := by
    rw [← symmetricThree_residual_eq L T z v hz S hS hX c]
    exact Theory.GroupTheory.NormalSymmetricThreeMarked.residual_card H c.equiv
  have hthree : 3 ∣ Nat.card J := hxc ▸ card_dvd_of_le hXJ
  have hc : Nat.card H = 6 := by
    rw [Nat.card_congr c.equiv.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcard : Nat.card J = Nat.card H := by
    apply Nat.dvd_antisymm (card_dvd_of_le hJH)
    rw [hc]
    exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  exact thompson_preimage_eq z v H (eq_of_le_of_card_ge hJH hcard.ge)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
end
