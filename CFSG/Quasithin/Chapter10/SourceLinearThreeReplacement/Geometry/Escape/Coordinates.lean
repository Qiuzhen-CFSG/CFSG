module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Pair

/-!
# The original natural factors and their exact orders

Conjugating the separate-factor centralization back by the exchange shows
that the first moved factor centralizes the other component. Consequently
its component-fixed subgroup lies in the full fixed part. When this is zero,
the survivor's actual SL₃(2)-equivariant coordinates have trivial kernel and
identify the first factor with the natural binary three-space. The exchanged
factor also has order eight; disjointness makes their product have order 64.

These are the literal factors, coordinates and cardinalities used by the
fusion and offender arguments of Aschbacher--Smith 10.3.2, printed p.756.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)

include s

/-- The specified exchange gives the literal two-component orbit. -/
theorem orbit_eq_pair :
    localOrbit T L = L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro t
    rcases source_nonnormal_maximal_pair D (survivor_nonnormal s)
      s.exchange_mem s.exchange_moves t (le_normalizer_componentOrbit L T t.property)
      with h | h
    · exact h.le.trans le_sup_left
    · exact h.le.trans le_sup_right
  · refine sup_le (le_componentOrbit L T) ?_
    exact le_iSup (fun t : (T : Subgroup G) =>
      L.map (MulAut.conj (t : G)).toMonoidHom) ⟨s.exchange,s.exchange_mem⟩

/-- The first moved factor centralizes the exchanged component. -/
theorem moved_centralizes_partner_component :
    ⁅D.fullModule,L⁆ ≤ centralizer
      (L.map (MulAut.conj s.exchange).toMonoidHom : Set G) := by
  have hback : L.map (MulAut.conj s.exchange⁻¹).toMonoidHom =
      L.map (MulAut.conj s.exchange).toMonoidHom := by
    rcases source_nonnormal_maximal_pair D (survivor_nonnormal s)
      s.exchange_mem s.exchange_moves s.exchange⁻¹
      (le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem s.exchange_mem))
      with h | h
    · exact (s.exchange_moves (by simpa only [inv_inv] using
        (normalizer (L : Set G)).inv_mem (mem_normalizer_iff_map_conj_eq.mpr h))).elim
    · exact h
  intro a ha
  rw [← hback]
  rintro _ ⟨l,hl,rfl⟩
  have hh := congrArg (MulAut.conj s.exchange⁻¹)
    (s.crossed (mem_map_of_mem (MulAut.conj s.exchange).toMonoidHom ha) l hl)
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- The section denominator vanishes with the full fixed part. -/
theorem moved_fixed_eq_bot
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro x hx
  apply hz.le
  refine ⟨survivor_moved_le s hx.1,?_⟩
  rw [orbit_eq_pair s]
  exact le_centralizer_iff.mpr (sup_le
    (le_centralizer_iff.mp (zpowers_le.mpr hx.2))
    (le_centralizer_iff.mp (zpowers_le.mpr (moved_centralizes_partner_component s hx.1))))
      (mem_zpowers x)

/-- The survivor coordinates identify the original moved factor with the natural space. -/
def movedCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ↥(⁅D.fullModule,L⁆ : Subgroup G) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  MulEquiv.ofBijective s.natural.coordinates ⟨(MonoidHom.ker_eq_bot_iff _).mp
    (by rw [s.natural.kernel_eq, moved_fixed_eq_bot s hz, bot_subgroupOf]),s.natural.onto⟩

/-- The original natural moved factor has order eight. -/
theorem moved_card
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := by
  have hc := s.natural.card_section
  rw [moved_fixed_eq_bot s hz, card_bot] at hc
  norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc ⊢
  exact hc

/-- Both exchanged factors contribute: the full module has order sixty-four. -/
theorem full_card
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card D.fullModule = 64 := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hc : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm
      (⟨b,survivor_partner_le s hb⟩ : D.fullModule) ⟨a,survivor_moved_le s ha⟩)
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B
    (survivor_pair_disjoint s hz) hc
  have hB : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj s.exchange).injective
  have hV : Nat.card D.fullModule = Nat.card A * Nat.card B := by
    rw [s.generated]
    exact (Nat.card_congr e.toEquiv).symm.trans (Nat.card_prod A B)
  rw [hV, hB, show Nat.card A = 8 from moved_card s hz]

/-- The maximal local group also permutes the exchanged moved factor. -/
theorem partner_pair (g : G) (hg : g ∈ D.maximalLocal) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj s.exchange).toMonoidHom =
      (MulAut.conj (g * s.exchange)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, he]
  exact survivor_moved_pair s _
    (D.maximalLocal.mul_mem hg (le_normalizer_componentOrbit L T s.exchange_mem))

/-- The equivalence uses the survivor's specified coordinates without changing the action. -/
theorem movedCoordinates_apply
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : ↥(⁅D.fullModule,L⁆ : Subgroup G)) :
    movedCoordinates s hz a = s.natural.coordinates a := rfl

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
