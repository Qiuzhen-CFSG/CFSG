module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Fixed
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.OppositeComponent

/-!
# Faithful coordinates on the original moved three-space

The opposite component centralizes V₁. Thus the kernel C_{V₁}(L) of the
given natural coordinates is fixed by both components, and is trivial when
C_V(L₀) = 1. The original section coordinates are consequently an actual
group isomorphism on V₁, with its original equivariance unchanged. In
particular the specified nonidentity vector a has nonzero coordinates.

Source: Aschbacher--Smith 10.1.1(3) and 10.2.11, printed pp.741,753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- The literal natural section has zero kernel in the diagonal configuration. -/
theorem natural_kernel_eq_bot (c : Configuration s a b) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  have hcross : ⁅D.fullModule,L⁆ ≤
      centralizer (L.map (MulAut.conj s.exchange).toMonoidHom : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D s.exchange_mem s.exchange_moves s.crossed)
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
        (survivor_nonnormal s)) inf_le_right s.exchange_mem s.exchange_moves
  have hC : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) ≤
      centralizer (localOrbit T L : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hpair]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hcross))
  exact bot_unique ((le_inf (inf_le_left.trans (survivor_moved_le s)) hC).trans_eq c.fixed)

/-- The supplied coordinates identify the entire original moved factor. -/
theorem natural_coordinates_bijective (c : Configuration s a b) :
    Function.Bijective s.natural.coordinates := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, s.natural.onto⟩
  rw [s.natural.kernel_eq, natural_kernel_eq_bot c, bot_subgroupOf]

/-- The given nonidentity first vector is nonzero in the literal natural action. -/
theorem first_coordinates_ne_one (c : Configuration s a b) :
    s.natural.coordinates ⟨a,c.first_mem⟩ ≠ 1 := by
  intro he
  have ha := (s.natural.coordinates_eq_one_iff ⟨a,c.first_mem⟩).mp he
  rw [natural_kernel_eq_bot c] at ha
  exact c.first_ne (mem_bot.mp ha)

/-- The original first moved factor has order eight, without a quotient-kernel premise. -/
theorem moved_card (c : Configuration s a b) : Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := by
  have he := s.natural.card_section
  rw [natural_kernel_eq_bot c, card_bot] at he
  norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at he ⊢
  exact he

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
