module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Inputs

/-!
# The exchanged centers in the original diagonal centralizer

The Sylow exchanger swaps the disjoint moved factors and fixes their product.
Uniqueness of coordinates in the product therefore makes it carry a to b.
Central-core containment and the TI normalizer bound show that V_z normalizes
the moved factor. Its displacement then lies in the fixed line whenever the
separate natural-module calculation identifies that fixed subgroup.

Source: Aschbacher--Smith 10.2.11(3), printed p.754.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}
namespace Configuration
variable (c : Configuration s a b)
include c

theorem exchange_first : (MulAut.conj s.exchange) a = b := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let e := MulAut.conj s.exchange
  have hd : Disjoint A B := survivor_pair_disjoint s c.fixed
  have he : B.map e.toMonoidHom = A := by
    have hcomp : e.toMonoidHom.comp e.toMonoidHom =
        (MulAut.conj (s.exchange*s.exchange)).toMonoidHom := by
      ext x
      simp [e, MulAut.conj_apply, mul_assoc]
    have hpair := survivor_moved_pair s (s.exchange*s.exchange)
      (le_normalizer_componentOrbit L T ((T : Subgroup G).mul_mem s.exchange_mem s.exchange_mem))
    have hBB : B.map e.toMonoidHom = A.map
        (MulAut.conj (s.exchange*s.exchange)).toMonoidHom := by
      change (A.map e.toMonoidHom).map e.toMonoidHom = _
      rw [map_map,hcomp]
    rw [hBB]
    rcases hpair with h | h
    · exact h
    · have hh : B.map e.toMonoidHom = A.map e.toMonoidHom := by
        rw [hBB]
        exact h
      have hBA := map_injective e.injective hh
      have ha : a ∈ A ⊓ B := ⟨c.first_mem,hBA.symm ▸ c.first_mem⟩
      exact (c.first_ne (mem_bot.mp (hd.eq_bot ▸ ha))).elim
  have haB : e a ∈ B := mem_map_of_mem e.toMonoidHom c.first_mem
  have hbA : e b ∈ A := he ▸ mem_map_of_mem e.toMonoidHom c.second_mem
  have hprod : e b * e a = a*b := by
    have hz : e (a*b) = a*b := by
      change s.exchange*(a*b)*s.exchange⁻¹=a*b
      rw [c.central.2 s.exchange s.exchange_mem,mul_inv_cancel_right]
    rw [map_mul] at hz
    have hab : Commute a b := by
      let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
      exact congrArg Subtype.val (mul_comm
        (⟨a,survivor_moved_le s c.first_mem⟩ : D.fullModule)
        ⟨b,survivor_partner_le s c.second_mem⟩)
    exact (hab.map e.toMonoidHom).eq.symm.trans hz
  have hh : ((⟨e b,hbA⟩ : A),(⟨e a,haB⟩ : B)) =
      (⟨a,c.first_mem⟩,⟨b,c.second_mem⟩) := mul_injective_of_disjoint hd hprod
  exact congrArg (fun p : A × B => (p.2:G)) hh

theorem span_normalizes_moved
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2)) :
    centralizerModule a b ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hab : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left))
  exact (le_inf c.span_le hab).trans (c.kernel_le_moved_normalizer.trans inf_le_right)

theorem moved_displacement_le_line
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2))
    (hfix : ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a) :
    ⁅⁅D.fullModule,L⁆,centralizerModule a b⁆ ≤ zpowers a := by
  have hab : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left))
  have hAW : ⁅D.fullModule,L⁆ ≤ normalizer (centralizerModule a b : Set G) :=
    ((survivor_moved_le s).trans c.full_le).trans (le_normalizer_conjugateSpanBy _ _)
  rw [← hfix]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp (c.span_normalizes_moved hc))
    ((le_normalizer_iff_commutator_le_right.mp hAW).trans hab)

end Configuration
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
