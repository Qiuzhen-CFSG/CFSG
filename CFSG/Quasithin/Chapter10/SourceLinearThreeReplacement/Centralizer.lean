module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts

/-!
# The literal subgroups of the central involution centralizer

The central involution puts T and K_zT inside G_z and witnesses a
nontrivial two-core of K_zT. The given full-module core containment
puts E and its G_z-conjugate span V_z in the same centralizer.
Source: Aschbacher--Smith 10.2.11 and §10.3, printed pp.753--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

omit [Finite G] in
/-- The literal conjugate span K_z remains inside G_z. -/
theorem componentSpan_le_centralizer (z : G) :
    componentSpan T L z ≤ centralizer ({z} : Set G) :=
  conjugateSpanBy_le_self ((map_subtype_le _).trans inf_le_right)

theorem CentralizerData.sylow_le_centralizer (d : CentralizerData T D s) :
    (T : Subgroup G) ≤ centralizer ({d.first * d.second} : Set G) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (d.central.2 t ht)

theorem CentralizerData.join_le_centralizer (d : CentralizerData T D s) :
    componentJoin T L (d.first * d.second) ≤
      centralizer ({d.first * d.second} : Set G) :=
  sup_le (componentSpan_le_centralizer _) d.sylow_le_centralizer

/-- The chosen central involution witnesses a nontrivial two-core in the
literal K_zT, so component extraction really lands in L(G,T). -/
theorem CentralizerData.join_core_ne_bot (d : CentralizerData T D s) :
    (componentJoin T L (d.first * d.second)).pCoreIn 2 ≠ ⊥ := by
  let z := d.first * d.second
  let J := componentJoin T L z
  let Q := zpowers z
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    simpa only [Q, Nat.card_zpowers, pow_one] using d.order)
  have hQJ : Q ≤ J := zpowers_le.mpr (mem_sup_right d.central.1)
  have hJQ : J ≤ centralizer (Q : Set G) := by
    simpa only [Q, zpowers_eq_closure, centralizer_closure] using d.join_le_centralizer
  have hcore := le_pCoreIn_of_normalizes hQ hQJ
    (hJQ.trans (Subgroup.centralizer_le_normalizer _))
  intro hz
  have hQbot : Q = ⊥ := bot_unique (hcore.trans_eq hz)
  have hzone : z = 1 := mem_bot.mp (hQbot ▸ mem_zpowers z)
  have ho := d.order
  change orderOf z = 2 at ho
  simp [hzone] at ho

theorem CentralizerData.module_le_centralizer (d : CentralizerData T D s) :
    centralizerModule d.first d.second ≤ centralizer ({d.first * d.second} : Set G) := by
  apply conjugateSpanBy_le_self
  have hVC : D.fullModule ≤ centralizer ({d.first * d.second} : Set G) :=
    d.full_core.trans (map_subtype_le _)
  have hf : d.first ∈ D.fullModule := by
    rw [s.generated]
    exact mem_sup_left d.first_mem
  have hs : d.second ∈ D.fullModule := by
    rw [s.generated]
    exact mem_sup_right d.second_mem
  exact sup_le (zpowers_le.mpr (hVC hf)) (zpowers_le.mpr (hVC hs))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
