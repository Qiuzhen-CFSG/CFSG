module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.SylowQuotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Geometry
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The original Sylow and Hall subgroup in odd degree

The binary normalizer of the marked natural SL₃ has odd index over SL₃
in odd field degree. Its existing source transport gives T=T_L on the
original chosen module. The cohomology calculation then puts that T in L.
The source odd Hall group has order dividing q-1, which is prime to three
in odd degree, so its O³ extraction is the entire group.

The cubic obstruction must still establish odd degree. No parity premise
is added to OrthogonalInput. Final assembly belongs to the common-core
orthogonal argument on printed p.774 of Aschbacher--Smith.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)

include d

/-- The actual Hall extraction is all of A once the cubic branch is excluded. -/
theorem source_oddCartanPart_eq (hodd : Odd S.field.degree) : oddCartanPart A = A := by
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv]
    exact OddHall.odd_hall_odd d.hall
  have hd := Hall.source_card_dvd d.source d.closure_natural A d.hall_le ho
  have hmod : 2 ^ S.field.degree % 3 = 2 := by
    obtain ⟨k,hk⟩ := hodd
    rw [hk]
    simp [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  have hnt : ¬ 3 ∣ 2 ^ S.field.degree - 1 := by
    have hp := pow_pos (by decide : 0 < (2 : ℕ)) S.field.degree
    omega
  have hcop : Nat.Coprime 3 (Nat.card A) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (fun hh => hnt (hh.trans hd))
  have hr : pResidual 3 A = ⊤ := by
    apply top_unique
    intro a _
    exact mem_pResidual_of_orderOf_coprime
      (hcop.of_dvd_right (_root_.orderOf_dvd_natCard a))
  rw [oddCartanPart,hr,top_sup_eq,← MonoidHom.range_eq_map,range_subtype]

/-- Odd-degree natural normalization, followed by the corrected cohomology identity. -/
theorem source_sylow_of_odd (hodd : Odd S.field.degree) :
    sourceTL T L = (T : Subgroup G) ∧ (T : Subgroup G) ≤ L ∧
      ∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G) := by
  have hTL := Closure.Linear.Outside.TorusSylow.sylow_eq_sourceTL D S m hodd
  exact ⟨hTL.symm,
    sylow_le_component D S m d.seed_core d.omega_fixed hTL.symm,
    sylow_placement D S m d.seed_core d.omega_fixed hTL.symm⟩

/-- The quotient calculation now requires only the remaining parity conclusion. -/
theorem source_sylow_quotient_of_odd (hodd : Odd S.field.degree) :
    let := source_pairCore_normal_sylow d
    IsElementaryAbelian 2 ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) ∧
      Nat.card ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) =
        (2 ^ S.field.degree) ^ 2 :=
  source_sylow_quotient d (source_sylow_of_odd d hodd).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
