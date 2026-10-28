module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.RankOne.Projection
public import Theory.SpecificGroups.SL2.OddFixedVectors

/-!
# The common pair lies inside the original component

A nontrivial odd Cartan actor fixes only the identity on each natural SL₂
summand of P. Its displacement map is therefore bijective on the elementary
pair. All these commutators lie in L, since P lies in T and T normalizes L.
The source application obtains the actor from the original Hall subgroup;
it assumes no compatibility between the coefficient fields of P and V.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
first three paragraphs. The exceptional model calculation uses I.2.2(3b).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {V H : Subgroup G} {h : G} {F : BinaryField}

omit [Finite G] in
theorem PairNaturalMarking.odd_actor_fixed (c : PairNaturalMarking V H h F)
    (d : outsideResidual H) (m : ℕ) (hm : Odd m) (hd : d ^ m = 1)
    (hne : QuotientGroup.mk' (pCore 2 (outsideResidual H)) d ≠ 1)
    (v : pairCore V H h) (hfix : pairResidualAction V H h c.normalizes d v = v) :
    v = 1 := by
  let a := c.quotientEquiv (QuotientGroup.mk' _ d)
  have ha : a ^ m = 1 := by
    rw [←map_pow,←map_pow,hd,map_one,map_one]
  have ha1 : a ≠ 1 := fun he => hne (c.quotientEquiv.map_eq_one_iff.mp he)
  apply c.coordinates.injective
  rw [map_one]
  change (c.coordinates v).toAdd = 0
  funext i
  have he := c.intertwines d v i
  rw [hfix] at he
  exact Matrix.SL2.odd_power_fixed_eq_zero a m hm ha ha1 _ he.symm

/-- An odd actor in L with nontrivial residual image puts the entire actual P in L. -/
theorem PairNaturalMarking.le_of_odd_actor (c : PairNaturalMarking V H h F)
    [IsMulCommutative (pairCore V H h)] (L : Subgroup G)
    (hn : pairCore V H h ≤ normalizer (L : Set G))
    (d : outsideResidual H) (hdL : (d : G) ∈ L)
    (m : ℕ) (hm : Odd m) (hd : d ^ m = 1)
    (hne : QuotientGroup.mk' (pCore 2 (outsideResidual H)) d ≠ 1) :
    pairCore V H h ≤ L := by
  let α := pairResidualAction V H h c.normalizes d
  let δ : pairCore V H h →* pairCore V H h := {
    toFun v := α v * v⁻¹
    map_one' := by simp
    map_mul' v w := by simp only [map_mul,_root_.mul_inv_rev]; ac_rfl }
  have hi : Function.Injective δ := by
    apply (MonoidHom.ker_eq_bot_iff δ).mp
    apply bot_unique
    intro v hv
    have he : α v = v := mul_inv_eq_one.mp hv
    exact c.odd_actor_fixed d m hm hd hne v he
  have hs : Function.Surjective δ := Finite.surjective_of_injective hi
  intro v hv
  obtain ⟨w,hw⟩ := hs ⟨v,hv⟩
  have hmemb : (δ w : G) ∈ L := by
    change (d : G) * (w : G) * (d : G)⁻¹ * (w : G)⁻¹ ∈ L
    simpa only [mul_assoc] using L.mul_mem hdL
      ((mem_normalizer_iff.mp (hn w.property) _).mp (L.inv_mem hdL))
  have he : (δ w : G) = v := congrArg (fun x : pairCore V H h => (x : G)) hw
  rwa [he] at hmemb

variable {T : Sylow 2 G} {L : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

theorem source_pairCore_le_component
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (c : PairNaturalMarking V H h S.field)
    (cK : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) : pairCore V H h ≤ L := by
  let := pairCore_elementary s hh hz
  have hPT : pairCore V H h ≤ (T : Subgroup G) := by
    have hcore := pCoreIn_le_sylow H (T.subtype s.outside.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hcore
    rw [map_subgroupOf_eq_of_le s.outside.1.1.2] at hcore
    exact (pairCore_le_core hh).trans hcore
  obtain ⟨d,hd,b,a,ha,hdiag⟩ := Hall.source_conjugate_diagonal s cK A hA hHall
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have hdA : (d : G) ∈ A := oddCartanPart_le A hd
  have hdp : d ^ Nat.card A = 1 := by
    apply Subtype.ext
    exact congrArg (fun x : A => (x : G)) (pow_card_eq_one' (x := (⟨d,hdA⟩ : A)))
  have hne : QuotientGroup.mk' (pCore 2 (outsideResidual H)) d ≠ 1 := by
    intro he
    rw [he,map_one,mul_one,mul_inv_cancel] at hdiag
    have h00 := congrArg (fun z : Matrix (Fin 2) (Fin 2) S.field.Carrier => z 0 0) hdiag
    exact ha (by simpa using h00.symm)
  exact c.le_of_odd_actor L (hPT.trans D.sylow_normalizes_component) d (hAL hd)
    (Nat.card A) ho hdp hne


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
