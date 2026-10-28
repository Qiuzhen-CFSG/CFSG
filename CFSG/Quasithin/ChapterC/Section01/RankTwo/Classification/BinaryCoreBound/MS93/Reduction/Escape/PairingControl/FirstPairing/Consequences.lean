module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Consequences of actual opposite coordinates

Opposite coordinates force [Vcirc,Q] into U because Q is the kernel of the
acting quotient. This is a normal subgroup of the irreducible natural U.
Step (1)'s noncontainment in D excludes the trivial subgroup, giving H=U.
The intrinsic quotient and subgroup coordinates both have order eight,
so the actual group Vcirc has order 64.

The construction of opposite coordinates and the two moving-edge assertions
remain separate mathematical obligations. No later escape result is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3), printed p.884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
open RankOnePairing

private theorem dual_commutator_le {A : Type*} [Group A]
    {π : A →* SL} {J N Z W : Subgroup A}
    {z : NaturalFactor π ⊤ Z ⊥} (d : DualFactor π ⊤ J N Z z)
    (hW : W ≤ π.ker) : ⁅J, W⁆ ≤ N := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro w hw x hx
  let u : J := ⟨x, hx⟩
  let v : J := ⟨w * x * w⁻¹, le_normalizer_iff.mp d.normalized w (mem_top w) x hx⟩
  have he : d.coordinates v = d.coordinates u := by
    have h := d.action w (mem_top w) u v rfl
    have hp : π w = 1 := hW hw
    simpa only [hp, map_one, inv_one, Matrix.SpecialLinearGroup.coe_one,
      Matrix.transpose_one, Matrix.one_mulVec, ofAdd_toAdd]
      using congrArg Multiplicative.ofAdd h
  have hk : v * u⁻¹ ∈ d.coordinates.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  rw [d.kernel] at hk
  exact hk

variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (H R a).map (MulAut.conj g).toMonoidHom = H R a
  have h := H_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

private theorem Vcirc_le_local [Finite M] (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : Vcirc R a ≤ stabilizer R a :=
  (le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))).trans
    ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1))

private theorem U_le_Vcirc (a : Vertex R) : U R a ≤ Vcirc R a :=
  commutator_mono (Z_le_VBall R a 2) le_rfl

/-- The quotient action, rather than a dimension label, bounds H by U. -/
theorem H_le_U_of_opposite [Finite M] (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (o : OppositeSectionAt a) :
    H R a ≤ U R a := by
  have h := dual_commutator_le o.dual (W := (Q R a).subgroupOf (stabilizer R a))
    o.kernel.ge
  have hm := map_mono (f := (stabilizer R a).subtype) h
  rw [map_commutator,
    map_subgroupOf_eq_of_le (Vcirc_le_local hb a ha),
    map_subgroupOf_eq_of_le (show Q R a ≤ stabilizer R a from fun _ hx => hx.1),
    map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer R a))] at hm
  exact hm

/-- The nonzero irreducible alternative gives the source equality H=U. -/
theorem H_eq_U_of_opposite [Finite M] (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) (o : OppositeSectionAt p.a) :
    H R p.a = U R p.a := by
  have hHU := H_le_U_of_opposite hb p.a p.color_a o
  have hUG := (U_le_Z p.a).trans (Z_le_stabilizer R p.a)
  have hHG := hHU.trans hUG
  let : ((H R p.a).subgroupOf (stabilizer R p.a)).Normal :=
    normal_subgroupOf_of_le_normalizer (H_normalized p.a)
  have him : (⊤ : Subgroup (stabilizer R p.a)).map o.projection = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr o.surjective
  rcases o.naturalU.irreducible him ((H R p.a).subgroupOf (stabilizer R p.a))
    (fun _ hx => hHU hx) le_normalizer_of_normal with he | he
  · exfalso
    apply H_not_le_fixed transfer bad
    intro x hx
    have hh : (⟨x, hHG hx⟩ : stabilizer R p.a) ∈
        (H R p.a).subgroupOf (stabilizer R p.a) := hx
    rw [he] at hh
    have hxone : x = 1 := congrArg Subtype.val (mem_bot.mp hh)
    simpa only [hxone] using (fixedCore R p.a).one_mem
  · have hh := congrArg (Subgroup.map (stabilizer R p.a).subtype) he
    simpa only [map_subgroupOf_eq_of_le hHG, map_subgroupOf_eq_of_le hUG] using hh

/-- The actual natural subgroup and dual quotient each have order eight. -/
theorem moving_card_of_opposite [Finite M] (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (o : OppositeSectionAt a) :
    Nat.card (Vcirc R a) = 64 := by
  let J := (Vcirc R a).subgroupOf (stabilizer R a)
  let N := (U R a).subgroupOf (stabilizer R a)
  have hNJ : N ≤ J := fun _ hx => U_le_Vcirc a hx
  let := o.dual.kernel_normal
  have hN : Nat.card N = 8 := by
    rw [Nat.card_congr o.naturalU.equivOfBot.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hquot : Nat.card (J ⧸ N.subgroupOf J) = 8 := by
    rw [Nat.card_congr o.dual.quotientEquiv.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hJ := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf J)
  rw [hquot, Nat.card_congr (subgroupOfEquivOfLe hNJ).toEquiv, hN] at hJ
  rw [← Nat.card_congr (subgroupOfEquivOfLe (Vcirc_le_local hb a ha)).toEquiv]
  exact hJ

/-- A local opposite-section theorem automatically holds at every M-vertex.
The producer is still required to construct the coordinates from its inputs. -/
theorem opposite_everywhere (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (produce : ∀ q : Counterexample geometry,
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a → Nonempty (OppositeSectionAt q.a)) :
    ∀ a, color R a = false → Nonempty (OppositeSectionAt a) := by
  intro a ha
  obtain ⟨q, hqa, hbad⟩ := contrary_at p bad a ha
  exact hqa ▸ produce q hbad

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
