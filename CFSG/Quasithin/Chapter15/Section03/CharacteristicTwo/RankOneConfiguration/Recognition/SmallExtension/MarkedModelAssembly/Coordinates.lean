module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.Marking
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The original plane in whole-center coordinates

An equivariant identification of the entire center sends an ambient subgroup
into a binary subspace without taking a further central quotient. Its cardinality,
normalizer and fixed vectors retain their literal ambient meanings. These facts
will supply the natural embedding of V₂ in the linear cases of C.1.34.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly
open CentralCover CentralCover.LinearModels
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {L : Subgroup G} {ρ : Representation (ZMod 2) A V}

noncomputable def centerPlane (m : FullCenter L ρ) (E : Subgroup G) :
    Submodule (ZMod 2) V :=
  AddSubgroup.toZModSubmodule 2
    (((E.subgroupOf (coreCenter L)).comap m.equiv.symm.toMonoidHom).toAddSubgroup')

theorem mem_centerPlane (m : FullCenter L ρ) (E : Subgroup G) (v : V) :
    v ∈ centerPlane m E ↔ (m.equiv.symm (Multiplicative.ofAdd v) : G) ∈ E := Iff.rfl

theorem coord_mem_centerPlane (m : FullCenter L ρ) (E : Subgroup G)
    (z : coreCenter L) : (m.equiv z).toAdd ∈ centerPlane m E ↔ (z : G) ∈ E := by
  change (m.equiv.symm (m.equiv z) : G) ∈ E ↔ (z : G) ∈ E
  rw [m.equiv.symm_apply_apply]

theorem centerPlane_card (m : FullCenter L ρ) {E : Subgroup G}
    (hE : E ≤ coreCenter L) : Nat.card (centerPlane m E) = Nat.card E := by
  let e : centerPlane m E ≃ E := {
    toFun v := ⟨m.equiv.symm (Multiplicative.ofAdd v.val), v.property⟩
    invFun z := ⟨(m.equiv ⟨z, hE z.property⟩).toAdd,
      (coord_mem_centerPlane m E _).mpr z.property⟩
    left_inv v := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (m.equiv.apply_symm_apply (Multiplicative.ofAdd v.val))
    right_inv z := by
      apply Subtype.ext
      exact congrArg (fun x : coreCenter L => (x : G))
        (m.equiv.symm_apply_apply ⟨z, hE z.property⟩) }
  exact Nat.card_congr e

theorem centerPlane_normalizer (m : FullCenter L ρ) (E : Subgroup G)
    (hE : E ≤ coreCenter L) (l : L) :
    m.actor l ∈ subspaceStabilizer ρ (centerPlane m E) ↔
      (l : G) ∈ normalizer (E : Set G) := by
  have hc (z : coreCenter L) :
      ρ (m.actor l) (m.equiv z).toAdd =
        (m.equiv (centerConjugate L l z)).toAdd :=
    (congrArg Multiplicative.toAdd (m.action l z)).symm
  constructor
  · intro hl
    apply mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      have hh := (hl (m.equiv ⟨z, hE hz⟩).toAdd).mpr
        ((coord_mem_centerPlane m E _).mpr hz)
      rwa [hc, coord_mem_centerPlane] at hh
    · intro hz
      have hzC : z ∈ coreCenter L :=
        ((mem_normalizer_iff.mp (normalizes_coreCenter L l.property)) z).mpr (hE hz)
      have hh := (hl (m.equiv ⟨z, hzC⟩).toAdd).mp
        (by rw [hc, coord_mem_centerPlane]; exact hz)
      exact (coord_mem_centerPlane m E _).mp hh
  · intro hl v
    obtain ⟨z, rfl⟩ := m.equiv.surjective (Multiplicative.ofAdd v)
    change ρ (m.actor l) (m.equiv z).toAdd ∈ centerPlane m E ↔
      (m.equiv z).toAdd ∈ centerPlane m E
    rw [hc, coord_mem_centerPlane, coord_mem_centerPlane]
    exact ((mem_normalizer_iff.mp hl) z).symm

theorem centerPlane_stabilizer (m : FullCenter L ρ) (E : Subgroup G)
    (hE : E ≤ coreCenter L) :
    ((normalizer (E : Set G)).subgroupOf L).map m.actor =
      subspaceStabilizer ρ (centerPlane m E) := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (centerPlane_normalizer m E hE l).mpr hl
  · intro ha
    obtain ⟨l, rfl⟩ := m.actor_surjective a
    exact ⟨l, (centerPlane_normalizer m E hE l).mp ha, rfl⟩

theorem centerPlane_fixed_disjoint (m : FullCenter L ρ) (E Y P : Subgroup G)
    (hYP : Y ≤ P) (hYL : Y ≤ L)
    (hfix : E ⊓ centralizer (Y : Set G) = ⊥) :
    Disjoint (centerPlane m E) (fixedSpace ρ ((P.subgroupOf L).map m.actor)) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hfixed
  let z := m.equiv.symm (Multiplicative.ofAdd v)
  have hzE : (z : G) ∈ E := hv
  have hzC : (z : G) ∈ centralizer (Y : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    let l : L := ⟨y, hYL hy⟩
    have hh := hfixed ⟨m.actor l, mem_map_of_mem _ (hYP hy)⟩
    change ρ (m.actor l) v = v at hh
    have he : centerConjugate L l z = z := by
      apply m.equiv.injective
      rw [m.action]
      change Multiplicative.ofAdd (ρ (m.actor l) (m.equiv (m.equiv.symm _)).toAdd) = _
      rw [m.equiv.apply_symm_apply]
      exact congrArg Multiplicative.ofAdd hh
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  have hz : z = 1 := Subtype.ext (mem_bot.mp (hfix ▸ And.intro hzE hzC))
  have he := congrArg (fun z => (m.equiv z).toAdd) hz
  simpa only [z, m.equiv.apply_symm_apply, map_one, toAdd_ofAdd, toAdd_one] using he

theorem plane_dimension {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (E : Submodule (ZMod 2) W) [Finite E] (hE : Nat.card E = 4) :
    Module.finrank (ZMod 2) E = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
  rw [hE, Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h.symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly

end
