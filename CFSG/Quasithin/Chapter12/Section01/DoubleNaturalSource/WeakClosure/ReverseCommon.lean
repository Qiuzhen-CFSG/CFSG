module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.SmallFixed
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry.FirstStage

/-!
# Rank and reverse-action transports for the doubled orbit

Binary rank additivity and fixed-space cardinalities identify the literal
relative centralizers with their linear dimensions. Ambient conjugation
transports the small-fixed-codimension bound to the actual conjugate module,
so an elementary reverse actor fixing corank at most two has image rank
at most one. These identities support both degree-four branches of 12.1.8.
Source: Aschbacher--Smith, E.3.28 and 12.1.8, pp.237,792--793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

theorem rank_add_corank {A : Subgroup G} (hA : A ≤ W) :
    rank A + subgroupCorank W A = rank W := by
  have hh := offender_corank_add (bot_le : (⊥ : Subgroup G) ≤ A) hA
  simpa only [subgroupCorank, Subgroup.relIndex_bot_left, rank, add_comm] using hh.symm

theorem rank_subgroupSpace {A : Subgroup G} :
    rank (W ⊓ A) = Module.finrank (ZMod 2) (subgroupSpace W A) := by
  let e : subgroupSpace W A ≃ ↥(W ⊓ A) := {
    toFun := fun u => ⟨u.val.toMul, u.val.toMul.property, (mem_subgroupSpace W A u.val).mp u.property⟩
    invFun := fun u => ⟨Additive.ofMul ⟨u.val,u.property.1⟩, (mem_subgroupSpace W A _).mpr u.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [rank, ← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, Nat.log_pow (by decide)]

theorem rank_fixed_centralizer (A : Subgroup G) (hA : A ≤ normalizer (W : Set G)) :
    rank (W ⊓ centralizer (A : Set G)) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation W) (inducedAutomizer W A)) := by
  rw [rank_subgroupSpace]
  apply congrArg (fun P : Submodule (ZMod 2) (Additive W) => Module.finrank (ZMod 2) P)
  ext v
  exact (mem_subgroupSpace W _ v).trans (mem_fixedSpace_inducedAutomizer W A hA v).symm

theorem four_orbit_rank (S : SourceSetup 4 (Automizer W) (Additive W)) : rank W = 8 := by
  have hd : Module.finrank (ZMod 2) (Additive W) = 8 := by
    rw [S.model.coordinates.finrank_eq]
    norm_num [CoordinateSpace, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  rw [Nat.card_congr (Additive.toMul : Additive W ≃ W), hd, Nat.card_zmod] at hc
  rw [rank,hc]
  decide

theorem reverse_small_fixedCodim (S : SourceSetup 4 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hc : subgroupCorank (W.map (MulAut.conj g).toMonoidHom)
      (W.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G)) ≤ 2) :
    rank (inducedAutomizer (W.map (MulAut.conj g).toMonoidHom) A) ≤ 1 := by
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let J := inducedAutomizer Wg A
  let : IsElementaryAbelian 2 J := inducedAutomizer_elementary Wg A hA
  let e := automizerMapEquiv W (MulAut.conj g)
  let I := J.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
  have he : I.map e.toMonoidHom = J := by
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro a
      exact e.apply_symm_apply a
    rw [hcomp, Subgroup.map_id]
  have hh := fixedCodim_map_equivariant (automizerRepresentation W)
    (automizerRepresentation Wg) e.toMonoidHom (automizerModuleEquiv W (MulAut.conj g))
    (automizerRepresentation_equivariant W (MulAut.conj g)) I
  rw [he, fixedCodim_inducedAutomizer Wg A hA] at hh
  have hb := (LowRank.four_small_fixedCodim S I (by rw [hρ,hh]; exact hc)).2
  have hcard : Nat.card I = Nat.card J := Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
  change Nat.log 2 (Nat.card I) ≤ 1 at hb
  rw [hcard] at hb
  exact hb

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
