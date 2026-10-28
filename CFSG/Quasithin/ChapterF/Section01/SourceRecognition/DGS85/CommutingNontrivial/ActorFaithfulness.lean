module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.MovingActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CoreIntersections

/-!
# Faithfulness on the actual two-subgroup actor

For a centerless local group, the central alternative of 6.2(c) would make
its nonzero Sylow-center span trivial. Hence Q is Sylow in the full local
centralizer of Z. Every two-subgroup therefore has the same intersection
with this centralizer and with Q. The literal quotient action on Z is
faithful on its image, with the original conjugation equation retained.

This does not assert faithfulness of the whole quotient. `MovingApplication`
applies the result to A = V_beta intersect Q_alpha' at the actual moving
neighbor, supplying the faithful quadratic actor used in 8.1 and later
module estimates.

Source: DGS, *Groups and Graphs* (1985), 6.2(c), p.119; 8.1, pp.132--134.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- At a centerless local actor the center alternative of 6.2(c) is impossible.
Thus the original Q is Sylow in the full vertex centralizer of Z. -/
theorem source_centerless_centralizer_sylow
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (hz : center (d.localGroup v) = ⊥) :
    ∃ T : Sylow 2 ↥(stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G),
      (T : Subgroup ↥(stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G)).map
        (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G)).subtype = Q (family P) v := by
  let := finite_endpoints h
  rcases d.sylow_or_center v with hs | he
  · exact hs
  · exfalso
    have hΩ : omegaCenterIn (d.localGroup v) = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      rintro x ⟨y, ⟨z, hz', rfl⟩, rfl⟩
      have hy : (z : d.localGroup v) = 1 := mem_bot.mp (hz ▸ z.property)
      exact mem_bot.mpr (congrArg (d.localGroup v).subtype hy)
    have hbot := he.trans hΩ
    obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
    rw [← hg, Z_translate, map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot
    exact base_Z_ne_bot h _ hbot

/-- On every two-subgroup, the original centralizer kernel agrees exactly
with the original vertex core, even before full quotient faithfulness. -/
theorem source_centerless_actor_kernel
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (hz : center (d.localGroup v) = ⊥)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAP : A ≤ stabilizer (family P) v) :
    A ⊓ centralizer (Z (family P) v : Set G) = A ⊓ Q (family P) v := by
  exact Noncommuting.inf_centralizer_eq_inf_core (stabilizer (family P) v)
    (Q (family P) v) (Z (family P) v) A hp hAP (Q_le_stabilizer _ _)
    (le_centralizer_iff.mp (Z_centralizes_Q (family P) v (source_Z_Q_U h v).1))
    (stabilizer_normalizes_Q (family P) v)
    (source_centerless_centralizer_sylow h d v hz)

/-- The actual quotient representation is faithful on every specified two-actor.
No faithfulness of the entire rank-one quotient is assumed. -/
theorem source_centerless_two_actor_faithful
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (hz : center (d.localGroup v) = ⊥)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAL : A ≤ d.localGroup v)
    {D : Type*} [Group D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup v)))
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) v))),
      (∀ (l : d.localGroup v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Function.Injective (ρ.comp ((A.subgroupOf (d.localGroup v)).map q).subtype) := by
  let := CommutingOneProfile.source_center_elementary h v
  dsimp only
  intro ρ hact
  let L := d.localGroup v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hker := source_centerless_actor_kernel h d v hz A hp (hAL.trans (d.local_le v))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply _root_.eq_bot_iff.mpr
  rintro ⟨x, hx⟩ hk
  obtain ⟨l, hl, rfl⟩ := hx
  have hc : (l : G) ∈ centralizer (Z (family P) v : Set G) := by
    intro z hz
    have hf : ρ (q l) (Additive.ofMul (⟨z, hz⟩ : Z (family P) v)) =
        Additive.ofMul (⟨z, hz⟩ : Z (family P) v) :=
      congrArg (fun f : Module.End (ZMod 2) (Additive (Z (family P) v)) =>
        f (Additive.ofMul (⟨z, hz⟩ : Z (family P) v))) hk
    have he := congrArg (fun z : Additive (Z (family P) v) => (z.toMul : G)) hf
    rw [hact] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hQ : (l : G) ∈ Q (family P) v := (hker.le ⟨hl, hc⟩).2
  have hq : l ∈ q.ker := by
    rw [local_quotient_kernel]
    exact hQ
  exact mem_bot.mpr (Subtype.ext hq)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
