module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallCorePlacement
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# The marked quaternion core lies in the ambient seed span

The local core P is B Bᵍ in the original pair, with B=P∩V. Mapping these
two factors through the literal pair inclusion puts P in ⟨Bᴴ⟩. This
provides the order-thirty-two lower bound needed for the global section
in Aschbacher--Smith, E.2.17, printed pp.229--230.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}
theorem OriginalWitness.small_core_le_span (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk)) :
    w.pair.subgroup.pCoreIn 2 ≤ conjugateSpanBy (w.pair.subgroup.pCoreIn 2 ⊓ W) ⊤ := by
  let h := w.pair.hypotheses hWS hSW hcore hn
  let hSU' := w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)
  let e := subgroupOfEquivOfLe w.pair.le
  let ρ := DihedralCubic.representation U W hU q hq hk
  let f := DihedralCubic.actorMap h hSU' q
  have hp := w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one
  have hf := w.pair.fitting hSW hfit
  have ha : ∀ (a : A (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup) w.pair.conjugator)
      (v : W.subgroupOf w.pair.subgroup),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : w.pair.subgroup) =
        (a : w.pair.subgroup) * v * (a : w.pair.subgroup)⁻¹ := by
    intro a v
    apply Subtype.ext
    change ((ρ (q (DihedralCubic.actorIn h hSU' a)) (Additive.ofMul (e v))).toMul : H) =
      ((a : w.pair.subgroup) : H) * ((v : w.pair.subgroup) : H) *
        ((a : w.pair.subgroup) : H)⁻¹
    rw [DihedralCubic.representation_apply]
    rfl
  have hρ := DihedralCubic.representation_injective U W hU q hq hk
  have hcard := w.model.star_card_two h hp hf ((Nat.card_congr e.toEquiv).trans hW)
    e ρ hρ f ha hD hratio
  let B₀ := w.pair.subgroup.pCoreIn 2 ⊓ W
  let L := conjugateSpanBy B₀ ⊤
  have hB : (B (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup)).map
      w.pair.subgroup.subtype = B₀ := by
    rw [h.B_eq_twoCore_inf,map_inf _ _ _ w.pair.subgroup.subtype_injective,
      map_subgroupOf_eq_of_le w.pair.le]
    rfl
  change (pCore 2 w.pair.subgroup).map w.pair.subgroup.subtype ≤ L
  rw [←(h.odd_dihedral hcard).1,P,Subgroup.map_sup]
  apply sup_le
  · rw [hB]
    exact le_conjugateSpanBy B₀ ⊤
  · rintro x ⟨a,ha,rfl⟩
    obtain ⟨b,hb,rfl⟩ := ha
    change (w.pair.conjugator : H) * (b : H) * (w.pair.conjugator : H)⁻¹ ∈ L
    apply le_normalizer_iff.mp (le_normalizer_conjugateSpanBy B₀ ⊤)
      (w.pair.conjugator : H) (mem_top _) (b : H)
    apply le_conjugateSpanBy B₀ ⊤
    rw [←hB]
    exact mem_map_of_mem w.pair.subgroup.subtype hb

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
