module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.PoolData
/-!
# Checking packed numeric records

The output of each cyclic trace instruction is checked as a single encoded
natural number. The decoding lemma and `packedCheck_sound` recover every clause
of the original `Pooled.check`, including predecessor bounds and exponents mod 13.
The tables and the source conventions are those of `../source/README.md`.
-/
@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
def checkValues (sv rv cv dv pv qv n : Nat)
    (op : Pooled.NumericInstruction) (out : Pooled.NumericFact) : Bool :=
  match op.tag with
  | 0 => out.left == op.p && out.word == 914 && out.right == op.p && out.exponent == 0
  | 1 => Nat.blt 0 op.p && out.left == min (dv / 4) (op.p - 1) &&
      out.word == (if dv % 4 < 2 then dv % 4 else dv % 4 + 1) && out.right == op.p && out.exponent == 0
  | 2 => out.left == 0 && out.word == 2 && out.right == 0 && out.exponent == 1
  | 3 => Nat.blt op.rule 164 && out.left == op.p &&
      out.word == (sv % 16384) && out.right == op.p && out.exponent == 0
  | 4 => Nat.blt op.p n && Nat.blt op.rule 2965 &&
      out.left == (Pooled.fact pv).right && out.right == (Pooled.fact pv).left &&
      (Pooled.fact pv).word == (rv / 16384) && out.word == (rv % 16384) &&
      (out.exponent + (Pooled.fact pv).exponent) % 13 == 0
  | _ => Nat.blt op.p n && Nat.blt op.q n && Nat.blt op.rule 14812 &&
      out.left == (Pooled.fact pv).left && out.right == (Pooled.fact qv).right &&
      (Pooled.fact pv).right == (Pooled.fact qv).left &&
      (Pooled.fact pv).word == (cv / 268435456) &&
      (Pooled.fact qv).word == (cv / 16384 % 16384) &&
      out.word == (cv % 16384) &&
      out.exponent == ((Pooled.fact pv).exponent + (Pooled.fact qv).exponent) % 13

def encode (l w r e : Nat) : Nat :=
  l * 549755813888 + w * 33554432 + r * 16 + e

theorem fact_encode (l w r e : Nat) (hw : w < 16384) (hr : r < 2097152)
    (he : e < 16) : Pooled.fact (encode l w r e) = ⟨l, w, r, e⟩ := by
  simp only [Pooled.fact, encode]
  congr 1 <;> omega

def packedValues (sv rv cv dv pv qv n : Nat)
    (op : Pooled.NumericInstruction) (out : Nat) : Bool :=
  match op.tag with
  | 0 => Nat.blt op.p 2097152 && out == encode op.p 914 op.p 0
  | 1 => Nat.blt 0 op.p && Nat.blt op.p 2097152 &&
      out == encode (min (dv / 4) (op.p - 1))
        (if dv % 4 < 2 then dv % 4 else dv % 4 + 1) op.p 0
  | 2 => out == encode 0 2 0 1
  | 3 => Nat.blt op.rule 164 && Nat.blt op.p 2097152 &&
      out == encode op.p (sv % 16384) op.p 0
  | 4 => Nat.blt op.p n && Nat.blt op.rule 2965 &&
      Nat.blt (Pooled.fact pv).left 2097152 &&
      (Pooled.fact pv).word == rv / 16384 &&
      out == encode (Pooled.fact pv).right (rv % 16384) (Pooled.fact pv).left
        ((13 - (Pooled.fact pv).exponent % 13) % 13)
  | _ => Nat.blt op.p n && Nat.blt op.q n && Nat.blt op.rule 14812 &&
      (Pooled.fact pv).right == (Pooled.fact qv).left &&
      (Pooled.fact pv).word == cv / 268435456 &&
      (Pooled.fact qv).word == cv / 16384 % 16384 &&
      out == encode (Pooled.fact pv).left (cv % 16384) (Pooled.fact qv).right
        (((Pooled.fact pv).exponent + (Pooled.fact qv).exponent) % 13)

theorem packedValues_sound (sv rv cv dv pv qv n : Nat)
    (op : Pooled.NumericInstruction) (out : Nat)
    (h : packedValues sv rv cv dv pv qv n op out = true) :
    checkValues sv rv cv dv pv qv n op (Pooled.fact out) = true := by
  unfold packedValues at h
  split at h <;> rename_i ht <;>
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
  · obtain ⟨hp, ho⟩ := h
    rw [ho, fact_encode _ _ _ _ (by decide) hp (by decide)]
    simp [checkValues, ht]
  · obtain ⟨⟨hp0, hp⟩, ho⟩ := h
    have hw : (if dv % 4 < 2 then dv % 4 else dv % 4 + 1) < 16384 := by
      split <;> omega
    rw [ho, fact_encode _ _ _ _ hw hp (by decide)]
    simp [checkValues, ht, hp0]
  · rw [h, fact_encode _ _ _ _ (by decide) (by decide) (by decide)]
    simp [checkValues, ht]
  · obtain ⟨⟨hr, hp⟩, ho⟩ := h
    rw [ho, fact_encode _ _ _ _ (Nat.mod_lt _ (by decide)) hp (by decide)]
    simp [checkValues, ht, hr]
  · obtain ⟨⟨⟨⟨hp, hr⟩, hl⟩, hw⟩, ho⟩ := h
    have he : (13 - (Pooled.fact pv).exponent % 13) % 13 < 16 := by omega
    have hex : ((13 - (Pooled.fact pv).exponent % 13) % 13 +
        (Pooled.fact pv).exponent) % 13 = 0 := by omega
    rw [ho, fact_encode _ _ _ _ (Nat.mod_lt _ (by decide)) hl he]
    simp [checkValues, ht, hp, hr, hw, hex]
  · obtain ⟨⟨⟨⟨⟨⟨hp, hq⟩, hr⟩, hm⟩, hw₁⟩, hw₂⟩, ho⟩ := h
    have hright : (Pooled.fact qv).right < 2097152 := Nat.mod_lt _ (by decide)
    have he : ((Pooled.fact pv).exponent + (Pooled.fact qv).exponent) % 13 < 16 := by omega
    rw [ho, fact_encode _ _ _ _ (Nat.mod_lt _ (by decide)) hright he]
    simp [checkValues, hp, hq, hr, hm, hw₁, hw₂]
def packedCheck (d f o : Nat → Nat) (n : Nat) : Bool :=
  let op := Pooled.instruction (o n)
  packedValues (sourceCode op.rule) (reversalCode op.rule) (compositionCode op.rule)
    (d op.p) (f op.p) (f op.q) n op (f n)

theorem packedCheck_sound (d f o : Nat → Nat) (n : Nat)
    (h : packedCheck d f o n = true) :
    Pooled.check (pool (fun _ => [])) d (fun k => Pooled.fact (f k)) n
      (Pooled.instruction (o n)) (Pooled.fact (f n)) = true := by
  exact packedValues_sound _ _ _ _ _ _ _ _ _ h

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
