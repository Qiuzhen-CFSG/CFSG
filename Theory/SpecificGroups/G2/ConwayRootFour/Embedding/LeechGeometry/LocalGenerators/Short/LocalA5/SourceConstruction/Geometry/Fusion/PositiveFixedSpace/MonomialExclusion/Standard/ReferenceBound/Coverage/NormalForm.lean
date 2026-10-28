module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Contracts

/-!
# A finite normal form for the reference signed centralizer

The two independent marked letters determine every local linear map. The square
relation makes the column permutation an involution, so its inverse has the same
coordinate formula. The sign commutation equations determine each tetrad's sign
up to one constant; actual Golay membership forces these constants to have even
parity. Thus only a column permutation, six hexacode bits, and five parity bits
remain. No enumeration or candidate-table exhaustiveness is assumed here.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, and the root-four convention on p.269. The code and local isometries
use the existing attributed ATLAS model.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage

/-- The unique linear map carrying both marked letters from column `i` to `j`. -/
def markedMap (i j : HexIndex) : KIsometry :=
  if i.2 = j.2 then 1 else localW

private theorem reference_letter_cases : ∀ (i : HexIndex) (x : K),
    x = 0 ∨ x = referenceHexA i ∨ x = referenceHexB i ∨
      x = referenceHexA i + referenceHexB i := by decide

private theorem markedMap_marks : ∀ i j : HexIndex,
    markedMap i j (referenceHexA i) = referenceHexA j ∧
    markedMap i j (referenceHexB i) = referenceHexB j := by decide

theorem markedMap_unique (i j : HexIndex) (e : KIsometry)
    (ha : e (referenceHexA i) = referenceHexA j)
    (hb : e (referenceHexB i) = referenceHexB j) : e = markedMap i j := by
  apply LinearEquiv.ext
  intro x
  rcases reference_letter_cases i x with rfl | rfl | rfl | rfl
  · simp only [map_zero]
  · exact ha.trans (markedMap_marks i j).1.symm
  · exact hb.trans (markedMap_marks i j).2.symm
  · simp only [map_add, ha, hb, (markedMap_marks i j).1, (markedMap_marks i j).2]

def markedPull (pi : HexIndex → HexIndex) (t : HexWord) (i : Omega) : Omega :=
  (pi i.1, rowLabel.symm (markedMap i.1 (pi i.1) (rowLabel i.2) + t (pi i.1)))

/-- Destination action for an involutive column permutation. -/
def markedAction (pi : HexIndex → HexIndex) (w : HexWord) : HexWord :=
  fun j => markedMap (pi j) j (w (pi j))

/-- Reduction of the actual inverse coordinate permutation, including code preservation. -/
theorem centralizer_marked_parameters (m : GolayMonomialGroup)
    (h : CentralizerParameters m) :
    ∃ (t : hexacode) (pi : Equiv.Perm HexIndex),
      (∀ i, monomialPull m i = markedPull pi t.val i) ∧
      Function.Involutive pi ∧
      (∀ w ∈ hexacode, markedAction pi w ∈ hexacode) := by
  obtain ⟨t, g, hp, ha, hb⟩ := centralizer_affine_parameters m h
  have hl (i : HexIndex) : g.val.localMap (g.val.perm i) =
      markedMap i (g.val.perm i) := markedMap_unique _ _ _ (ha i) (hb i)
  have hp' (i : Omega) : monomialPull m i = markedPull g.val.perm t.val i := by
    rcases i with ⟨i,k⟩
    rw [hp, affinePermutation_apply]
    exact congrArg (fun e : KIsometry => (g.val.perm i,
      rowLabel.symm (e (rowLabel k) + t.val (g.val.perm i)))) (hl i)
  have hpi : Function.Involutive g.val.perm := by
    intro i
    have hi := congrArg Prod.fst (h.involutive (i,0))
    simpa only [hp', markedPull] using hi
  have hinv (i : HexIndex) : g.val.perm.symm i = g.val.perm i := by
    apply g.val.perm.injective
    simpa only [Equiv.apply_symm_apply] using (hpi i).symm
  refine ⟨t, g.val.perm, hp', hpi, ?_⟩
  intro w hw
  have he : markedAction g.val.perm w = Monomial.act g.val w := by
    funext j
    have hj := hl (g.val.perm j)
    simpa only [markedAction, Monomial.act_apply, hinv, hpi j] using
      congrArg (fun e : KIsometry => e (w (g.val.perm j))) hj.symm
  rw [he]
  exact (g.prop w).mp hw


def signLetter (i j : HexIndex) (t : K) : K :=
  markedMap j i (if j.2 = 0 then localKappa⁻¹ t else localKappa t)

private theorem local_sign_rules : ∀ (i j : HexIndex) (t : K) (k : Fin 4),
    (jWord (fun _ => signLetter i j t) (i,k) +
        Atlas.Codes.j (referenceHexB j) (rowLabel.symm (markedMap i j (rowLabel k) + t)) =
      jWord referenceHexB (i,k) +
        Atlas.Codes.j (signLetter i j t) (referencePullA (i,k)).2) ∧
    (jWord (fun _ => signLetter i j t) (i,k) +
        Atlas.Codes.j ((referenceHexA + referenceHexB) j)
          (rowLabel.symm (markedMap i j (rowLabel k) + t)) =
      jWord (referenceHexA + referenceHexB) (i,k) +
        Atlas.Codes.j (signLetter i j t) (referencePullB (i,k)).2) := by decide

def signWord (pi : HexIndex → HexIndex) (t : HexWord) : BinaryWord :=
  jWord (fun i => signLetter i (pi i) (t (pi i)))

private theorem reference_orbit : ∀ i : Omega,
    i = (i.1,0) ∨ i = referencePullA (i.1,0) ∨ i = referencePullB (i.1,0) ∨
      i = referencePullA (referencePullB (i.1,0)) := by decide

theorem reference_invariant_constant (s : BinaryWord)
    (ha : ∀ i, s (referencePullA i) = s i)
    (hb : ∀ i, s (referencePullB i) = s i) (i : Omega) :
    s i = s (i.1,0) := by
  rcases reference_orbit i with he | he | he | he
  · exact congrArg s he
  · exact (congrArg s he).trans (ha _)
  · exact (congrArg s he).trans (hb _)
  · exact (congrArg s he).trans ((ha _).trans (hb _))

/-- Both sign commutation equations leave only the row-zero bit in each tetrad. -/
theorem centralizer_signWord (m : GolayMonomialGroup) (h : CentralizerParameters m)
    (pi : Equiv.Perm HexIndex) (t : HexWord)
    (hp : ∀ i, monomialPull m i = markedPull pi t i) :
    m.left.toAdd.val = signWord pi t + rho (fun i => m.left.toAdd.val (hexIndexEquiv.symm i,0)) := by
  have hfA (i : Omega) : signWord pi t i + jWord referenceHexB (monomialPull m i) =
      jWord referenceHexB i + signWord pi t (referencePullA i) := by
    rw [hp]
    exact (local_sign_rules i.1 (pi i.1) (t (pi i.1)) i.2).1
  have hfB (i : Omega) : signWord pi t i +
        jWord (referenceHexA + referenceHexB) (monomialPull m i) =
      jWord (referenceHexA + referenceHexB) i + signWord pi t (referencePullB i) := by
    rw [hp]
    exact (local_sign_rules i.1 (pi i.1) (t (pi i.1)) i.2).2
  have ha (i : Omega) : (m.left.toAdd.val - signWord pi t) (referencePullA i) =
      (m.left.toAdd.val - signWord pi t) i := by
    have hs := h.sign_a i
    have hf := hfA i
    dsimp only [Pi.sub_apply]
    linear_combination -hs + hf
  have hb (i : Omega) : (m.left.toAdd.val - signWord pi t) (referencePullB i) =
      (m.left.toAdd.val - signWord pi t) i := by
    have hs := h.sign_b i
    have hf := hfB i
    dsimp only [Pi.sub_apply]
    linear_combination -hs + hf
  funext i
  have hc := reference_invariant_constant _ ha hb i
  change m.left.toAdd.val i = signWord pi t i + m.left.toAdd.val (hexIndexEquiv.symm (hexIndexEquiv i.1),0)
  rw [Equiv.symm_apply_apply]
  have hz : signWord pi t (i.1,0) = 0 := rfl
  dsimp only [Pi.sub_apply] at hc
  rw [hz, sub_zero] at hc
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

/-- Golay membership removes the odd coset and supplies the five parity parameters. -/
theorem centralizer_even_column_sign (m : GolayMonomialGroup) (h : CentralizerParameters m)
    (pi : Equiv.Perm HexIndex) (t : HexWord)
    (hp : ∀ i, monomialPull m i = markedPull pi t i) :
    ∃ r : Fin 5 → Bit, m.left.toAdd.val = signWord pi t + rho (parityEncoder 5 r) := by
  have hx := centralizer_signWord m h pi t hp
  obtain ⟨⟨u,r,e⟩, he⟩ := m.left.toAdd.prop
  have he0 : e = 0 := by
    have hh := congrArg (fun w : BinaryWord => blockParity w (0,0)) he
    rw [golayEncoder_blockParity, hx] at hh
    simpa [blockParity, signWord, jWord, rho, Finset.sum_add_distrib,
      Fintype.card_fin, nsmul_eq_mul] using hh
  have hr : r.val = fun i => m.left.toAdd.val (hexIndexEquiv.symm i,0) := by
    funext i
    have hh := congrFun he (hexIndexEquiv.symm i,0)
    simpa [golayEncoder, c0Encoder, he0, jWord, rho] using hh
  obtain ⟨v,hv⟩ := r.prop
  refine ⟨v, ?_⟩
  rw [hv, hr]
  exact hx

/-- The generator tests are literal hexacode membership, using its checked decoder. -/
def ColumnChecks (pi : HexIndex → HexIndex) : Prop :=
  Function.Involutive pi ∧ ∀ k : Fin 6,
    hexEncoder (hexDecoder (markedAction pi (hexGenerators k))) =
      markedAction pi (hexGenerators k)

instance (pi : HexIndex → HexIndex) : Decidable (ColumnChecks pi) :=
  inferInstanceAs (Decidable ((∀ i, pi (pi i) = i) ∧ _))

def signedWord (pi : HexIndex → HexIndex) (u : HexParameters) (r : Fin 5 → Bit) : BinaryWord :=
  signWord pi (hexEncoder u) + rho (parityEncoder 5 r)

/-- The complete reduction consumed by the exhaustive candidate-table check. -/
theorem centralizer_finite_parameters (m : GolayMonomialGroup) (h : CentralizerParameters m) :
    ∃ (pi : Equiv.Perm HexIndex) (u : HexParameters) (r : Fin 5 → Bit),
      ColumnChecks pi ∧
      (∀ i, monomialPull m i = markedPull pi (hexEncoder u) i) ∧
      m.left.toAdd.val = signedWord pi u r := by
  obtain ⟨t, pi, hp, hi, hh⟩ := centralizer_marked_parameters m h
  obtain ⟨r, hr⟩ := centralizer_even_column_sign m h pi t.val hp
  obtain ⟨u, hu⟩ := t.prop
  refine ⟨pi, u, r, ⟨hi, ?_⟩, ?_, ?_⟩
  · intro k
    have hk : hexGenerators k ∈ hexacode := by
      rw [← hexBasis_coe]
      exact (hexBasis k).prop
    obtain ⟨v, hv⟩ := hh _ hk
    rw [← hv, hex_decode_encode]
  · simpa only [hu] using hp
  · simpa only [signedWord, hu] using hr

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage
