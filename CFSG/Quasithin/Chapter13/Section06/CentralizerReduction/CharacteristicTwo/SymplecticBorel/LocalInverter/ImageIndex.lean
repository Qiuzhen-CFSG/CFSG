module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Generation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.ModuleKernel
/-!
# The actual Borel image and centralizer index in the Sp₄ branch

The higher-field Borel is two-perfect. Its action on the marked module
therefore lies in the two-residual of the five-point vector stabilizer.
That residual lies in the cubic subgroup on the complementary three
letters: this subgroup is normal and its quotient has exponent two.
The actual Lᵥ contains a lift of the three-cycle, giving the reverse
inclusion and equality of the literal conjugation images in Aut(V).

Faithfulness of the five-point core identifies the permutation kernel
with C_B(V). The image has order three, so O₂(B) lies in this kernel and
|B : C_B(V) O₂(B)| = 3. The existing Transport residual lemmas then
apply to B_C = O²(C_B(V)).

The earlier normalizer action and its compatibility with the marking
are explicit inputs, as in A5Module.FlagSource. The two group placements
Lᵥ ≤ B and B ≤ N_H(V) ∩ C_H(v) also remain explicit; the parent local
assembly supplies them. No image or index conclusion is assumed.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928
(PDF pp.944–945), with the module conventions of §13.2 and §B.3.
-/

@[expose] public section

open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
open A5Module
namespace ImageIndex
private abbrev Perm := Equiv.Perm (Fin 5)
/-- The three permutations on the complementary letters. -/
private def cubicSubgroup : Subgroup Perm where
  carrier := {g | g = 1 ∨ g = cubic.val ∨ g = cubic.val ^ 2}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro g h (rfl | rfl | rfl) (rfl | rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro g (rfl | rfl | rfl) <;> decide +kernel

/-- The literal stabilizer of e₁₂ in the five-point core. -/
private def vectorStabilizer : Subgroup Perm where
  carrier := {g | coreRepresentation (Fin 5) g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change coreRepresentation (Fin 5) (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    have he := congrArg (coreRepresentation (Fin 5) g⁻¹) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he
    exact he.symm

private instance : DecidablePred (· ∈ cubicSubgroup) := fun _ => inferInstanceAs (Decidable (_ = _ ∨ _ = _ ∨ _ = _))
private instance : DecidablePred (· ∈ vectorStabilizer) := fun _ => inferInstanceAs (Decidable (_ = _))


private theorem cubic_card : Nat.card cubicSubgroup = 3 := by rw [Nat.card_eq_fintype_card]; decide +kernel

private theorem square_mem : ∀ g : Perm, g ∈ vectorStabilizer → g^2 ∈ cubicSubgroup := by decide +kernel

private theorem conjugate_mem : ∀ g : Perm, g ∈ vectorStabilizer → g * cubic.val * g⁻¹ ∈ cubicSubgroup := by
  decide +kernel

private instance : (cubicSubgroup.subgroupOf vectorStabilizer).Normal := by
  constructor
  rintro ⟨x, hxD⟩ hx ⟨g, hg⟩
  change g * x * g⁻¹ ∈ cubicSubgroup
  rcases hx with rfl | rfl | rfl
  · simp only [mul_one, mul_inv_cancel]; exact cubicSubgroup.one_mem
  · exact conjugate_mem g hg
  · have hp := cubicSubgroup.pow_mem (conjugate_mem g hg) 2
    simpa only [pow_two, mul_assoc, inv_mul_cancel_left] using hp

private theorem residual_le : pResidual 2 vectorStabilizer ≤ cubicSubgroup.subgroupOf vectorStabilizer := by
  have hq : IsPGroup 2 (vectorStabilizer ⧸ cubicSubgroup.subgroupOf vectorStabilizer) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (cubicSubgroup.subgroupOf vectorStabilizer) q
    refine ⟨1, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact square_mem g g.property
  exact sInf_le ⟨inferInstance, hq⟩

private theorem cubic_le {P : Subgroup Perm} (h : cubic.val ∈ P) : cubicSubgroup ≤ P := by
  rintro g (rfl | rfl | rfl)
  · exact P.one_mem
  · exact h
  · exact P.pow_mem h 2

/-- Four explicit vectors detect the full symmetric action, including odd permutations. -/
private theorem faithful : ∀ g : Perm,
    coreRepresentation (Fin 5) g z = z → coreRepresentation (Fin 5) g v = v →
    coreRepresentation (Fin 5) g a = a →
    coreRepresentation (Fin 5) g (act aConjugator v) = act aConjugator v → g = 1 := by
  decide +kernel
end ImageIndex

variable {H F : Type*} [Group H] [Field F] [Finite H] [Finite F]
variable (K : Subgroup H) (e : K ≃* Sp F) (S : Sylow 2 (Sp F))
variable {L V : Subgroup H}

/-- The ambient Borel map, with codomain the actual normalizer of V. -/
def borelNormalizer (hB : borelIn K e S ≤ normalizer (V : Set H)) :
    localBorel K e S →* normalizer (V : Set H) :=
  (borelMap K e S).codRestrict _ (fun b => hB ⟨b, rfl⟩)

/-- The literal conjugation action of B on V. -/
def borelActionOnV (hB : borelIn K e S ≤ normalizer (V : Set H)) :
    localBorel K e S →* MulAut V :=
  V.normalizerMonoidHom.comp (borelNormalizer K e S hB)

omit [Finite H] [Finite F] in
/-- The action uses the original ambient conjugation convention. -/
theorem borelActionOnV_apply (hB : borelIn K e S ≤ normalizer (V : Set H))
    (b : localBorel K e S) (x : V) :
    ((borelActionOnV K e S hB b x : V) : H) =
      borelMap K e S b * (x : H) * (borelMap K e S b)⁻¹ := rfl

omit [Finite H] [Finite F] in
/-- Its kernel is the literal preimage of C_H(V) under the ambient Borel map. -/
theorem borelActionOnV_ker (hB : borelIn K e S ≤ normalizer (V : Set H)) :
    (borelActionOnV K e S hB).ker = centralizerInBorel K e S V := by
  rw [borelActionOnV, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- Inclusion of the actual residual Lᵥ in the module normalizer. -/
def lvNormalizer (s : Marking L V) : Lv L (markedV s) →* normalizer (V : Set H) :=
  (Lv L (markedV s)).subtype.codRestrict _
    (fun l => marking_normalizes s (by
      obtain ⟨c, _, hc⟩ := l.property
      change (l : H) ∈ L
      rw [← hc]
      exact c.property.1))

/-- The literal Lᵥ-action used in the barred-image equality. -/
def lvActionOnV (s : Marking L V) : Lv L (markedV s) →* MulAut V :=
  V.normalizerMonoidHom.comp (lvNormalizer s)

variable (s : Marking L V)
variable (ρ : normalizer (V : Set H) →* Equiv.Perm (Fin 5))
variable (hρ : ∀ (u : normalizer (V : Set H)) (x : Space),
  MulAut.conj (u : H) (s.map (Multiplicative.ofAdd x)) =
    s.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (ρ u) x)))
variable (hagree : ∀ (l : L) (hl : (l : H) ∈ normalizer (V : Set H)),
  ρ ⟨l, hl⟩ = (s.action l).val)

include hρ in
omit [Field F] [Finite H] [Finite F] in
private theorem action_eq_of_perm_eq (u w : normalizer (V : Set H))
    (he : ρ u = ρ w) : V.normalizerMonoidHom u = V.normalizerMonoidHom w := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, ha⟩ := s.range_eq.ge x.property
  apply Subtype.ext
  change (u : H) * (x : H) * (u : H)⁻¹ = (w : H) * (x : H) * (w : H)⁻¹
  rw [← ha]
  exact (hρ u a.toAdd).trans (by rw [he, ← hρ w a.toAdd]; rfl)

include hρ in
omit [Field F] [Finite H] [Finite F] in
private theorem normalizer_kernel (u : normalizer (V : Set H)) :
    ρ u = 1 ↔ V.normalizerMonoidHom u = 1 := by
  constructor
  · intro he
    exact action_eq_of_perm_eq s ρ hρ u 1 (he.trans (map_one ρ).symm) |>.trans
      (map_one V.normalizerMonoidHom)
  · intro he
    have hf (x : Space) : coreRepresentation (Fin 5) (ρ u) x = x := by
      apply Multiplicative.ofAdd.injective
      apply s.injective
      rw [← hρ]
      let a : V := ⟨s.map (Multiplicative.ofAdd x), s.range_eq.le ⟨_, rfl⟩⟩
      have ha := congrArg (fun f : MulAut V => ((f a : V) : H)) he
      exact ha
    exact ImageIndex.faithful (ρ u) (hf z) (hf v) (hf a) (hf (act aConjugator v))

include hρ in
omit [Finite H] [Finite F] in
private theorem borel_perm_fixes (hB : borelIn K e S ≤ normalizer (V : Set H))
    (hv : borelIn K e S ≤ Gv (markedV s)) (b : localBorel K e S) :
    ρ (borelNormalizer K e S hB b) ∈ ImageIndex.vectorStabilizer := by
  apply Multiplicative.ofAdd.injective
  apply s.injective
  rw [← hρ]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hv ⟨b, rfl⟩))

include hagree in
private theorem lv_cubic_mem :
    cubic.val ∈ (ρ.comp (lvNormalizer s)).range := by
  obtain ⟨c, hc, he⟩ := exists_residual_cubic s
  let l : Lv L (markedV s) := ⟨c, ⟨c, hc, rfl⟩⟩
  refine ⟨l, ?_⟩
  change ρ (lvNormalizer s l) = cubic.val
  rw [show ρ (lvNormalizer s l) = (s.action (inclusion inf_le_left c)).val from
    hagree (inclusion inf_le_left c) (lvNormalizer s l).property, he]

omit [Finite H] [Finite F] in
private theorem lv_perm_le_borel (hB : borelIn K e S ≤ normalizer (V : Set H))
    (hLB : Lv L (markedV s) ≤ borelIn K e S) :
    (ρ.comp (lvNormalizer s)).range ≤ (ρ.comp (borelNormalizer K e S hB)).range := by
  rintro g ⟨l, rfl⟩
  obtain ⟨b, hb⟩ := hLB l.property
  refine ⟨b, ?_⟩
  exact congrArg ρ (Subtype.ext hb)

variable [CharP F 2]

include hρ hagree in
private theorem borel_perm_range {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hB : borelIn K e S ≤ normalizer (V : Set H))
    (hv : borelIn K e S ≤ Gv (markedV s))
    (hLB : Lv L (markedV s) ≤ borelIn K e S) :
    (ρ.comp (borelNormalizer K e S hB)).range = ImageIndex.cubicSubgroup := by
  apply le_antisymm
  · let f : localBorel K e S →* ImageIndex.vectorStabilizer :=
      (ρ.comp (borelNormalizer K e S hB)).codRestrict _
        (borel_perm_fixes K e S s ρ hρ hB hv)
    have hr := map_pResidual_le 2 f
    rw [localBorel_twoPerfect K e hF hn S] at hr
    rintro g ⟨b, rfl⟩
    exact ImageIndex.residual_le (hr ⟨b, mem_top _, rfl⟩)
  · exact (ImageIndex.cubic_le (lv_cubic_mem s ρ hagree)).trans
      (lv_perm_le_borel K e S s ρ hB hLB)

include hρ hagree in
/-- The barred-image equality is equality of the actual conjugation images in Aut(V). -/
theorem borelActionOnV_range_eq {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hB : borelIn K e S ≤ normalizer (V : Set H) ⊓ Gv (markedV s))
    (hLB : Lv L (markedV s) ≤ borelIn K e S) :
    (borelActionOnV K e S (hB.trans inf_le_left)).range = (lvActionOnV s).range := by
  let hBN := hB.trans inf_le_left
  have hp := borel_perm_range K e S s ρ hρ hagree hF hn hBN
    (hB.trans inf_le_right) hLB
  have hlp : (ρ.comp (lvNormalizer s)).range = ImageIndex.cubicSubgroup :=
    le_antisymm ((lv_perm_le_borel K e S s ρ hBN hLB).trans hp.le)
      (ImageIndex.cubic_le (lv_cubic_mem s ρ hagree))
  apply le_antisymm
  · rintro g ⟨b, rfl⟩
    have hb : ρ (borelNormalizer K e S hBN b) ∈ (ρ.comp (lvNormalizer s)).range :=
      hlp.symm ▸ (hp.le ⟨b, rfl⟩)
    obtain ⟨l, hl⟩ := hb
    exact ⟨l, action_eq_of_perm_eq s ρ hρ _ _ hl⟩
  · rintro g ⟨l, rfl⟩
    obtain ⟨b, hb⟩ := hLB l.property
    exact ⟨b, congrArg V.normalizerMonoidHom (Subtype.ext hb)⟩

include hρ hagree in
/-- The literal centralizer, even after adjoining O₂(B), has index three. -/
theorem centralizer_sup_twoCore_index {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hB : borelIn K e S ≤ normalizer (V : Set H) ⊓ Gv (markedV s))
    (hLB : Lv L (markedV s) ≤ borelIn K e S) :
    (centralizerInBorel K e S V ⊔ pCore 2 (localBorel K e S)).index = 3 := by
  let f := ρ.comp (borelNormalizer K e S (hB.trans inf_le_left))
  have hr : f.range = ImageIndex.cubicSubgroup :=
    borel_perm_range K e S s ρ hρ hagree hF hn _ (hB.trans inf_le_right) hLB
  have hk : f.ker = centralizerInBorel K e S V := by
    rw [← borelActionOnV_ker K e S (hB.trans inf_le_left)]
    ext b
    exact normalizer_kernel s ρ hρ (borelNormalizer K e S (hB.trans inf_le_left) b)
  have hc : IsPGroup 3 ImageIndex.cubicSubgroup := IsPGroup.of_card (n := 1) ImageIndex.cubic_card
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
    ((pCore 2 (localBorel K e S)).map f) ImageIndex.cubicSubgroup (pCore_isPGroup.map f) hc
  have hm : (pCore 2 (localBorel K e S)).map f ≤ ImageIndex.cubicSubgroup :=
    (map_le_range _ _).trans hr.le
  have hcore : pCore 2 (localBorel K e S) ≤ f.ker :=
    (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (by
      simpa only [hd.eq_bot] using (le_inf le_rfl hm)))
  rw [← hk, sup_of_le_left hcore, index_ker, hr, ImageIndex.cubic_card]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
