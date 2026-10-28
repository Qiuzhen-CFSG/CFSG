module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Fusion
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Core.Lifting
public import CFSG.Quasithin.Chapter1.Defs

/-!
# Hyperplanes and weak-closure bounds in Section 15.3

We prove the conditional implication 15.3.63 from the genuine fusion and
abelian-span inputs of 15.3.62, zero-index weak closure from 15.3.46(4),
and the earlier E.4.1 and E.3.35(1) outputs. Those two outputs remain explicit:
`localA V = 1` is the value for the actual automizer representation, and
`GenerationContainmentInput` is E.3.35(1) specialized to the outside family.
The source assembly must supply them from the solvable automizer and the
uniqueness/centralizer hypotheses, respectively.

Instead of first computing the offender image rank, we use the definition
of `a=1` directly: every noncentralizing elementary abelian actor has a
hyperplane whose fixed space is larger. Lifting through the actual automizer
produces B of corank one in A, with [C_V(B),A] nontrivial. For a hyperplane
A of Vᵍ, B has corank two in Vᵍ. The bound r≥3 puts C_V(B) in N_G(Vᵍ),
so the nontrivial commutator lies in V∩Vᵍ. Lemma 15.3.62 then kills it.
Taking the actual weak-closure span proves W₁≤C_T(V), and the infimum
calculation proves w>1 even when the minimizing family is empty.

The concluding r=2 helper uses a minimal member of the genuine nonempty
outside family, without truncating infinity to a natural number. The field
parity helper derives oddness from a torus divisor and the 3-prime local
intersection; the torus divisor still needs its actual model proof. The
shared quotient-action interface fixes the actor H/O₂(H), the module U/Z,
and its conjugation formula. None of these helpers asserts 15.3.64 or the
minimal-member assertion 15.3.65(1).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1151–1152, with E.3.8–9, E.3.35(1), and E.4.1.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fixedSpace_eq_of_relative_centralizer_eq
    {V A B : Subgroup G} [IsElementaryAbelian 2 V]
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (h : V ⊓ centralizer (A : Set G) = V ⊓ centralizer (B : Set G)) :
    fixedSpace (automizerRepresentation V) (inducedAutomizer V A) =
      fixedSpace (automizerRepresentation V) (inducedAutomizer V B) := by
  ext v
  rw [mem_fixedSpace_inducedAutomizer V A hA, mem_fixedSpace_inducedAutomizer V B hB]
  have hv := congrArg (fun S : Subgroup G => (v.toMul : G) ∈ S) h
  simpa only [Subgroup.mem_inf, v.toMul.property, true_and] using (iff_of_eq hv)

/-- Lift a failure of the second fixed-space family to an actual hyperplane. -/
theorem exists_hyperplane_nontrivial_commutator
    {V A : Subgroup G} [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (ha : localA V = 1) (hAN : A ≤ normalizer (V : Set G))
    (hAC : ¬ A ≤ centralizer (V : Set G)) :
    ∃ B ≤ A, subgroupCorank A B = 1 ∧ ⁅V ⊓ centralizer (B : Set G), A⁆ ≠ ⊥ := by
  classical
  have hI : IsElementaryTwo (inducedAutomizer V A) :=
    ⟨fun hz => hAC ((inducedAutomizer_eq_bot_iff hAN).mp hz),
      inducedAutomizer_elementary V A hAN⟩
  have hn : ¬ inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 := by
    intro h
    have hh := le_moduleA_of_mem (automizerRepresentation V) h
    change (2 : ℕ∞) ≤ localA V at hh
    rw [ha] at hh
    norm_num at hh
  have hex : ∃ D ≤ inducedAutomizer V A,
      Nat.log 2 (D.relIndex (inducedAutomizer V A)) < 2 ∧
      fixedSpace (automizerRepresentation V) (inducedAutomizer V A) ≠
        fixedSpace (automizerRepresentation V) D := by
    by_contra! hf
    exact hn ⟨by decide, hI, hf⟩
  obtain ⟨D, hDI, hDcor, hne⟩ := hex
  obtain ⟨B, hBA, hBI, hcor⟩ := core_lift_image_subgroup hAN D hDI
  have hcor1 : subgroupCorank A B = 1 := by
    have hlt : subgroupCorank A B < 2 := hcor ▸ hDcor
    have hn0 : subgroupCorank A B ≠ 0 := by
      intro hz
      have he := subgroup_eq_of_corank_zero hBA hz
      exact hne (by rw [← hBI, he])
    omega
  refine ⟨B, hBA, hcor1, ?_⟩
  intro hcomm
  apply hne
  rw [← hBI]
  apply fixedSpace_eq_of_relative_centralizer_eq hAN (hBA.trans hAN)
  exact le_antisymm (inf_le_inf_left V (centralizer_le hBA))
    (le_inf inf_le_left (commutator_eq_bot_iff_le_centralizer.mp hcomm))

/-- The actual hyperplane argument, before taking the weak-closure span. -/
theorem hyperplane_le_centralizer_of_three_le_globalR
    {V T : Subgroup G} [IsElementaryAbelian 2 V]
    (ha : localA V = 1) (hr : (3 : ℕ∞) ≤ globalR V)
    (hTN : T ≤ normalizer (V : Set G))
    (hinter : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {A : Subgroup G} (hA : A ∈ gamma V T 1) :
    A ≤ centralizer (V : Set G) := by
  classical
  by_contra hAC
  obtain ⟨⟨g, hAg, hidx⟩, hAT⟩ := hA
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 A := offender_elementary_of_le hAg
  have hAN := hAT.trans hTN
  obtain ⟨B, hBA, hBcor, hcomm⟩ := exists_hyperplane_nontrivial_commutator ha hAN hAC
  have hAcor : subgroupCorank W A = 1 := by
    change Nat.log 2 (A.relIndex W) = 1
    change A.relIndex W = 2 ^ 1 at hidx
    rw [hidx, Nat.log_pow (by decide)]
  have hBcorW : subgroupCorank W B = 2 := by
    rw [offender_corank_add hBA hAg, hAcor, hBcor]
  have hCW : V ⊓ centralizer (B : Set G) ≤ normalizer (W : Set G) := by
    apply inf_le_right.trans
    apply centralizer_le_normalizer_of_corank_lt_globalR (hBA.trans hAg)
    rw [hBcorW, globalR_map_equiv]
    exact lt_of_lt_of_le (by norm_num) hr
  have hcommV : ⁅V ⊓ centralizer (B : Set G), A⁆ ≤ V :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hAN)
  have hcommW : ⁅V ⊓ centralizer (B : Set G), A⁆ ≤ W :=
    (commutator_mono le_rfl hAg).trans
      (le_normalizer_iff_commutator_le_right.mp hCW)
  have hmeet : V ⊓ W ≠ ⊥ := by
    intro hz
    exact hcomm (le_bot_iff.mp ((le_inf hcommV hcommW).trans_eq hz))
  exact hcomm (le_bot_iff.mp ((commutator_mono inf_le_left hAg).trans_eq (hinter g hmeet)))

omit [Finite G] in
/-- The weak-closure minimum stays in the extended naturals throughout. -/
theorem one_lt_globalW_of_first_two_centralize
    {V T : Subgroup G}
    (hzero : indexedWeakClosure V T 0 ≤ centralizer (V : Set G))
    (hone : indexedWeakClosure V T 1 ≤ centralizer (V : Set G)) :
    1 < globalW V T := by
  have htwo : (2 : ℕ∞) ≤ globalW V T := by
    apply le_iInf
    intro j
    apply le_iInf
    intro hj
    by_cases h : 2 ≤ j
    · exact_mod_cast h
    · have he : j = 0 ∨ j = 1 := by omega
      rcases he with rfl | rfl
      · exact (hj (le_inf (indexedWeakClosure_le V T 0) hzero)).elim
      · exact (hj (le_inf (indexedWeakClosure_le V T 1) hone)).elim
  exact lt_of_lt_of_le (by norm_num) htwo

/-- The conditional weak-closure conclusion in 15.3.63(1). -/
theorem lemma_15_3_63_1_of_localA
    {V T : Subgroup G} [IsElementaryAbelian 2 V]
    (ha : localA V = 1) (hr : (3 : ℕ∞) ≤ globalR V)
    (hTN : T ≤ normalizer (V : Set G))
    (hzero : indexedWeakClosure V T 0 ≤ centralizer (V : Set G))
    (hinter : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    indexedWeakClosure V T 1 ≤ T ⊓ centralizer (V : Set G) ∧ 1 < globalW V T := by
  have hone : indexedWeakClosure V T 1 ≤ centralizer (V : Set G) := by
    rw [weakClosure_eq_sSup_gamma]
    exact sSup_le fun _ hA => hyperplane_le_centralizer_of_three_le_globalR ha hr hTN hinter hA
  exact ⟨le_inf (indexedWeakClosure_le V T 1) hone,
    one_lt_globalW_of_first_two_centralize hzero hone⟩

/-- 15.3.63(1), with 15.3.62 derived from the original local inputs. The sole
additional module input is the exact E.4.1 value on the actual automizer. -/
theorem lemma_15_3_63_1
    {V M Mc : Subgroup G} [IsElementaryAbelian 2 V] {z : G}
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hzV : z ∈ V) (hz : z ≠ 1) (hzs : d.singular ⟨z, hzV⟩)
    (hMc : Mc = centralizer (zpowers z : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ m ∈ M, MulAut.conj m z = MulAut.conj a z)
    (hsingular : ∀ g : G, g ∉ M →
      ∀ x : ↥(V ⊓ V.map (MulAut.conj g).toMonoidHom),
        d.singular ⟨x, x.property.1⟩)
    [IsMulCommutative (conjugateSpanBy V Mc)]
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hzero : indexedWeakClosure V T 0 ≤ centralizer (V : Set G))
    (ha : localA V = 1) (hr : (3 : ℕ∞) ≤ globalR V) :
    indexedWeakClosure V T 1 ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      1 < globalW V T :=
  lemma_15_3_63_1_of_localA ha hr (hTM.trans d.normalizes) hzero
    (lemma_15_3_62_2 d hzV hz hzs hMc hfusion hsingular)

/-- The source family H(T,M), with nontrivial two-core and actual containment. -/
def sylowOutsideFamily (T : Sylow 2 G) (M : Subgroup G) : Set (Subgroup G) :=
  Chapter1.HOutside G ((T : Subgroup G) : Set G) (M : Set G)

/-- The minimal members H*(T,M) of that same family. -/
def minimalSylowOutsideFamily (T : Sylow 2 G) (M : Subgroup G) : Set (Subgroup G) :=
  {H | Minimal (fun J => J ∈ sylowOutsideFamily T M) H}

/-- The precise local implication supplied by E.3.35(1). The source assembly
must discharge its uniqueness and relative-centralizer hypotheses. This uses
the actual E-generation parameter, with no field exponent substituted for it. -/
def GenerationContainmentInput (V : Subgroup G) (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∀ H ∈ sylowOutsideFamily T M,
    (generationParameter H : ℕ∞) < min (globalW V T) (globalR V) → H ≤ M

/-- The n(H) assertion of 15.3.63(2) from the proved weak-closure bounds and
E.3.35(1), retaining the latter's precise output as an explicit earlier input. -/
theorem lemma_15_3_63_2_of_generation_containment
    {V M : Subgroup G} {T : Sylow 2 G}
    (hgen : GenerationContainmentInput V T M)
    (hr : (3 : ℕ∞) ≤ globalR V) (hw : 1 < globalW V T)
    {H : Subgroup G} (hH : H ∈ sylowOutsideFamily T M) :
    1 < generationParameter H := by
  by_contra hn
  have hle : (generationParameter H : ℕ∞) ≤ 1 := by
    exact_mod_cast (show generationParameter H ≤ 1 by omega)
  have hlt : (generationParameter H : ℕ∞) < min (globalW V T) (globalR V) :=
    lt_min (hle.trans_lt hw) (hle.trans_lt (lt_of_lt_of_le (by norm_num) hr))
  exact hH.2 (hgen H hH hlt)

/-- Both parts of 15.3.63, conditional only on the earlier local conclusions,
E.4.1 and E.3.35(1). In particular w>1 is proved, not an input. -/
theorem lemma_15_3_63
    {V M Mc : Subgroup G} [IsElementaryAbelian 2 V] {z : G}
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hzV : z ∈ V) (hz : z ≠ 1) (hzs : d.singular ⟨z, hzV⟩)
    (hMc : Mc = centralizer (zpowers z : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ m ∈ M, MulAut.conj m z = MulAut.conj a z)
    (hsingular : ∀ g : G, g ∉ M →
      ∀ x : ↥(V ⊓ V.map (MulAut.conj g).toMonoidHom),
        d.singular ⟨x, x.property.1⟩)
    [IsMulCommutative (conjugateSpanBy V Mc)]
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hzero : indexedWeakClosure V T 0 ≤ centralizer (V : Set G))
    (ha : localA V = 1) (hgen : GenerationContainmentInput V T M)
    (hr : (3 : ℕ∞) ≤ globalR V) :
    indexedWeakClosure V T 1 ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      1 < globalW V T ∧
      ∀ H ∈ sylowOutsideFamily T M, 1 < generationParameter H := by
  obtain ⟨hW, hw⟩ := lemma_15_3_63_1 d hzV hz hzs hMc hfusion hsingular T hTM hzero ha hr
  exact ⟨hW, hw, fun _ hH => lemma_15_3_63_2_of_generation_containment hgen hr hw hH⟩

/-- The final numerical step in 15.3.65: a genuine nonempty outside family
has a minimal member, and its n=1 rules out r≥3, including r=infinity. -/
theorem globalR_eq_two_of_minimal_generation_one
    {V M : Subgroup G} {T : Sylow 2 G}
    (hr : (2 : ℕ∞) ≤ globalR V)
    (hne : (sylowOutsideFamily T M).Nonempty)
    (hlarge : (3 : ℕ∞) ≤ globalR V →
      ∀ H ∈ sylowOutsideFamily T M, 1 < generationParameter H)
    (hminimal : ∀ H ∈ minimalSylowOutsideFamily T M, generationParameter H = 1) :
    globalR V = 2 := by
  obtain ⟨H, hH⟩ := (Set.toFinite (sylowOutsideFamily T M)).exists_minimal hne
  have hn := hminimal H hH
  have hnot : ¬ (3 : ℕ∞) ≤ globalR V := by
    intro h3
    have hh := hlarge h3 H hH.prop
    omega
  have hle : globalR V ≤ 2 := by
    exact le_of_not_gt (fun hh => hnot ((ENat.add_one_le_iff (by norm_num)).mpr hh))
  exact le_antisymm hle hr

omit [Finite G] in
/-- The arithmetic restriction used on p.1152. The torus divisibility must be
proved in the actual E.2.2 Borel; the exponent here is not n(H). -/
theorem odd_field_exponent_of_three_prime_intersection
    {M H : Subgroup G} {f : ℕ}
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G))
    (htorus : 2 ^ f - 1 ∣ Nat.card (M ⊓ H : Subgroup G)) : Odd f := by
  by_contra hn
  have he : Even f := Nat.not_odd_iff_even.mp hn
  obtain ⟨k, hk⟩ := he
  have hf : f = 2 * k := by omega
  have hp : (2 ^ f) % 3 = 1 := by
    rw [hf, pow_mul, Nat.pow_mod]
    norm_num
  have hpos : 0 < 2 ^ f := pow_pos (by decide) _
  have hd : 3 ∣ 2 ^ f - 1 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  exact hthree (hd.trans htorus)

/-- The representation interface shared by 15.3.64 and 15.3.65. The actor is
literally H/O₂(H), the space is literally U/Z, and the formula specifies the
conjugation action on every quotient representative. Faithfulness is the
15.3.48(3) conclusion, not an abstract model identification. -/
structure LocalQuotientAction (H U Z : Subgroup G)
    [IsElementaryAbelian 2 U] where
  kernel_le : Z ≤ U
  le_local : U ≤ H
  normalizes : H ≤ normalizer (U : Set G)
  representation : Representation (ZMod 2) (H ⧸ pCore 2 H)
    (Additive (U ⧸ Z.subgroupOf U))
  conjugation : ∀ (h : H) (u : U),
    representation (QuotientGroup.mk' (pCore 2 H) h)
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(h : G) * u * (h : G)⁻¹, (normalizes h.property u).mp u.property⟩)
  faithful : Function.Injective representation

omit [Finite G] in
/-- Independently constructed actions agree on the literal quotient module,
so the module-bound and component arguments can share their representation. -/
theorem LocalQuotientAction.representation_eq {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a b : LocalQuotientAction H U Z) : a.representation = b.representation := by
  apply MonoidHom.ext
  intro hq
  apply LinearMap.ext
  intro u
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) hq
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) u.toMul
  have hv' : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) v) = u :=
    congrArg Additive.ofMul hv
  rw [← hv', a.conjugation, b.conjugation]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
