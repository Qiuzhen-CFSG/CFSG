module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The original two conjugate spans in 14.7.72

Here S = ⟨Uᴸ⟩ and R = ⟨U₀ᴸ⟩ use the original fixed-space preimage U₀.
The original natural marking makes the conjugates of the flag point generate V,
so V ≤ R ≤ S. Simultaneous normalization of the seeds and L gives normalization
of both spans by T. No containment of a normalized subgroup in its actor is used.

Source: Aschbacher–Smith, proof of 14.7.72, printed pp.1075–1076,
combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original U-generated subgroup, before its identification with O₂(L). -/
@[expose] def S (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G :=
  conjugateSpanBy F.U L

/-- The original fixed-kernel span, before its identification with V. -/
@[expose] noncomputable def R (d : Data T L V F W) : Subgroup G := conjugateSpanBy d.U₀ L

variable (d : Data T L V F W)

omit [Finite G] in
theorem U_le_S : F.U ≤ S F L := le_conjugateSpanBy _ _

theorem U₀_le_R : d.U₀ ≤ R d := le_conjugateSpanBy _ _

theorem R_le_S : R d ≤ S F L := conjugateSpanBy_mono d.U₀_le_U le_rfl

omit [Finite G] in
theorem L_normalizes_S : L ≤ normalizer (S F L : Set G) :=
  le_normalizer_conjugateSpanBy _ _

theorem L_normalizes_R : L ≤ normalizer (R d : Set G) :=
  le_normalizer_conjugateSpanBy _ _

include d in
/-- The natural marking, including its actual qL, generates V from V₁. -/
theorem point_span : conjugateSpanBy (F.Vi 1) L = V := by
  apply le_antisymm (conjugateSpanBy_le (F.le_seed 1) d.natural.chosen.normalizes)
  intro v hv
  by_cases hv1 : v = 1
  · exact hv1 ▸ (conjugateSpanBy (F.Vi 1) L).one_mem
  have hzP : d.z ∈ F.Vi 1 := by rw [d.point]; exact mem_zpowers d.z
  let zV : V := ⟨d.z, F.le_seed 1 hzP⟩
  let vV : V := ⟨v, hv⟩
  have hz : (d.naturalCoordinates zV).toAdd ≠ 0 := by
    intro h
    have he : d.naturalCoordinates zV = d.naturalCoordinates 1 :=
      h.trans d.naturalCoordinates.map_one.symm
    exact d.z_ne_one (congrArg Subtype.val (d.naturalCoordinates_bijective.1 he))
  have hv' : (d.naturalCoordinates vV).toAdd ≠ 0 := by
    intro h
    have he : d.naturalCoordinates vV = d.naturalCoordinates 1 :=
      h.trans d.naturalCoordinates.map_one.symm
    exact hv1 (congrArg Subtype.val (d.naturalCoordinates_bijective.1 he))
  obtain ⟨g,hg⟩ := BinaryLinearThree.natural_transitive_nonzero _ _ hz hv'
  obtain ⟨l,hl⟩ := d.qL_surjective g
  have he := d.naturalCoordinates_equivariant l zV
  rw [hl, hg] at he
  have he' := d.naturalCoordinates_bijective.1 (Multiplicative.toAdd.injective he)
  exact subset_closure ⟨l,l.property,d.z,hzP,congrArg Subtype.val he'⟩

theorem V_le_R : V ≤ R d := by
  exact (point_span d).symm.le.trans (conjugateSpanBy_mono d.point_le_U₀ le_rfl)

include d in
/-- In particular the point cannot be invariant under all of L. -/
theorem not_L_normalizes_point : ¬ L ≤ normalizer (F.Vi 1 : Set G) := by
  intro h
  have hVP : V ≤ F.Vi 1 := (point_span d).symm.le.trans (conjugateSpanBy_le le_rfl h)
  have hc := card_le_of_le hVP
  have hV : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  omega

include d in
/-- A subgroup of the point normalized by L must vanish. -/
theorem eq_bot_of_normalized_le_point (A : Subgroup G)
    (hA : A ≤ F.Vi 1) (hLA : L ≤ normalizer (A : Set G)) : A = ⊥ := by
  by_contra hn
  have hc : Nat.card A ≠ 1 := fun h => hn (card_eq_one.mp h)
  have hp : 0 < Nat.card A := Nat.card_pos
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have he : A = F.Vi 1 := eq_of_le_of_card_ge hA (by omega)
  exact not_L_normalizes_point d (he ▸ hLA)

omit [Finite G] in
private theorem normalizes_span (A B N : Subgroup G)
    (hNA : N ≤ normalizer (A : Set G)) (hNB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer (conjugateSpanBy A B : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq, map_conjugateSpanBy,
    mem_normalizer_iff_map_conj_eq.mp (hNA hn),
    mem_normalizer_iff_map_conj_eq.mp (hNB hn)]

include d in
theorem T_normalizes_S (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (S F L : Set G) :=
  normalizes_span F.U L (T : Subgroup G)
    ((F.invariant 1).trans d.conjugationSection.normalized) hTL

theorem T_normalizes_R (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (R d : Set G) :=
  normalizes_span d.U₀ L (T : Subgroup G)
    ((F.invariant 1).trans d.H_normalizes_U₀) hTL

/-- An actual Steinberg identification of S/V for the same original qL.
Unlike `BinaryConjugationSection`, these coordinates require only normalization:
S ≤ L is not assumed before the double-cover argument proves S = O₂(L). -/
structure SteinbergCoordinates where
  coordinates : S F L →* Multiplicative BinaryLinearThree.Steinberg
  onto : Function.Surjective coordinates
  kernel_eq : coordinates.ker = V.subgroupOf (S F L)
  equivariant (l : L) (a : S F L) :
    (coordinates ⟨l * a * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_S l.property) a).mp a.property⟩).toAdd =
      BinaryLinearThree.S (d.qL l) (coordinates a).toAdd

namespace SteinbergCoordinates
variable {d} (c : SteinbergCoordinates d)

theorem coordinates_eq_one_iff (a : S F L) :
    c.coordinates a = 1 ↔ (a : G) ∈ V := by
  change a ∈ c.coordinates.ker ↔ _
  rw [c.kernel_eq]
  rfl

include c in
theorem kernel_normal : (V.subgroupOf (S F L)).Normal := by
  rw [← c.kernel_eq]
  infer_instance

/-- After actual containment is proved, these coordinates give the literal
section used by the Ru1 constructor. -/
@[expose] noncomputable def toSection (hSL : S F L ≤ L) :
    BinaryConjugationSection L (S F L) V (BinaryLinearThree.S.comp d.qL) where
  section_le := hSL
  kernel_le := (V_le_R d).trans (R_le_S d)
  normalized := L_normalizes_S
  coordinates := c.coordinates
  onto := c.onto
  kernel_eq := c.kernel_eq
  equivariant := c.equivariant

private noncomputable def quotientEquivOfKernel {A B : Type*} [Group A] [Group B]
    (f : A →* B) (N : Subgroup A) [N.Normal]
    (hk : f.ker = N) (hf : Function.Surjective f) : (A ⧸ N) ≃* B :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- An isomorphism of the literal S/V quotient with the Steinberg carrier. -/
noncomputable def quotientEquiv [(V.subgroupOf (S F L)).Normal] :
    (S F L ⧸ V.subgroupOf (S F L)) ≃* Multiplicative BinaryLinearThree.Steinberg :=
  quotientEquivOfKernel (A := S F L) (B := Multiplicative BinaryLinearThree.Steinberg)
    c.coordinates (V.subgroupOf (S F L)) c.kernel_eq c.onto

/-- The quotient equivalence retains the original coordinate map on representatives. -/
theorem quotientEquiv_mk [(V.subgroupOf (S F L)).Normal] (a : S F L) :
    c.quotientEquiv (QuotientGroup.mk' (V.subgroupOf (S F L)) a) = c.coordinates a := by
  unfold quotientEquiv quotientEquivOfKernel
  rfl

end SteinbergCoordinates

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
