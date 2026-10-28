module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.Frames
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.NormCharacter

/-!
# Homogeneous Cayley generators with normalized norms

Every elementary eight in the actual ternary octonion automorphism group has
homogeneous imaginary generators of norms `1,1,±1`. Finite character duality
makes its character group an elementary eight. The norm homomorphism has image
of order at most two, hence kernel of order at least four. Choose two distinct
nonidentity characters in this kernel and a third outside their four-element
subgroup. These are the basis-selection facts needed for the construction.

Nonisotropic vectors in the three character lines have the required norms.
Distinct characters give zero traces and all four orthogonality conditions;
multiplication gives homogeneity of the entire parenthesized frame. This uses
neither an arbitrary-triple multiplication table nor subgroup conjugacy.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482. The recognition configuration
in §I.4, printed p.417, is not itself a conjugacy or coverage theorem. The
split-octonion coordinates and norm follow the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
open Atlas.SplitOctonion
open scoped IsMulCommutative

private theorem dual_card (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : Nat.card (Character E) = 8 := by
  let : HasEnoughRootsOfUnity (ZMod 3) 2 :=
    { prim := ⟨-1, IsPrimitiveRoot.neg_one 3 (by decide)⟩
      cyc := rootsOfUnity.isCyclic (ZMod 3) 2 }
  let : HasEnoughRootsOfUnity (ZMod 3) (Monoid.exponent E) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 3) (IsElementaryAbelian.exponent_dvd_p 2 E)
  exact (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity E (ZMod 3)).trans hE

private theorem norm_kernel_card (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : 4 ≤ Nat.card (lineNorm E hE).ker := by
  have hcard := (lineNorm E hE).ker.card_mul_index
  rw [Subgroup.index_ker, dual_card E hE] at hcard
  have hbound := (lineNorm E hE).range.card_le_card_group
  have hu : Nat.card (ZMod 3)ˣ = 2 := by rw [Nat.card_units, Nat.card_zmod]
  rw [hu] at hbound
  nlinarith

private theorem exists_outside {T : Type*} [Finite T] (s : Finset T)
    (hs : s.card < Nat.card T) : ∃ t, t ∉ s := by
  classical
  let := Fintype.ofFinite T
  have hlt : s.card < (Finset.univ : Finset T).card := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hs
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨t, ht⟩

private theorem normalized_characters (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) :
    ∃ χ ψ ξ : Character E,
      lineNorm E hE χ = 1 ∧ lineNorm E hE ψ = 1 ∧
      χ ≠ 1 ∧ ψ ≠ 1 ∧ ξ ≠ 1 ∧ χ ≠ ψ ∧ χ ≠ ξ ∧ ψ ≠ ξ ∧ χ * ψ ≠ ξ := by
  classical
  let K := (lineNorm E hE).ker
  have hK : 4 ≤ Nat.card K := norm_kernel_card E hE
  obtain ⟨χ, hχ⟩ := exists_outside ({1} : Finset K) (by simp; omega)
  have hχ1 : χ ≠ 1 := by simpa only [Finset.mem_singleton] using hχ
  obtain ⟨ψ, hψ⟩ := exists_outside ({1, χ} : Finset K)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hψχ : ψ ≠ χ := fun h => hψ (by simp [h])
  obtain ⟨ξ, hξ⟩ := exists_outside
    ({1, χ.val, ψ.val, χ.val * ψ.val} : Finset (Character E))
    (lt_of_le_of_lt Finset.card_le_four (by rw [dual_card E hE]; decide))
  refine ⟨χ.val, ψ.val, ξ, χ.property, ψ.property,
    (fun h => hχ1 (Subtype.ext h)), (fun h => hψ1 (Subtype.ext h)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hξ (by simp [h])
  · intro h; exact hψχ (Subtype.ext h.symm)
  · intro h; exact hξ (by simp [← h])
  · intro h; exact hξ (by simp [← h])
  · intro h; exact hξ (by simp [← h])

/-- The norm character selects homogeneous imaginary generators of norms one,
one and one of the two nonzero ternary scalars. -/
theorem exists_normalized_homogeneous_triple (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : ∃ (k : Bool) (a b c : V),
      IsCayleyTriple (referenceNorm k) a b c ∧
      ∀ i, ∃ χ : Character E, frame a b c i ∈ characterSpace E χ := by
  obtain ⟨χ, ψ, ξ, hχn, hψn, hχ1, hψ1, hξ1, hχψ, hχξ, hψξ, hχψξ⟩ :=
    normalized_characters E hE
  obtain ⟨a, ha, han⟩ := exists_nonisotropic E χ
  obtain ⟨b, hb, hbn⟩ := exists_nonisotropic E ψ
  obtain ⟨c, hc, hcn⟩ := exists_nonisotropic E ξ
  have ha0 : a ≠ 0 := by intro h; apply han; simp [h, SplitOctonion.norm]
  have hb0 : b ≠ 0 := by intro h; apply hbn; simp [h, SplitOctonion.norm]
  have hna : norm a = 1 := by rw [← lineNorm_apply E hE ha ha0, hχn]; rfl
  have hnb : norm b = 1 := by rw [← lineNorm_apply E hE hb hb0, hψn]; rfl
  obtain ⟨k, hk⟩ : ∃ k, norm c = referenceNorm k :=
    (by decide : ∀ r : ZMod 3, r ≠ 0 → ∃ k, r = referenceNorm k) (norm c) hcn
  refine ⟨k, a, b, c, ?_, frame_homogeneous ha hb hc⟩
  exact {
    trace_a := trace_eq_zero_of_character_ne_one hχ1 ha
    trace_b := trace_eq_zero_of_character_ne_one hψ1 hb
    trace_c := trace_eq_zero_of_character_ne_one hξ1 hc
    norm_a := hna
    norm_b := hnb
    norm_c := hk
    norm_c_ne := hk ▸ hcn
    polar_ab := orthogonal hχψ ha hb
    polar_ac := orthogonal hχξ ha hc
    polar_bc := orthogonal hψξ hb hc
    polar_abc := orthogonal hχψξ (mul_mem ha hb) hc }

end Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
