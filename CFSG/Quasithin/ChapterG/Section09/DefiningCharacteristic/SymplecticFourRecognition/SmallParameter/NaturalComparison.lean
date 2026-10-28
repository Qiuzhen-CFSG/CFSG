module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The alternating and symplectic binary natural modules

The four-coordinate map below kills the constant vector in the six-letter
permutation module and has precisely that kernel on the augmentation core.
Its induced linear equivalence sends each duad class to the corresponding
vector in the existing polar table. Equivariance on the fifteen nonzero
vectors then identifies the deleted alternating action with the natural
action of the literal commutator subgroup of Sp₄(2).

Twisting the alternating action by a genuine automorphism preserves this
quasiequivalence. Field transport treats every two-element field. These
are comparisons of concrete modules, not a classification of arbitrary
four-dimensional representations.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.3.1,
I.5.4 and G.9.3(9), printed pp.83,354,356--357,420.
-/

public section

open scoped Matrix
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter

private def encode : Full (Fin 6) →ₗ[ZMod 2] NaturalModule where
  toFun v := vec (v 4 + v 5) (v 2 + v 3 + v 4 + v 5)
    (v 3 + v 5) (v 1 + v 3 + v 4 + v 5)
  map_add' v w := by ext i; rcases i with i | i <;> fin_cases i <;> simp [vec] <;> ring
  map_smul' c v := by ext i; rcases i with i | i <;> fin_cases i <;> simp [vec, mul_add]

private theorem constants_le_kernel : constants (Fin 6) ≤ LinearMap.ker encode := by
  rw [constants, Submodule.span_le, Set.singleton_subset_iff]
  change encode (allOne (Fin 6)) = 0
  decide +kernel

private noncomputable def naturalToPolar : natural (Fin 6) →ₗ[ZMod 2] NaturalModule :=
  ((constants (Fin 6)).liftQ encode constants_le_kernel).comp (natural (Fin 6)).subtype

private theorem encode_core_kernel (v : Full (Fin 6))
    (hv : ∑ i, v i = 0) (hz : encode v = 0) : v ∈ constants (Fin 6) := by
  have h : ∀ v : Full (Fin 6), (∑ i, v i) = 0 → encode v = 0 →
      v = v 0 • allOne (Fin 6) := by decide +kernel
  rw [h v hv hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem naturalToPolar_injective : Function.Injective naturalToPolar := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  obtain ⟨u, hu, he⟩ := v.property
  change v = 0
  apply Subtype.ext
  change v.val = 0
  rw [← he]
  apply (Submodule.Quotient.mk_eq_zero (constants (Fin 6))).mpr
  apply encode_core_kernel u hu
  change (constants (Fin 6)).liftQ encode constants_le_kernel v.val = 0 at hv
  rw [← he] at hv
  exact hv

private theorem naturalToPolar_bijective : Function.Bijective naturalToPolar := by
  refine ⟨naturalToPolar_injective, ?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj naturalToPolar_injective,
    finrank_natural_even (Fin 6) (by decide)]
  simp [NaturalModule]

/-- The explicit coordinate equivalence from the deleted module to the polar module. -/
noncomputable def naturalPolarEquiv : natural (Fin 6) ≃ₗ[ZMod 2] NaturalModule :=
  LinearEquiv.ofBijective naturalToPolar naturalToPolar_bijective

private theorem pair_encode (i j : Fin 6) (d : Theory.SpecificGroups.SymmetricSix.Duad)
    (hd : duadSet d = pair i j) :
    naturalPolarEquiv (pairVector i j) = (polarVector d).val := by
  change encode (Pi.single i 1 + Pi.single j 1) = (polarVector d).val
  decide +revert +kernel

/-- The coordinate equivalence intertwines the full symmetric action. -/
theorem naturalPolarEquiv_equivariant (g : S6) (v : natural (Fin 6)) :
    naturalPolarEquiv (naturalRepresentation (Fin 6) g v) =
      polarAction g (naturalPolarEquiv v) := by
  rcases vector_cases v with rfl | ⟨d, rfl⟩
  · simp
  · obtain ⟨e, he⟩ := duadSet_complete (pair d.val.1 d.val.2)
      (by simp [pair, ne_of_lt d.property])
    change naturalPolarEquiv (naturalRepresentation (Fin 6) g
      (pairVector d.val.1 d.val.2)) =
        polarAction g (naturalPolarEquiv (pairVector d.val.1 d.val.2))
    rw [pairVector_map, pair_encode _ _ e he]
    have hge : duadSet (g • e) = pair (g d.val.1) (g d.val.2) := by
      rw [duadSet_smul, he]
      simp [pair]
    rw [pair_encode _ _ (g • e) hge]
    exact (polarAction_vector g e).symm

open Theory.SpecificGroups.SymplecticFour.Binary
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition

/-- Restriction of the polar group equivalence to the actual commutator subgroup. -/
noncomputable def alternatingToDerived : A6 ≃*
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  ((symmetricSixEquiv.symm.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr symmetricSixEquiv.symm.surjective]
    exact alternatingGroup.commutator_perm_eq (by norm_num)))).symm

/-- The restricted group equivalence retains the original polar matrices. -/
theorem alternatingToDerived_coe (g : A6) :
    (alternatingToDerived g).val = polarRepresentation g.val := by
  change symmetricSixEquiv g.val = polarRepresentation g.val
  exact symmetricSixEquiv_apply g.val

/-- Actual group and linear equivalences identify the two natural models. -/
theorem alternatingNatural_quasiequivalent :
    Quasiequivalent (alternatingNaturalRepresentation (Fin 6))
      (binaryNatural (ZMod 2)) := by
  refine ⟨alternatingToDerived, naturalPolarEquiv, ?_⟩
  intro g v
  change naturalPolarEquiv (naturalRepresentation (Fin 6) g.val v) = _
  rw [naturalPolarEquiv_equivariant]
  change polarAction g.val (naturalPolarEquiv v) =
    (alternatingToDerived g).val.val *ᵥ naturalPolarEquiv v
  rw [alternatingToDerived_coe]
  exact (polarRepresentation_apply g.val _).symm

/-- Any automorphic twist, including an exceptional outer twist, has the same
quasiequivalence class; the twisting automorphism is retained in the witness. -/
theorem alternatingNatural_twist_quasiequivalent (α : MulAut A6) :
    Quasiequivalent ((alternatingNaturalRepresentation (Fin 6)).comp α.toMonoidHom)
      (binaryNatural (ZMod 2)) := by
  obtain ⟨e, f, hf⟩ := alternatingNatural_quasiequivalent
  exact ⟨α.trans e, f, fun g v => hf (α g) v⟩

/-- A recognition in the six-letter model yields the specified matrix model
over any field with two elements. -/
theorem quasiequivalent_binaryNatural_of_alternatingNatural
    {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) D V} (hF : Nat.card F = 2)
    (hρ : Quasiequivalent ρ (alternatingNaturalRepresentation (Fin 6))) :
    Quasiequivalent ρ (binaryNatural F) := by
  apply (quasiequivalent_natural_binary_iff hF).mpr
  obtain ⟨a, b, hb⟩ := hρ
  obtain ⟨e, f, hf⟩ := alternatingNatural_quasiequivalent
  refine ⟨a.trans e, b.trans f, ?_⟩
  intro g v
  exact (congrArg f (hb g v)).trans (hf (a g) (b v))

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter
