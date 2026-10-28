module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Seed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction

/-!
# Model exclusions and full automorphism quotients for the invariant sieve

The actual D₈ automizer excludes the cyclic symplectic row. The proved
PSL₃(3) and M₁₁ Sylow-pair calculations exclude those rows as well. For
PSL₄(2) and PSL₅(2), the inner-pair invariant forces a genuinely outer
actor; inner/graph coverage gives the full automorphism image, and the
conjugation kernel is the literal two-core of IT. Coefficient transport
identifies its target with the specified projective group over ZMod 2.

These local results are reused from the Chapter 15 development. Their
hypotheses are intrinsic local/Sylow data and they have no Chapter 10
source dependency. No global Chapter 15 theorem is used here.

Source: Aschbacher--Smith, 10.2.4, printed p.747, and 1.3.4, pp.509--511.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant
open Chapter1 Chapter1.XiEmbedding
open Chapter15.Section04.LocalSetup.EmbeddingReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem binary_model_equiv {Q : Type*} [Group Q] {k : ℕ}
    (hm : ClassicalGroup.IsPSL Q k 2) :
    Nonempty (Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin k) (ZMod 2)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv f.symm)⟩

/-- Sieve the intrinsic alternatives using the actual dihedral automizer,
then identify the literal join quotient with the full binary automorphism group. -/
theorem models_of_dihedral {X P H I : Subgroup G}
    (h : LocalInput 3 (T : Subgroup G) X P H)
    (hIH : I ≤ H) (hn : (I.subgroupOf H).Normal)
    (hi : (T : Subgroup G) ≤ normalizer I) (hX : X ≤ I)
    (hD : Nonempty (automizer (T : Subgroup G) P ≃* DihedralGroup 4))
    (ha : Alternatives 3 (T : Subgroup G) P I) :
    ∃ k : ℕ, (k = 4 ∨ k = 5) ∧ ClassicalGroup.IsPSL (XiQuotient I) k 2 ∧
      Nonempty (XiQuotient (I ⊔ (T : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin k) (ZMod 2))) := by
  have hT := sylowIn_overgroup (le_sup_right.trans h.overgroup)
  have hsmall := SmallModels.not_linearThreeModel h hT hIH hn hX hD
  have hmathieu := SmallModels.not_mathieuEleven h hT hIH hn hX hD
  have hm : ClassicalGroup.IsPSL (XiQuotient I) 4 2 ∨
      ClassicalGroup.IsPSL (XiQuotient I) 5 2 := by
    rcases (alternatives_of_dihedral ha hD).2 with hs | ⟨_, hl | he⟩
    · exact (hs.1.1 hi).elim
    · exact (hsmall hl).elim
    · exact he.resolve_left hmathieu
  have hex : ∃ k : ℕ, (k = 4 ∨ k = 5) ∧ ClassicalGroup.IsPSL (XiQuotient I) k 2 := by
    rcases hm with hm | hm
    · exact ⟨4,Or.inl rfl,hm⟩
    · exact ⟨5,Or.inr rfl,hm⟩
  obtain ⟨k,hk,hm⟩ := hex
  obtain ⟨a⟩ := BinaryAction.binary_quotient_aut_of_local h hT hIH hn hX hk hm
  obtain ⟨e⟩ := binary_model_equiv hm
  exact ⟨k,hk,hm,⟨a.trans (MulAut.congr e)⟩⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant
