module

public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.DihedralRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.Fusion
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.SemidihedralLocal
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.SemidihedralRecognition

/-!
# Small Sylow two-subgroups in even characteristic

The dihedral branch of I.4.3 follows from the actual central involution
centralizer and the single involution class, followed by I.4.1. Its small
exceptional models are transported to the source's Fermat/Mersenne list.
The semidihedral branch identifies the centralizer’s quaternion core, full
automorphism action, and characteristic SL₂(3) residual. The actual GL₂(3)
model and I.4.2 give both source alternatives.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma I.4.3, printed pp.416–417.
-/

namespace CFSG.Quasithin.ChapterI

/-- I.4.3(1), for the original finite group without a subgroup of index two.
The conclusion retains actual classical matrix models, including PSL₂(3). -/
public theorem lemma_I_4_3_1
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ N : Subgroup G, N.index ≠ 2) (hE : IsEvenCharacteristic G)
    (T : Sylow 2 G) (hT : Stellmacher.IsDihedralGroup T) :
    Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL G 2 p := by
  rcases SmallSylow.dihedral_recognition hno hE T hT with h | ⟨p, hp, he⟩
  · exact Or.inl h
  · let : Fact p.Prime := ⟨hp.1⟩
    exact Or.inr ⟨p, hp, ZMod p, inferInstance, inferInstance, Nat.card_zmod p, he⟩

/-- The Sylow-order conclusion in the proof of I.4.3(2), with only its
original finite-group, even-characteristic and no-index-two hypotheses. -/
public theorem lemma_I_4_3_2_sylow_card
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ N : Subgroup G, N.index ≠ 2) (hE : IsEvenCharacteristic G)
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T) :
    Nat.card T = 16 :=
  SemidihedralLocal.sylow_card_sixteen T (hE T) (fun N _ => hno N) hT

/-- I.4.3(2), for the original finite group without a subgroup of index two. -/
public theorem lemma_I_4_3_2
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ N : Subgroup G, N.index ≠ 2) (hE : IsEvenCharacteristic G)
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T) :
    ClassicalGroup.IsPSL G 3 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11) :=
  SmallSylow.semidihedral_recognition (fun N _ => hno N) hE T hT

end CFSG.Quasithin.ChapterI
