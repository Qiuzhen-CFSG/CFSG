module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureLine

/-!
# An actual pure-line offender with its centralizer Sylow aligned

The pure line is the whole commutator of the two original offender
hyperplanes. Thompson control puts a Sylow subgroup of its centralizer
inside N_G(L)=N_G(W). Conjugating the entire pair by an element of that
normalizer aligns the local Sylow with the original T, while retaining
W and the exact offender minimum. The commutator transport identifies the
new line with the conjugate of the old line.

The resulting witness has Z₁=[A,A₁] of order two in one of the two original
marked factors and C_T(Z₁) Sylow in C_G(Z₁). Both W and A₁ escape the full
centralizer two-core by the previously proved terminal argument. To finish
7.6.1 one still needs source 7.7.2 for this pure line, the quotient fixed-space
and irreducibility argument placing A₁ in that core, and the original w≤1
bound. No characteristic-two property of an arbitrary involution centralizer
is assumed here.
Source: Aschbacher–Smith 3.2.10(4,8), H.4.3(2) and 7.6.1,
printed pp.380,583,702–703, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- A simultaneous normalizer conjugation of the actual pair gives the
source pure commutator line with its literal centralizer Sylow placement. -/
theorem sourceOrbit_binary_exists_sylow_pureLine_core_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) ∧
        (∃ S : Sylow 2 (centralizer (Z : Set G)),
          (S : Subgroup _).map (centralizer (Z : Set G)).subtype =
            (T : Subgroup G) ⊓ centralizer (Z : Set G)) ∧
        ¬ D.sourceOrbit ≤ (centralizer (Z : Set G)).pCoreIn 2 ∧
        ¬ offenderFixedSpan D.sourceOrbit g ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,_,_⟩ :=
    D.sourceOrbit_binary_exists_pureLine_core_obstruction h hd F hF hmodel hnon hw
  let W := D.sourceOrbit
  let Z := ⁅offenderNormalizer W g,offenderFixedSpan W g⁆
  obtain ⟨m,hm,S,hS⟩ := DoubledBinaryPureSylow.exists_centralizer_sylow_conjugate
    W (normalizer (L : Set G)) T D.sylow_normalizes_component
    (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
    (fun R hp hJR => ((D.sourceOrbit_nonFF_thompson_normalizers h hnon).2 R hp hJR).2)
    Z (hpair.trans inf_le_left)
  have hmW : m ∈ normalizer (W : Set G) := by
    rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
  have hmg := DoubledBinaryPureSylow.offenderAt_normalizer_transport W T m g hmW hg
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨_,_,_,hB,_⟩ := D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  obtain ⟨_,_,_,hB',_⟩ := D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hmg
  let Z' := ⁅offenderNormalizer W (m*g),offenderFixedSpan W (m*g)⁆
  have he : Z.map (MulAut.conj m).toMonoidHom = Z' := by
    dsimp only [Z,Z',W]
    rw [hB,hB']
    exact DoubledBinaryPureSylow.pair_commutator_transport W m g hmW
  have hSyl : ∃ P : Sylow 2 (centralizer (Z' : Set G)),
      (P : Subgroup _).map (centralizer (Z' : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z' : Set G) := by
    rw [←he]
    exact ⟨S,hS⟩
  obtain ⟨t',ht',hnt',hZ',hpure',hpair',hcentral'⟩ :=
    D.sourceOrbit_binary_offender_pure_commutator h hd F hF hmodel hnon hw hmg
  exact ⟨m*g,hmg,t',ht',hnt',hZ',hpure',hpair',hcentral',hSyl,
    D.sourceOrbit_binary_not_le_sharedLine_core h hd F hF hmodel hnon hw hmg
      (hpair'.trans inf_le_left) hZ' (hpair'.trans inf_le_right),
    fun hcore => D.sourceOrbit_binary_false_of_sharedLine_hyperplane_core
      h hd F hF hmodel hnon hw hmg (hpair'.trans inf_le_left) hZ' (hpair'.trans inf_le_right) hcore⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
