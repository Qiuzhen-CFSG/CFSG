module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTerminal
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Aligning the pure commutator line with the original Sylow subgroup

For a subgroup Z of the source orbit W, Thompson control places a Sylow
subgroup of C_G(Z) containing J(T) inside the original normalizer M.
Sylow conjugacy inside M then aligns it with T. This gives a conjugate
line whose literal T-centralizer is Sylow in its full ambient centralizer.

Conjugation by an element of N_G(W) preserves the offender condition and
transports both normalizer hyperplanes of its symmetric pair. The Chapter12
application consequently aligns the pure line and its actual offender
together, rather than asserting Sylow placement for an arbitrary line.
Source: Aschbacher–Smith 3.2.10(4,8) and 7.6.1, printed pp.583,702,
refs/quasithin.pdf. Conjugation is the project's left-conjugation convention.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureSylow
open Subgroup Stellmacher ChapterE
open Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_map (Z : Subgroup G) (e : G ≃* G) :
    (centralizer (Z : Set G)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- Thompson control aligns the centralizer Sylow by an element of the
original orbit normalizer; no Sylow claim is made for an arbitrary line. -/
theorem exists_centralizer_sylow_conjugate
    (W M : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hcontrol : ∀ R : Subgroup G, IsPGroup 2 R →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ R → normalizer (R : Set G) ≤ M)
    (Z : Subgroup G) (hZW : Z ≤ W) :
    ∃ m ∈ M, ∃ S : Sylow 2 (centralizer (Z.map (MulAut.conj m).toMonoidHom : Set G)),
      (S : Subgroup _).map (centralizer (Z.map (MulAut.conj m).toMonoidHom : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z.map (MulAut.conj m).toMonoidHom : Set G) := by
  let C := centralizer (Z : Set G)
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJC : J ≤ C := hJ.trans (centralizer_le hZW)
  obtain ⟨P,hJP⟩ := ((T.isPGroup'.to_le hJT).comap_subtype (K := C)).exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  have hJR : J ≤ R := by
    intro x hx
    exact mem_map_of_mem C.subtype (hJP (show (⟨x,hJC hx⟩ : C) ∈ J.subgroupOf C from hx))
  have hRM : R ≤ M := R.le_normalizer.trans (hcontrol R (P.isPGroup'.map _) hJR)
  obtain ⟨A,hRA⟩ := ((P.isPGroup'.map C.subtype).comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq M A (T.subtype hTM)
  let e := MulAut.conj (m : G)
  have hRT : R.map e.toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : (MulAut.conj m) (⟨x,hRM hx⟩ : M) ∈ (T.subtype hTM : Subgroup M) := by
      rw [←hm]
      exact mem_map_of_mem (MulAut.conj m).toMonoidHom (hRA hx)
    exact hh
  let C' := centralizer (Z.map e.toMonoidHom : Set G)
  let f : C ≃* C' := (C.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (centralizer_map Z e))
  let S := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hS : (S : Subgroup C').map C'.subtype = R.map e.toMonoidHom := by
    change ((P : Subgroup C).map f.toMonoidHom).map C'.subtype = _
    rw [map_map,map_map]
    rfl
  exact ⟨m,m.property,S,(inf_eq_sylow_map S T.isPGroup' (hS.trans_le hRT)).symm⟩

omit [Finite G] in
private theorem map_conj_mul (W : Subgroup G) (m g : G) :
    W.map (MulAut.conj (m*g)).toMonoidHom =
      (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev,mul_assoc]

omit [Finite G] in
/-- Normalizer conjugation keeps the literal offender and its corank. -/
theorem offender_normalizer_transport
    (W : Subgroup G) (m g : G) (hm : m ∈ normalizer (W : Set G)) :
    (offenderNormalizer W g).map (MulAut.conj m).toMonoidHom = offenderNormalizer W (m*g) := by
  have hW : W.map (MulAut.conj m).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hm
  rw [offenderNormalizer,offenderNormalizer,map_inf _ _ _ (MulAut.conj m).injective,
    map_equiv_normalizer_eq,hW,map_conj_mul]

omit [Finite G] in
/-- Conjugating the entire pair inside N(W) preserves the same weak-closure minimum. -/
theorem offenderAt_normalizer_transport
    (W T : Subgroup G) (m g : G) (hm : m ∈ normalizer (W : Set G))
    (hg : IsWOffenderAt W T g) : IsWOffenderAt W T (m*g) := by
  have hW : W.map (MulAut.conj m).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hm
  constructor
  · intro he
    have hmap : (⁅W,W.map (MulAut.conj g).toMonoidHom⁆).map
        (MulAut.conj m).toMonoidHom = ⊥ := by
      rw [map_commutator,hW,←map_conj_mul,he]
    exact hg.1 ((map_eq_bot_iff_of_injective _ (MulAut.conj m).injective).mp hmap)
  · have hi := relIndex_map_map_of_injective (offenderNormalizer W g)
      (W.map (MulAut.conj g).toMonoidHom) (f := (MulAut.conj m).toMonoidHom)
      (MulAut.conj m).injective
    rw [offender_normalizer_transport W m g hm,←map_conj_mul] at hi
    change globalW W T = (Nat.log 2 _ : ℕ∞)
    rw [hi]
    exact hg.2

omit [Finite G] in
/-- For the symmetric pair, both literal normalizer hyperplanes transport together. -/
theorem pair_commutator_transport
    (W : Subgroup G) (m g : G) (hm : m ∈ normalizer (W : Set G)) :
    (⁅offenderNormalizer W g,W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)⁆).map
        (MulAut.conj m).toMonoidHom =
      ⁅offenderNormalizer W (m*g),W ⊓ normalizer (W.map (MulAut.conj (m*g)).toMonoidHom : Set G)⁆ := by
  have hW : W.map (MulAut.conj m).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hm
  rw [map_commutator,offender_normalizer_transport W m g hm,
    map_inf _ _ _ (MulAut.conj m).injective,hW,
    map_equiv_normalizer_eq,←map_conj_mul]

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureSylow
