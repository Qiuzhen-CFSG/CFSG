module

public import BenderSuzuki.SE.Basic
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# Strongly embedded subgroups in a concrete Suzuki group

The ovoid action makes the standard Borel maximal. A strongly embedded
subgroup contains an ambient Sylow two-subgroup and its normalizer.
Aligning that Sylow subgroup with the concrete root group therefore identifies
the original subgroup with the image of the standard Borel under an actual
multiplicative equivalence. No subgroup-classification theorem is needed.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2 and its Borel argument;
Huppert--Blackburn, Finite Groups III, XI.3.3, for the concrete ovoid.
-/

noncomputable section
open BenderSuzuki Subgroup PFAppendixIII PFchapter1section1

namespace BenderSuzuki.MatrixGroups

public theorem suzukiBorelSubgroup_isCoatom (m : ℕ) (hm : 0 < m) :
    IsCoatom (SuzukiBorelSubgroup m) := by
  let : MulAction.IsPreprimitive (SuzukiMatrixGroup m) (SuzukiOvoid m) :=
    MulAction.isPreprimitive_of_is_two_pretransitive inferInstance
  rw [suzukiBorelSubgroup_eq_stabilizer m hm]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ _

private theorem aligned_root_equiv {H : Type*} [Group H] [Finite H] {m : ℕ} (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (S : Sylow 2 H) :
    ∃ f : SuzukiMatrixGroup m ≃* H,
      (SuzukiRootSubgroup m).map f.toMonoidHom = (S : Subgroup H) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  let P' : Sylow 2 H := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' S
  refine ⟨e.symm.trans (MulAut.conj g), ?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change ((P : Subgroup (SuzukiMatrixGroup m)).map e.symm.toMonoidHom).map
    (MulAut.conj g).toMonoidHom = (S : Subgroup H) at hh
  change (SuzukiRootSubgroup m).map
    ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
  simpa only [hP, map_map] using hh

public theorem suzuki_stronglyEmbedded_eq_borel_map {H : Type*} [Group H] [Finite H] {m : ℕ} (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (M : Subgroup H) (hM : IsStronglyEmbedded M) :
    ∃ f : SuzukiMatrixGroup m ≃* H, (SuzukiBorelSubgroup m).map f.toMonoidHom = M := by
  obtain ⟨S, hSM⟩ := hM.containsSylowTwo
  obtain ⟨f, hf⟩ := aligned_root_equiv hm e S
  have heven : Even (Nat.card (SuzukiRootSubgroup m)) := by
    rw [suzukiRootSubgroup_card m hm]
    exact (even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)).pow_of_ne_zero (by decide)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := SuzukiRootSubgroup m) 2 heven.two_dvd
  have hxI : PFAppendixIII.IsInvolution (f x) := by
    apply BenderSuzuki.IsInvolution.map_of_injective _ f.toMonoidHom f.injective
    have ho : orderOf (x : SuzukiMatrixGroup m) = 2 := (Subgroup.orderOf_coe x).trans hx
    exact ⟨((orderOf_eq_prime_iff).mp ho).2, ((orderOf_eq_prime_iff).mp ho).1⟩
  have hxS : f x ∈ (S : Subgroup H) := hf ▸ mem_map_of_mem f.toMonoidHom x.property
  have hn : normalizer (S : Set H) ≤ M := by
    intro g hg
    apply hM.mem_of_involution_mem_rightConjugate (hSM hxS) _ hxI
    have hh := rightConjugateElem_mem_rightConjugate (M := M) (g := g)
      (hSM ((mem_normalizer_iff.mp hg _).mp hxS))
    simpa [rightConjugateElem, mul_assoc] using hh
  have hBM : SuzukiBorelSubgroup m ≤ M.comap f.toMonoidHom := by
    apply map_le_iff_le_comap.mp
    rw [← suzukiRootSubgroup_normalizer m hm, map_equiv_normalizer_eq, hf]
    exact hn
  have hproper : M.comap f.toMonoidHom ≠ ⊤ := by
    intro hh
    apply hM.ne_top
    have hh' := congrArg (Subgroup.map f.toMonoidHom) hh
    simpa only [map_comap_eq_self_of_surjective (f := f.toMonoidHom) f.surjective, map_top_of_surjective f.toMonoidHom f.surjective] using hh'
  have heq : SuzukiBorelSubgroup m = M.comap f.toMonoidHom :=
    ((suzukiBorelSubgroup_isCoatom m hm).le_iff_eq hproper).mp hBM |>.symm
  refine ⟨f, ?_⟩
  rw [heq, map_comap_eq_self_of_surjective (f := f.toMonoidHom) f.surjective]
end BenderSuzuki.MatrixGroups
