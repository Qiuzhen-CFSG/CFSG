module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.Sylow
public import Stellmacher.ElementaryAbelianMaxSylowImages

/-!
# Transpositions in a seven-point Thompson image

A maximum elementary subgroup with a nontrivial disjoint-transposition
image can be conjugated so that its image contains each canonical pair swap.
Kernel conjugacy places that subgroup back in the chosen Sylow subgroup
without changing its image. Every transposition in a Sylow two-subgroup
of S₇ belongs to its canonical pair group, proving the asserted containment.

Source: Aschbacher--Smith B.3.2(4), used in the completion of 12.3.1, p.812.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB.Offenders

private def pairInterchange (i : Fin 3) : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 ⟨2*i.val, by omega⟩ * Equiv.swap 1 ⟨2*i.val+1, by omega⟩

private theorem pairInterchange_first (i : Fin 3) :
    (MulAut.conj (pairInterchange i)) (pairSwap 7 0) = pairSwap 7 i := by
  revert i
  decide

private theorem pairInterchange_generators (i j : Fin 3) :
    ∃ k : Fin 3, (MulAut.conj (pairInterchange i)) (pairSwap 7 j) = pairSwap 7 k := by
  revert i j
  decide

private theorem pairInterchange_D (i : Fin 3) :
    (D 7).map (MulAut.conj (pairInterchange i)).toMonoidHom ≤ D 7 := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  rintro a ⟨j,hj,rfl⟩
  obtain ⟨k,hk⟩ := pairInterchange_generators i j
  change (MulAut.conj (pairInterchange i)) (pairSwap 7 j) ∈ D 7
  rw [hk]
  exact pairSwap_mem (n := 7) (m := 3) k k.isLt

variable {H : Type*} [Group H] [Finite H]

/-- A single nontrivial disjoint-transposition maximum elementary image
forces every transposition in the chosen Sylow image into its Thompson image. -/
theorem swap_mem_thompson_image_of_caseAFamily
    (R : Sylow 2 H) (π : H →* Equiv.Perm (Fin 7)) (hπ : Function.Surjective π)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (R : Subgroup H))
    (hfamily : CaseAFamily 7 (A.map π))
    {s : Equiv.Perm (Fin 7)} (hs : s.IsSwap) (hsQ : s ∈ (R : Subgroup H).map π) :
    s ∈ (elementaryAbelianMaxJ (R : Subgroup H)).map π := by
  obtain ⟨m,hm,hm3,a,ha⟩ := hfamily
  obtain ⟨Q₀,hD,_⟩ := Odd.exists_sylow_containing_D (Or.inr rfl : 7 = 5 ∨ 7 = 7)
  let Q := R.mapSurjective hπ
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 7)) Q₀ Q
  have hgQ : (Q₀ : Subgroup (Equiv.Perm (Fin 7))).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg (fun U : Sylow 2 (Equiv.Perm (Fin 7)) => (U : Subgroup (Equiv.Perm (Fin 7)))) hg
  have hDJ : (D 7).map (MulAut.conj g).toMonoidHom ≤
      (elementaryAbelianMaxJ (R : Subgroup H)).map π := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro t ⟨i,hi,rfl⟩
    let b := g * pairInterchange i * a⁻¹
    obtain ⟨n,hn⟩ := hπ b
    let B := A.map (MulAut.conj n).toMonoidHom
    have hBg : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
      have hh := (maxFamily_map_injective_iff (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective ⊤ A).mpr ((maxFamily_sylow_iff R A).mp hA).2
      rwa [map_top_of_surjective _ (MulAut.conj n).surjective] at hh
    have hBi : B.map π = ((disjointTranspositions 7 m).map
        (MulAut.conj (pairInterchange i)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      have he : π.comp (MulAut.conj n).toMonoidHom = (MulAut.conj b).toMonoidHom.comp π := by
        apply MonoidHom.ext
        intro x
        change π (n*x*n⁻¹) = b * π x * b⁻¹
        rw [map_mul,map_mul,map_inv,hn]
      change (A.map _).map π = _
      rw [map_map,he,←map_map,ha,map_map,map_map]
      congr 1
      ext x
      simp [b,MulAut.conj_apply,mul_assoc]
    have hBQ : B.map π ≤ (R : Subgroup H).map π := by
      rw [hBi]
      exact (map_mono ((map_mono (disjointTranspositions_le_D 7 m)).trans
        (pairInterchange_D i))).trans ((map_mono hD).trans hgQ.le)
    obtain ⟨C,hC,hCi⟩ := exists_maxFamily_sylow_same_image R π B hBg hBQ
    have ht : (MulAut.conj g) (pairSwap 7 i) ∈ C.map π := by
      rw [hCi,hBi]
      apply mem_map_of_mem
      rw [←pairInterchange_first i]
      exact mem_map_of_mem _ (pairSwap_mem (n := 7) (m := m) (0 : Fin 3) (by change 0 < m; omega))
    exact map_mono (le_sSup hC) ht
  have hsin : (MulAut.conj g⁻¹) s ∈ Q₀ := by
    have hx : s ∈ (Q₀ : Subgroup _).map (MulAut.conj g).toMonoidHom := hgQ ▸ hsQ
    obtain ⟨t,ht,he⟩ := hx
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using ht
  have hswap : ((MulAut.conj g⁻¹) s).IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := hs
    exact ⟨g⁻¹ i,g⁻¹ j,(g⁻¹).injective.ne hij,Equiv.symm_trans_swap_trans i j g⁻¹⟩
  have hsD := Odd.isSwap_mem_D_of_isPGroup (Or.inr rfl) Q₀.isPGroup' hD hswap hsin
  have hx := hDJ (mem_map_of_mem (MulAut.conj g).toMonoidHom hsD)
  simpa [MulAut.conj_apply,mul_assoc] using hx

end CFSG.Quasithin.ChapterB.Offenders
