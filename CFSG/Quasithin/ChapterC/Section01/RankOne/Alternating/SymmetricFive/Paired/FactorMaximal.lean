module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Borel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.LocalGeometry

/-!
# The prescribed symmetric-five factor meets the maximal local in S₄

The genuine component Sylow normalizer places an A₄ in the original maximal
overgroup. Properness of the marked S₅ factor and an odd Thompson element
then make its intersection the same point stabilizer. The two transpositions
identify its fixed point in the original coordinates, retaining the literal
factor embedding for the later cubic lift and conjugate-span calculation.

Source: Aschbacher--Smith C.1.24, E.2.3(3) and3.1.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB ChapterB.Offenders
variable {G : Type*} [Group G] [Finite G]

private theorem even_stabilizer_coatom (i : Fin 5) :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 5)) i) := by
  have hc : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
    rw [Nat.card_eq_fintype_card]
    revert i
    decide +kernel
  have hi : (MulAction.stabilizer (alternatingGroup (Fin 5)) i).index = 5 := by
    have hh := (MulAction.stabilizer (alternatingGroup (Fin 5)) i).card_mul_index
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  refine ⟨fun h => by simp [h] at hi, fun B hB => ?_⟩
  have hd := (index_dvd_of_le hB.le)
  rw [hi] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
  · exact index_eq_one.mp h
  · have := index_strictAnti hB
    omega

theorem source_symmetric_factor_maximal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    {L : Subgroup G} (hL : IsComponent G L)
    (e : L ≃* alternatingGroup (Fin 5))
    (j : Sym →* G)
    (hmark : ∀ l : L, j (e l) = l)
    (hF : ¬ j.range ≤ minimalParabolicMax T hP)
    (a : Sym) (hD : ((D 5).map (MulAut.conj a).toMonoidHom).map j ≤ T) :
    (minimalParabolicMax T hP).comap j = pointFour.map (MulAut.conj a).toMonoidHom := by
  let M := minimalParabolicMax T hP
  let B : Subgroup Sym := M.comap j
  have hB : B ≠ ⊤ := by
    intro hb
    apply hF
    rintro _ ⟨g,rfl⟩
    exact (show g ∈ B from hb ▸ mem_top _)
  obtain ⟨i,hi⟩ := source_component_borel T hP hL e
  have heven : alternatingGroup (Fin 5) ⊓ MulAction.stabilizer Sym i ≤ B := by
    intro x hx
    have hh : (e.symm ⟨x,hx.1⟩ : G) ∈ M :=
      hi (mem_map_of_mem L.subtype (mem_map_of_mem e.symm.toMonoidHom hx.2))
    have he := hmark (e.symm ⟨x,hx.1⟩)
    rw [e.apply_symm_apply] at he
    change j x ∈ M
    exact he ▸ hh
  have hDB : (D 5).map (MulAut.conj a).toMonoidHom ≤ B := by
    intro x hx
    exact (minimalParabolicMax_spec T hP).2 (hD (mem_map_of_mem j hx))
  have hodd : a * Equiv.swap (0 : Fin 5) 1 * a⁻¹ ∈ B :=
    hDB (mem_map_of_mem (MulAut.conj a).toMonoidHom (pairSwap_mem 0 (by decide)))
  have hodd' : a * Equiv.swap (0 : Fin 5) 1 * a⁻¹ ∉ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_mul,map_inv,Equiv.Perm.sign_swap (by decide)]
    simp
  have hBE : B.subgroupOf (alternatingGroup (Fin 5)) =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    have hh : MulAction.stabilizer (alternatingGroup (Fin 5)) i ≤
        B.subgroupOf (alternatingGroup (Fin 5)) := by
      intro x hx
      exact heven ⟨x.property,hx⟩
    rcases (even_stabilizer_coatom i).le_iff.mp hh with ht | he
    · exfalso
      apply hB
      apply top_unique
      intro x _
      have hAB : alternatingGroup (Fin 5) ≤ B := by
        intro y hy
        exact (show (⟨y,hy⟩ : alternatingGroup (Fin 5)) ∈ B.subgroupOf _ from ht ▸ mem_top _)
      by_cases hx : x ∈ alternatingGroup (Fin 5)
      · exact hAB hx
      · have hxt : x * (a * Equiv.swap (0 : Fin 5) 1 * a⁻¹)⁻¹ ∈ alternatingGroup (Fin 5) := by
          rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
          exact iff_of_false hx hodd'
        simpa only [inv_mul_cancel_right] using B.mul_mem (hAB hxt) hodd
    · exact he
  have hBi : B ≤ MulAction.stabilizer Sym i := by
    intro g hg
    have hc (x : alternatingGroup (Fin 5)) (hx : x.val i = i) : x.val (g⁻¹ i) = g⁻¹ i := by
      have hxm : (x : Sym) ∈ B := heven ⟨x.property,hx⟩
      have hgx : (⟨g * (x : Sym) * g⁻¹,
          (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem x x.property g⟩ :
          alternatingGroup (Fin 5)) ∈ B.subgroupOf _ := B.mul_mem (B.mul_mem hg hxm) (B.inv_mem hg)
      rw [hBE] at hgx
      change g (x.val (g⁻¹ i)) = i at hgx
      exact g.injective (by simpa using hgx)
    have hfix : ∀ i j : Fin 5,
        (∀ x : alternatingGroup (Fin 5), x.val i = i → x.val j = j) → j = i := by
      decide +kernel
    have he := hfix i (g⁻¹ i) hc
    change g i = i
    simpa using congrArg g he.symm
  have hi' : i = a 4 := by
    have hfix : ∀ i : Fin 5, Equiv.swap (0 : Fin 5) 1 i = i →
        Equiv.swap (2 : Fin 5) 3 i = i → i = 4 := by decide
    have h₁ := hBi (hDB (mem_map_of_mem (MulAut.conj a).toMonoidHom (pairSwap_mem 0 (by decide))))
    have h₂ := hBi (hDB (mem_map_of_mem (MulAut.conj a).toMonoidHom (pairSwap_mem 1 (by decide))))
    have hh := hfix (a⁻¹ i) (a.injective (by simpa [MulAut.conj_apply,pairSwap] using h₁))
      (a.injective (by simpa [MulAut.conj_apply,pairSwap] using h₂))
    simpa using congrArg a hh
  have hstab : MulAction.stabilizer Sym i = pointFour.map (MulAut.conj a).toMonoidHom := by
    subst i
    ext g
    change g (a 4) = a 4 ↔ _
    constructor
    · intro hg
      refine ⟨a⁻¹ * g * a,?_,?_⟩
      · apply (mem_pointFour_iff _).mpr
        change a⁻¹ (g (a 4)) = 4
        rw [hg]; simp
      · simp [MulAut.conj_apply,mul_assoc]
    · rintro ⟨g,hg,rfl⟩
      change a (g (a⁻¹ (a 4))) = a 4
      have hg' : g 4 = 4 := (mem_pointFour_iff g).mp hg
      simp only [Equiv.Perm.coe_inv,Equiv.symm_apply_apply,hg']
  have hle : B ≤ pointFour.map (MulAut.conj a).toMonoidHom := hBi.trans hstab.le
  have hge : pointFour.map (MulAut.conj a).toMonoidHom ≤ B := by
    rw [←hstab]
    intro x hx
    by_cases ha : x ∈ alternatingGroup (Fin 5)
    · exact heven ⟨ha,hx⟩
    · have ht : x * (a * Equiv.swap (0 : Fin 5) 1 * a⁻¹)⁻¹ ∈ alternatingGroup (Fin 5) ⊓ MulAction.stabilizer Sym i := by
        constructor
        · change x * (a * Equiv.swap (0 : Fin 5) 1 * a⁻¹)⁻¹ ∈ alternatingGroup (Fin 5)
          rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
          exact iff_of_false ha hodd'
        · exact (MulAction.stabilizer Sym i).mul_mem hx ((MulAction.stabilizer Sym i).inv_mem (hBi hodd))
      simpa only [inv_mul_cancel_right] using B.mul_mem (heven ht) hodd
  exact le_antisymm hle hge
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
