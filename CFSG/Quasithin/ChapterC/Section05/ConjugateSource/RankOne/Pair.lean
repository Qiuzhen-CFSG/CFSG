module

public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.PairTransport
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# Two Sylow conjugates in the natural rank-one quotient

An explicit Weyl matrix conjugates an upper transvection to a lower one.
The proved Borel-overgroup calculation then shows that the two root groups
generate SL₂. Sylow conjugacy transports the result to any defining-
characteristic Sylow subgroup, including SL₂(2).

The actual preceding quotient marking supplies the full upper-root image
of S. Quotient transport chooses a conjugator in L and replaces S by Uˣ
modulo the actual two-core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2)
and C.5.6, printed pp.155–157 (PDF pp.166–168).
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {F : Type*} [Field F]
local notation "u" => SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one
local notation "v" => SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero
private def w : SL(2,F) := u (-1) * v 1 * u (-1)
private theorem conj_w : (MulAut.conj (w (F := F))) (u (1 : F)) = v (-1) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w, mul_apply, Fin.sum_univ_two, transvection_coe]

private theorem upper_pair : ∃ g : SL(2,F),
    upperUnipotent F ⊔ (upperUnipotent F).map (MulAut.conj g).toMonoidHom = ⊤ := by
  refine ⟨w, ?_⟩
  by_contra ht
  have hb := overgroup_le_rankOneBorel
    (le_sup_left : upperUnipotent F ≤
      upperUnipotent F ⊔ (upperUnipotent F).map (MulAut.conj w).toMonoidHom) ht
  have hm : v (-1 : F) ∈ rankOneBorel F := hb
    (mem_sup_right (mem_map.mpr ⟨u 1, (mem_upperUnipotent F _).mpr ⟨1, rfl⟩,
      conj_w⟩))
  have hz := (mem_rankOneBorel_iff _).mp hm
  simp [transvection_coe] at hz

variable {G : Type*} [Group G] {R L : Subgroup G}

/-- The full upper root group and its Weyl conjugate generate the marked
quotient. Its conjugator lifts into the selected original block. -/
theorem Setup.quotient_pair (h : Setup R L F) {V : Subgroup G}
    (hspan : S R = V ⊔ Q R L) :
    ∃ y ∈ L, L ≤ (V ⊔ V.map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  obtain ⟨y, hy, hg⟩ := choose_block_conjugator h h.quotient h.surjective
    (by rw [h.image]; exact upper_pair)
  exact ⟨y, hy, lift_quotient_pair hspan h.quotient h.kernel hg⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
