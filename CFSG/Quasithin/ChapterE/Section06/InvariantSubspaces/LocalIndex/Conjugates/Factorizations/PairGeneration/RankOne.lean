module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.Models
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# Two Sylow conjugates in the natural rank-one quotient

An explicit Weyl matrix conjugates an upper transvection to a lower one.
The proved Borel-overgroup calculation then shows that the two root groups
generate SL₂. Sylow conjugacy transports the result to any defining-
characteristic Sylow subgroup, including SL₂(2).

The actual quotient model supplies the Sylow image of S. Quotient transport
chooses a conjugator in L and replaces S by Uˣ modulo the actual two-core.
Construction of that model is the explicit remaining premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2)
and C.5.6, printed pp.155–157 (PDF pp.166–168).
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
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

private theorem sylow_pair [Finite F] [CharP F 2] (T : Sylow 2 (SL(2,F))) :
    ∃ g : SL(2,F), (T : Subgroup (SL(2,F))) ⊔
      (T : Subgroup (SL(2,F))).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (SL(2,F)) (upperUnipotentSylow F 2) T
  have ht : (upperUnipotent F).map (MulAut.conj d).toMonoidHom = T := by
    change ((d • upperUnipotentSylow F 2 : Sylow 2 (SL(2,F))) : Subgroup (SL(2,F))) = _
    rw [hd]
  obtain ⟨g, hg⟩ := upper_pair (F := F)
  refine ⟨d * g * d⁻¹, ?_⟩
  rw [← ht]
  have he : ((upperUnipotent F).map (MulAut.conj d).toMonoidHom).map
      (MulAut.conj (d * g * d⁻¹)).toMonoidHom =
      ((upperUnipotent F).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj d).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, ← Subgroup.map_sup, hg]
  exact map_top_of_surjective _ (MulAut.conj d).surjective
universe z
variable {G : Type z} [Group G] [Finite G]
variable {K : GroupClass.{z}} {A H R L : Subgroup G}

/-- A rank-one model supplies two Sylow conjugates; quotient transport
then chooses and lifts an actual conjugator in the block. -/
theorem rankOne_pair_of_model {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : Configuration K A H R L) (m : RankOneQuotient R L F)
    {x : G} (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L) :
    ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
      ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  obtain ⟨y, hy, hg⟩ := choose_block_conjugator h m.quotient m.surjective
    (by rw [m.image]; exact sylow_pair m.sylow)
  exact ⟨y, hy, lift_quotient_pair hspan m.quotient m.kernel hg⟩

/-- The natural and A₃ alternatives use the same concrete SL₂ calculation. -/
theorem rankOne_pair_of_input (hn : RankOneQuotientInput (G := G) K)
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hL : (∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 3)
    {x : G} (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G))
    (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L) :
    ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
      ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  obtain ⟨F, _, _, _, ⟨m⟩⟩ := hn A H R L h hb hL x hx hnc hspan
  exact rankOne_pair_of_model h m hspan

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration

end
