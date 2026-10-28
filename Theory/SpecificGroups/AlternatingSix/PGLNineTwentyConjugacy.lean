module
public import Theory.SpecificGroups.AlternatingSix.PGLNineFiveNormalizer

/-!
# Conjugacy of the full pair images in PGL₂(9)

Every subgroup of order twenty has a unique Sylow five-subgroup. It is
therefore contained in that five-subgroup's normalizer, whose order is
already twenty. Sylow conjugacy consequently aligns any two such subgroups.
This retains the entire quotient pair subgroup, rather than only its order.
-/

public noncomputable section
open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter
namespace AlternatingSix.PGLNineFiveNormalizer
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem pgl_card : Nat.card (PGL2 Nine.F) = 720 := by
  rw [pgl2_card_formula,Nine.card]
  norm_num

/-- An actual subgroup of order twenty is the full normalizer of its
five-subgroup. -/
theorem twenty_eq_five_normalizer
    (H : Subgroup (PGL2 Nine.F)) (hH : Nat.card H = 20) :
    ∃ Q : Subgroup (PGL2 Nine.F), Nat.card Q = 5 ∧ H = normalizer (Q : Set (PGL2 Nine.F)) := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let S : Sylow 5 H := default
  have hS : Nat.card S = 5 := by rw [S.card_eq_multiplicity,hH]; decide +kernel
  have hi : (S : Subgroup H).index = 4 := by
    have hh := (S : Subgroup H).card_mul_index
    rw [hS,hH] at hh
    omega
  have hcount : Nat.card (Sylow 5 H) = 1 := by
    have hd := S.card_dvd_index
    rw [hi] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hm := card_sylow_modEq_one 5 H
    change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hm
    omega
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (S : Subgroup H).Normal := S.normal_of_subsingleton
  let Q := (S : Subgroup H).map H.subtype
  have hQ : Nat.card Q = 5 := (card_map_of_injective H.subtype_injective).trans hS
  have hn : H ≤ normalizer (Q : Set (PGL2 Nine.F)) := by
    have hh := (S : Subgroup H).le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  refine ⟨Q,hQ,eq_of_le_of_card_ge hn ?_⟩
  rw [five_normalizer_card Q hQ,hH]

/-- One actual projective element simultaneously carries the entire
order-twenty subgroup to any other such subgroup. -/
theorem twenty_subgroups_conjugate
    (H K : Subgroup (PGL2 Nine.F)) (hH : Nat.card H = 20) (hK : Nat.card K = 20) :
    ∃ g : PGL2 Nine.F, H.map (MulAut.conj g).toMonoidHom = K := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨Q,hQ,rfl⟩ := twenty_eq_five_normalizer H hH
  obtain ⟨R,hR,rfl⟩ := twenty_eq_five_normalizer K hK
  let P : Sylow 5 (PGL2 Nine.F) := Sylow.ofCard Q (by rw [hQ,pgl_card]; decide +kernel)
  let S : Sylow 5 (PGL2 Nine.F) := Sylow.ofCard R (by rw [hR,pgl_card]; decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (PGL2 Nine.F) P S
  have he : Q.map (MulAut.conj g).toMonoidHom = R := congrArg Sylow.toSubgroup hg
  refine ⟨g,?_⟩
  rw [map_equiv_normalizer_eq,he]

end AlternatingSix.PGLNineFiveNormalizer
