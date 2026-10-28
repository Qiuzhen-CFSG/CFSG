module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Normalizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Parabolics

/-!
# Ambient intersections and the residual normalizer

Distinct overgroups with a common subgroup maximal in both meet precisely
in that subgroup. Applying this to the three source vertices gives the
literal intersections. The residual sandwich from `Basic` then computes
O²(L ∩ H₃); maximality and the cubic nonnormality theorem compute N_H₃(L₂).
Neither deduction identifies L ∩ H₃ itself with L₂.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
the ambient deductions in 14.4.13, printed p.1012.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G]

private theorem inf_eq_of_common_coatom {P A B : Subgroup G}
    (hPA : P ≤ A) (hPB : P ≤ B)
    (ha : IsCoatom (P.subgroupOf A)) (hb : IsCoatom (P.subgroupOf B))
    (hne : A ≠ B) : A ⊓ B = P := by
  have hlt : P.subgroupOf A ≤ B.subgroupOf A := fun _ hx => hPB hx
  rcases eq_or_lt_of_le hlt with he | he
  · apply le_antisymm
    · intro x hx
      exact (show (⟨x,hx.1⟩ : A) ∈ P.subgroupOf A from he ▸ hx.2)
    · exact le_inf hPA hPB
  · have hAB : A ≤ B := subgroupOf_eq_top.mp (ha.2 _ he)
    have hpA : P.subgroupOf B < A.subgroupOf B := by
      apply lt_of_le_of_ne (fun _ hx => hPA hx)
      intro he
      apply ha.1
      apply subgroupOf_eq_top.mpr
      intro x hx
      exact (show (⟨x,hAB hx⟩ : B) ∈ P.subgroupOf B from he ▸ hx)
    exact False.elim (hne (le_antisymm hAB (subgroupOf_eq_top.mp (hb.2 _ hpA))))

/-- All three literal intersections from marked maximality and distinctness
of the vertices. These are the ambient equalities used in D3. -/
theorem source_intersections
    (L L₁ L₂ X T : Subgroup G) (h₁ : L₁ ≤ L) (h₂ : L₂ ≤ L)
    (h₁₂ : (L ⊔ T) ≠ (L₁ ⊔ X ⊔ T))
    (h₂₃ : (L₁ ⊔ X ⊔ T) ≠ (localJoin L₂ X ⊔ T))
    (h₃₁ : (localJoin L₂ X ⊔ T) ≠ (L ⊔ T))
    (hp₁₁ : IsCoatom ((L₁ ⊔ T).subgroupOf (L ⊔ T)))
    (hp₁₂ : IsCoatom ((L₂ ⊔ T).subgroupOf (L ⊔ T)))
    (hp₂₁ : IsCoatom ((L₁ ⊔ T).subgroupOf (L₁ ⊔ X ⊔ T)))
    (hp₂₂ : IsCoatom ((X ⊔ T).subgroupOf (L₁ ⊔ X ⊔ T)))
    (hp₃₁ : IsCoatom ((L₂ ⊔ T).subgroupOf (localJoin L₂ X ⊔ T)))
    (hp₃₂ : IsCoatom ((X ⊔ T).subgroupOf (localJoin L₂ X ⊔ T))) :
    (L ⊔ T) ⊓ (L₁ ⊔ X ⊔ T) = L₁ ⊔ T ∧
      (L₁ ⊔ X ⊔ T) ⊓ (localJoin L₂ X ⊔ T) = X ⊔ T ∧
      (localJoin L₂ X ⊔ T) ⊓ (L ⊔ T) = L₂ ⊔ T := by
  refine ⟨?_, ?_, ?_⟩
  · exact inf_eq_of_common_coatom (sup_le_sup_right h₁ T)
      (sup_le_sup_right le_sup_left T) hp₁₁ hp₂₁ h₁₂
  · exact inf_eq_of_common_coatom (sup_le_sup_right le_sup_right T)
      (sup_le_sup_right le_sup_right T) hp₂₂ hp₃₂ h₂₃
  · exact inf_eq_of_common_coatom (sup_le_sup_right le_sup_left T)
      (sup_le_sup_right h₂ T) hp₃₁ hp₁₂ h₃₁

/-- The corrected residual conclusion in the printed proof of 14.4.13. -/
theorem source_point_plane_residual
    (L L₂ X T : Subgroup G) (h₂ : L₂ ≤ L)
    (hres : twoResidual L₂ = L₂) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (L₂ : Set G))
    (hi : (localJoin L₂ X ⊔ T) ⊓ (L ⊔ T) = L₂ ⊔ T) :
    twoResidual (L ⊓ (localJoin L₂ X ⊔ T)) = L₂ := by
  apply twoResidual_eq_of_between hres hT hn
  · exact le_inf h₂ (le_sup_left.trans le_sup_left)
  · rw [← hi]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_left)

private theorem relative_normalizer_eq_of_coatom {E T J : Subgroup G}
    (hET : T ≤ normalizer (E : Set G)) (hEJ : E ≤ J) (hTJ : T ≤ J)
    (hp : IsCoatom ((E ⊔ T).subgroupOf J))
    (hne : ¬ J ≤ normalizer (E : Set G)) :
    J ⊓ normalizer (E : Set G) = E ⊔ T := by
  have hn : E ⊔ T ≤ normalizer (E : Set G) := sup_le E.le_normalizer hET
  have hj : E ⊔ T ≤ J := sup_le hEJ hTJ
  have hl : (E ⊔ T).subgroupOf J ≤ (normalizer (E : Set G)).subgroupOf J :=
    fun _ hx => hn hx
  rcases eq_or_lt_of_le hl with he | he
  · apply le_antisymm
    · intro x hx
      exact (show (⟨x,hx.1⟩ : J) ∈ (E ⊔ T).subgroupOf J from he ▸ hx.2)
    · exact le_inf hj hn
  · exact False.elim (hne (subgroupOf_eq_top.mp (hp.2 _ he)))

/-- The relative normalizer bound required by `IntrinsicSource` follows
from the linear quotient and marked maximality; it is not a new premise. -/
theorem source_plane_normalizer [Finite G]
    (L L₂ X T : Subgroup G) (h₂ : ThreeExtension L T L₂)
    (e : coreQuotient (localJoin L₂ X ⊔ T) ≃* Matrix.PSL3Two.PSL)
    (hp : IsCoatom ((L₂ ⊔ T).subgroupOf (localJoin L₂ X ⊔ T))) :
    (localJoin L₂ X ⊔ T) ⊓ normalizer (L₂ : Set G) = L₂ ⊔ T := by
  exact relative_normalizer_eq_of_coatom h₂.T_normalizes
    (le_sup_left.trans le_sup_left) le_sup_right hp
    (h₂.not_normal_in_linear_vertex (le_sup_left.trans le_sup_left) e)

private theorem residual_eq_of_join_le {X Y T : Subgroup G}
    (hx : twoResidual (X ⊔ T) = X) (hy : twoResidual (Y ⊔ T) = Y)
    (hnot : ¬ X ≤ T) (hmin : IsCoatom (T.subgroupOf (Y ⊔ T)))
    (hle : X ⊔ T ≤ Y ⊔ T) : X = Y := by
  have hlt : T.subgroupOf (Y ⊔ T) < (X ⊔ T).subgroupOf (Y ⊔ T) := by
    apply lt_of_le_of_ne (fun _ ht => (show T ≤ X ⊔ T from le_sup_right) ht)
    intro he
    apply hnot
    intro x hX
    have hxXT : x ∈ X ⊔ T := (show X ≤ X ⊔ T from le_sup_left) hX
    exact (show (⟨x,hle hxXT⟩ : (Y ⊔ T : Subgroup G)) ∈ T.subgroupOf (Y ⊔ T) from
      he ▸ hxXT)
  have hjoin : X ⊔ T = Y ⊔ T :=
    le_antisymm hle (subgroupOf_eq_top.mp (hmin.2 _ hlt))
  exact hx.symm.trans ((congrArg twoResidual hjoin).trans hy)

private theorem separation {L L₁ X T H : Subgroup G}
    (hx : twoResidual (X ⊔ T) = X) (h₁ : twoResidual (L₁ ⊔ T) = L₁)
    (hnot : ¬ X ≤ T) (hmin : IsCoatom (T.subgroupOf (L₁ ⊔ T)))
    (hflag : (L ⊔ T) ⊓ H = L₁ ⊔ T) (hXH : X ≤ H) (hne : X ≠ L₁) :
    ¬ X ≤ L ⊔ T := by
  intro hXL
  apply hne
  apply residual_eq_of_join_le hx h₁ hnot hmin
  apply sup_le _ le_sup_right
  rw [← hflag]
  exact le_inf hXL hXH

private theorem pair_distinct {A B J : Subgroup G} (hA : A ≤ J) (hB : B ≤ J)
    (hgen : A ⊔ B = J) (hp : IsCoatom (A.subgroupOf J)) :
    A.subgroupOf J ≠ B.subgroupOf J := by
  intro he
  have hab : A = B := by
    simpa only [map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB]
      using congrArg (fun P : Subgroup J => P.map J.subtype) he
  have haJ : A = J := by simpa only [← hab, sup_idem] using hgen
  exact hp.1 (by rw [haJ, subgroupOf_self])

private theorem coatom_index_three (P : Subgroup G) (hi : P.index = 3) : IsCoatom P := by
  constructor
  · intro he
    norm_num [he] at hi
  · intro Q hQ
    have hd : Q.index ∣ 3 := hi ▸ index_dvd_of_le hQ.le
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hh | hh
    · exact index_eq_one.mp hh
    · have hm := relIndex_mul_index hQ.le
      rw [hi, hh] at hm
      have he : P.relIndex Q = 1 := by omega
      exact False.elim (hQ.not_ge (relIndex_eq_one.mp he))

/-- The different member of Y cannot lie in LT. The earlier flag stabilizer
identity and the index-three parabolic force any such member to equal L₁. -/
theorem source_actor_separation [Finite G]
    (L L₁ X H : Subgroup G) (T : Sylow 2 G)
    (h₁ : ThreeExtension H T L₁) (hX : ThreeExtension H T X)
    (hne : X ≠ L₁)
    (hflag : (L ⊔ (T : Subgroup G)) ⊓ H = L₁ ⊔ (T : Subgroup G))
    (hi : ((T : Subgroup G).subgroupOf (L₁ ⊔ (T : Subgroup G))).index = 3) :
    ¬ X ≤ L ⊔ (T : Subgroup G) := by
  exact separation (hX.residual_join T.isPGroup') (h₁.residual_join T.isPGroup')
    (hX.not_le_twoGroup T.isPGroup') (coatom_index_three _ hi) hflag hX.le_H hne

/-- Pull the full linear parabolic geometry onto two marked ambient
subgroups which generate the vertex. -/
theorem linear_vertex_parabolics [Finite G]
    (T : Sylow 2 G) (J A B : Subgroup G) (hA : A ≤ J) (hB : B ≤ J)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hgen : A ⊔ B = J) (e : coreQuotient J ≃* Matrix.PSL3Two.PSL)
    (hp : IsCoatom (A.subgroupOf J)) (hr : IsCoatom (B.subgroupOf J)) :
    Quasithin.I5.RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      (A.subgroupOf J) (B.subgroupOf J) := by
  exact rankTwoParabolics_of_linear_quotient e (T.subtype (hTA.trans hA)) _ _ hp hr
    (pair_distinct hA hB hgen hp) (fun _ hx => hTA hx) (fun _ hx => hTB hx)

/-- Pull the full product parabolic geometry onto the marked subgroups
of the middle source vertex. -/
theorem product_vertex_parabolics [Finite G]
    (T : Sylow 2 G) (J A B : Subgroup G) (hA : A ≤ J) (hB : B ≤ J)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hgen : A ⊔ B = J)
    (e : coreQuotient J ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hp : IsCoatom (A.subgroupOf J)) (hr : IsCoatom (B.subgroupOf J)) :
    Quasithin.I5.RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      (A.subgroupOf J) (B.subgroupOf J) := by
  exact rankTwoParabolics_of_product_quotient e (T.subtype (hTA.trans hA)) _ _ hp hr
    (pair_distinct hA hB hgen hp) (fun _ hx => hTA hx) (fun _ hx => hTB hx)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
