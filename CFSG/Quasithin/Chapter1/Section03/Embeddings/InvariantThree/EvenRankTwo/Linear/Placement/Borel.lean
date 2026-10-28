module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow

/-!
# Odd subgroups of the actual degree-three Borel

The diagonal homomorphism on upper triangular matrices has unipotent kernel.
Over a field of order 2^f, its restriction to a three-subgroup is injective,
since the intersection with UT₃ is trivial. Thus that three-subgroup is
abelian. This is a matrix calculation, with no multiplier or projective
cover identification assumed.

Application: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`).
-/

public section
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement

private def borelDiagonal (F : Type*) [Field F] [Finite F] :
    borelSL F →* (Fin 3 → F) where
  toFun g i := g.val.val i i
  map_one' := by ext i; simp
  map_mul' := by
    intro g h
    obtain ⟨g10,g20,g21⟩ := (mem_borelSL_iff F g).mp g.property
    obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F h).mp h.property
    ext i
    fin_cases i <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, g10,g20,g21,h10,h20,h21]

/-- Three-subgroups of the matrix Borel embed in its diagonal group. -/
theorem threeSubgroup_commutative_of_le_borelSL (F : Type*) [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2^f)
    (R : Subgroup SL(3,F)) (hR : IsPGroup 3 R) (hRB : R ≤ borelSL F) :
    IsMulCommutative R := by
  let d := (borelDiagonal F).comp (inclusion hRB)
  have hU : IsPGroup 2 (unipotentSL F) := by
    apply IsPGroup.of_card (n := f * 3)
    rw [card_unipotentSL F, hF, pow_mul]
  have hdis : Disjoint R (unipotentSL F) := hR.disjoint_of_coprime hU (by decide)
  have hd : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff d).mp
    apply le_bot_iff.mp
    intro r hr
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hdis r.property
    have hdiag : ∀ i, r.val.val i i = 1 := by
      intro i
      exact congrFun (show d r = 1 from hr) i
    have hb := (mem_borelSL_iff F r).mp (hRB r.property)
    rw [mem_unipotentSL_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb.1,hb.2.1,hb.2.2,hdiag]
  exact ⟨⟨fun a b => hd (by simp only [map_mul, mul_comm])⟩⟩

/-- A genuine scalar-cover map transports matrix-Borel abelianness to Q.
A Sylow three-subgroup of the inverse image maps onto R; the commuting
triangle places that lift in the actual upper-triangular matrix group. -/
theorem threeSubgroup_commutative_of_scalar_cover (F : Type*) [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2^f)
    {Q : Type*} [Group Q] [Finite Q] (R : Subgroup Q) (hR : IsPGroup 3 R)
    (q : Q →* PSL(3,F)) (k : SL(3,F) →* Q) (hk : Function.Surjective k)
    (hfac : q.comp k = projection F) (hB : R.map q ≤ borel F) :
    IsMulCommutative R := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K := R.comap k
  let P : Sylow 3 K := Sylow.nonempty.some
  let A : Subgroup SL(3,F) := (P : Subgroup K).map K.subtype
  have hPmap : (P : Subgroup K).map (k.subgroupComap R) = ⊤ := by
    let T := P.mapSurjective (k.subgroupComap_surjective_of_surjective R hk)
    exact (T.is_maximal' (hR.to_subgroup ⊤) le_top).symm
  have hmap : A.map k = R := by
    have he : R.subtype.comp (k.subgroupComap R) = k.comp K.subtype := rfl
    rw [show A = (P : Subgroup K).map K.subtype from rfl, Subgroup.map_map,
      ← he, ← Subgroup.map_map, hPmap, ← MonoidHom.range_eq_map, range_subtype]
  have hAB : A ≤ borelSL F := by
    intro x hx
    rw [← borel_comap F]
    change projection F x ∈ borel F
    rw [← hfac]
    apply hB
    exact mem_map_of_mem q (map_subtype_le (P : Subgroup K) hx)
  have hA : IsMulCommutative A := by
    apply threeSubgroup_commutative_of_le_borelSL F hF A (P.isPGroup'.map K.subtype) hAB
  let _ := hA
  have hm := Subgroup.map_isMulCommutative A k
  rw [hmap] at hm
  exact hm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement
