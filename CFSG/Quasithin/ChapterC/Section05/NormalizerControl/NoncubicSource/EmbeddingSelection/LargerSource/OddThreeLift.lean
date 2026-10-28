module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.SpecificGroups.OddThreePerfectLifts

/-!
# The full-Sylow centralizer reduction for the smaller SL₂(5) cover

The unique central involution of SL₂(5) is fixed by every normalizing
element. Hence the smaller subgroup and its full Sylow normalizer lie in
its actual involution centralizer. Projective ternary centralizers lift
through cubic scalar kernels to GL₂ or GU₂; the determinant kernel retains
the smaller subgroup faithfully and a full Sylow still normalizes it.

The source application uses the literal larger-span images in X/O₂(X).
This isolates the prime-field rank-one recognition needed for A.3.12(9),
pp.47–48, and the remaining natural C.5.12 branch, p.163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The characteristic central involution is fixed by the full normalizer. -/
theorem exists_normalizer_fixed_involution_of_center_card_two
    (B : Subgroup G) (hc : Nat.card (center B) = 2) :
    ∃ z : G, z ∈ B ∧ orderOf z = 2 ∧
      normalizer (B : Set G) ≤ centralizer ({z} : Set G) := by
  let Z := (center B).map B.subtype
  have hZ : Nat.card Z = 2 := by rw [card_map_of_injective B.subtype_injective,hc]
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZ])
  refine ⟨z, (map_subtype_le _) z.property, (orderOf_coe z).trans hz, ?_⟩
  exact (normalizer_le_normalizer_characteristic_image B (center B)).trans
    ((normalizer_le_centralizer_of_card_two Z hZ).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property)))

/-- A Sylow normalizing an SL₂(5) subgroup lies in the full centralizer of
its central involution, together with the smaller subgroup itself. -/
theorem sl2_five_full_sylow_in_centralizer
    (T : Sylow 2 G) (B : Subgroup G) (hB : IsSL B 2 5)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ z : G, z ∈ B ∧ orderOf z = 2 ∧
      B ⊔ (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  have hc : Nat.card (center B) = 2 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hB
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center,hF]
    norm_num
  obtain ⟨z,hz,ho,hn⟩ := exists_normalizer_fixed_involution_of_center_card_two B hc
  exact ⟨z,hz,ho,sup_le (B.le_normalizer.trans hn) (hTB.trans hn)⟩

/-- The original natural larger-span branch retains its actual central
involution and the full original quotient Sylow in its centralizer. -/
theorem source_larger_odd_three_full_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : let E := ((conjugateSpanBy K X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      IsPSLSign E u 3 p ∨ IsSLSign E u 3 p) :
    let r := QuotientGroup.mk' (pCore 2 X)
    let B := (K.subgroupOf X).map r
    let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
    ∃ z : X ⧸ pCore 2 X, z ∈ B ∧ orderOf z = 2 ∧
      B ⊔ (Q : Subgroup (X ⧸ pCore 2 X)) ≤ centralizer ({z} : Set (X ⧸ pCore 2 X)) := by
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hB := (source_larger_odd_three_forces_small_cover hG K T X hK h3 hUT hT hTK
    hAX hX S hS hVC hp ho u hm).2
  apply sl2_five_full_sylow_in_centralizer Q B hB
  change (S : Subgroup X).map r ≤ normalizer (B : Set (X ⧸ pCore 2 X))
  apply (map_mono (f := r) ?_).trans (le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq (le_sup_left.trans hAX : K ≤ X)]
  intro s hs
  exact hTK (hS ▸ mem_map_of_mem X.subtype hs)

/-- The faithful linear cover of a centralizer containing a nontrivial
perfect subgroup is noncommutative. -/
private theorem noncommutative_cover {A H : Type*} [Group A] [Group H]
    (f : A →* H) (hf : Function.Surjective f) (B : Subgroup H)
    [IsQuasisimple B] : ¬ IsMulCommutative A := by
  intro ha
  have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
    obtain ⟨x,rfl⟩ := hf x
    obtain ⟨y,rfl⟩ := hf y
    rw [← map_mul,← map_mul,ha.is_comm.comm x y])
  have hb : IsMulCommutative B := IsMulCommutative.of_comm (fun x y =>
    Subtype.ext (hh.is_comm.comm x y))
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  exact Group.IsPerfect.not_isMulCommutative B hb

open scoped MatrixGroups

/-- A smaller quasisimple subgroup normalized by the full projective-linear
centralizer Sylow lifts into the actual SL₂ determinant kernel of GL₂. -/
theorem projective_linear_centralizer_full_sylow_lift
    {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) (ht : orderOf t = 2)
    (T : Sylow 2 (centralizer ({t} : Set _)))
    (B : Subgroup (centralizer ({t} : Set _))) [IsQuasisimple B]
    (hTB : (T : Subgroup (centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)))) ≤
      normalizer (B : Set (centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))))) :
    ∃ (S : Sylow 2 (GL (Fin 2) F)) (A : Subgroup (GL (Fin 2) F)),
      Nonempty (A ≃* B) ∧ A ≤ Matrix.GeneralLinearGroup.det.ker ∧
        (S : Subgroup (GL (Fin 2) F)) ≤ normalizer (A : Set (GL (Fin 2) F)) := by
  obtain ⟨f,hf,hk,h3⟩ := Matrix.PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection t ht h2
  obtain ⟨S,A,e,_,hA,hn,_⟩ := Theory.SpecificGroups.OddThreeLevi.exists_perfect_sylow_normalized_lift
    (MonoidHom.id _) Function.injective_id (noncommutative_cover f hf B)
    f hf hk h3 T B hTB
  exact ⟨S,A,⟨e⟩,hA,hn⟩

/-- The unitary branch lifts to the actual GU₂ full Sylow and SU₂
 determinant kernel, preserving the smaller subgroup isomorphism. -/
theorem projective_unitary_centralizer_full_sylow_lift
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (F : Type*) [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (t : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (T : Sylow 2 (centralizer ({t} : Set _)))
    (B : Subgroup (centralizer ({t} : Set _))) [IsQuasisimple B]
    (hTB : (T : Subgroup (centralizer ({t} : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)))) ≤
      normalizer (B : Set (centralizer ({t} : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))))) :
    ∃ (S : Sylow 2 (ABG.GU2 p 1 one_ne_zero)) (A : Subgroup (ABG.GU2 p 1 one_ne_zero)),
      Nonempty (A ≃* B) ∧ A ≤ (ABG.unitaryForm 2 p 1 one_ne_zero).unitaryDet.ker ∧
        (S : Subgroup (ABG.GU2 p 1 one_ne_zero)) ≤
          normalizer (A : Set (ABG.GU2 p 1 one_ne_zero)) := by
  obtain ⟨f,hf,hk,h3⟩ := Matrix.SU3.OddCubicCentralizer.surjection p hp F J hcard hc t ht
  let ρ := (ABG.unitaryForm 2 p 1 one_ne_zero).unitarySubgroup.subtype
  obtain ⟨S,A,e,_,hA,hn,_⟩ := Theory.SpecificGroups.OddThreeLevi.exists_perfect_sylow_normalized_lift
    ρ Subtype.val_injective (noncommutative_cover f hf B) f hf hk h3 T B hTB
  exact ⟨S,A,⟨e⟩,hA,hn⟩


/-- Restrict the original full Sylow and its normalized smaller subgroup
to the actual involution centralizer, with no conjugation replacement. -/
private theorem centralizer_restriction
    (T : Sylow 2 G) (B : Subgroup G) [IsQuasisimple B] (hB : IsSL B 2 5)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ (t : G) (_ht : orderOf t = 2)
      (S : Sylow 2 (centralizer ({t} : Set G))) (A : Subgroup (centralizer ({t} : Set G))),
      IsQuasisimple A ∧ Nonempty (A ≃* B) ∧
        (S : Subgroup _) ≤ normalizer (A : Set (centralizer ({t} : Set G))) := by
  obtain ⟨t,_,ht,hC⟩ := sl2_five_full_sylow_in_centralizer T B hB hTB
  let C := centralizer ({t} : Set G)
  have hBC : B ≤ C := le_sup_left.trans hC
  have hTC : (T : Subgroup G) ≤ C := le_sup_right.trans hC
  let e := subgroupOfEquivOfLe hBC
  refine ⟨t,ht,T.subtype hTC,B.subgroupOf C,IsQuasisimple.of_mulEquiv e.symm,⟨e⟩,?_⟩
  rw [Sylow.coe_subtype,← subgroupOf_normalizer_eq hBC]
  exact subgroupOf_mono C hTB

/-- The full Sylow normalizer of an SL₂(5) subgroup in actual odd PSL₃
lifts to a full GL₂ Sylow normalizing an isomorphic determinant-one subgroup. -/
theorem projective_linear_sl2_five_rank_one_lift
    {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (T : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) [IsQuasisimple B]
    (hB : IsSL B 2 5)
    (hTB : (T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) ≤
      normalizer (B : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))) :
    ∃ (S : Sylow 2 (GL (Fin 2) F)) (A : Subgroup (GL (Fin 2) F)),
      Nonempty (A ≃* B) ∧ A ≤ Matrix.GeneralLinearGroup.det.ker ∧
        (S : Subgroup (GL (Fin 2) F)) ≤ normalizer (A : Set (GL (Fin 2) F)) := by
  obtain ⟨t,ht,Q,D,hD,⟨e⟩,hn⟩ := centralizer_restriction T B hB hTB
  let : IsQuasisimple D := hD
  obtain ⟨S,A,⟨a⟩,hA,hN⟩ := projective_linear_centralizer_full_sylow_lift h2 t ht Q D hn
  exact ⟨S,A,⟨a.trans e⟩,hA,hN⟩

/-- The corresponding full Sylow normalizer in actual odd PSU₃ lifts to
GU₂ and its SU₂ determinant kernel, keeping the actual smaller cover. -/
theorem projective_unitary_sl2_five_rank_one_lift
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (F : Type*) [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (B : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) [IsQuasisimple B]
    (hB : IsSL B 2 5)
    (hTB : (T : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      normalizer (B : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∃ (S : Sylow 2 (ABG.GU2 p 1 one_ne_zero)) (A : Subgroup (ABG.GU2 p 1 one_ne_zero)),
      Nonempty (A ≃* B) ∧ A ≤ (ABG.unitaryForm 2 p 1 one_ne_zero).unitaryDet.ker ∧
        (S : Subgroup (ABG.GU2 p 1 one_ne_zero)) ≤
          normalizer (A : Set (ABG.GU2 p 1 one_ne_zero)) := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨t,ht,Q,D,hD,⟨e⟩,hn⟩ := centralizer_restriction T B hB hTB
  let : IsQuasisimple D := hD
  obtain ⟨S,A,⟨a⟩,hA,hN⟩ := projective_unitary_centralizer_full_sylow_lift p hp F J hcard hc t ht Q D hn
  exact ⟨S,A,⟨a.trans e⟩,hA,hN⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
