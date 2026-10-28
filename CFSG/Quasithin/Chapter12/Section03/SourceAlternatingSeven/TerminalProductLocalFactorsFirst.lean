module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsResiduals
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsSeed
public import Theory.SpecificGroups.SymmetricFour.CorePreimageAction
public import Theory.Representation.BinarySevenCode.WeightSixResidual

/-!
# Identifying the first terminal factor and its moved seed

The normal four-group in the support S₄ is transitive, so Sylow-fixed
words are constant on that support. The first block residual therefore
fixes Z, using the omega splitting and its containment in L. Conversely,
a Sylow-central weight-six word singles out one complementary letter.
The complementary image of C_L(Z) lies in its order-two stabilizer, so
its prime-to-three residual is trivial. This identifies the actual first
block residual with the published L₁=O^{3′}(C_L(Z)).

Consequently L_e=L₁R₂ for the second block residual R₂, and the whole
moved seed [Z,L_e] equals [Z,R₂] and contains an original weight-two point.
The identification R₂=L₂ and its natural marking remain with this task;
ComponentAnalysis is discharged by the final owner qt-d-1231-terminal.
Source: Aschbacher--Smith, paragraphs around 12.3.13, printed pp.811--812.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

theorem sylow_le_pointNormalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (T : Subgroup G) ≤ P.pointNormalizer := by
  apply le_inf (((structural G T L S.hypothesis).2.2 V S.chosen).1)
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp P.central).2.1 t ht)

/-- Every Sylow-fixed word is constant on the four-letter support of e. -/
theorem omega_word_support_constant
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (z : V) (hz : (z : G) ∈ P.Z)
    (i j : WeightFourLocal.Support (D.model.coordinates P.point).toAdd) :
    (D.model.coordinates z).toAdd.val i = (D.model.coordinates z).toAdd.val j := by
  let f : P.pointNormalizer →* Equiv.Perm (Fin 4) :=
    (MonoidHom.fst _ _).comp P.pointBlockAction
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨n,hn⟩ := P.pointBlockAction_surjective structural escape (a,1)
    exact ⟨n,congrArg Prod.fst hn⟩
  obtain ⟨t,ht,he⟩ := sylow_core_preimage_transitive
    (T.subtype (P.sylow_le_pointNormalizer structural)) f hf
    (WeightFourLocal.fourLetters _ P.weight_four i)
    (WeightFourLocal.fourLetters _ P.weight_four j)
  have htT : (t : G) ∈ (T : Subgroup G) := ht.1
  have hletters := P.pointBlockAction_first t i
  have hij : D.model.permutation ⟨t,t.property.1⟩ i = j := by
    have h := (WeightFourLocal.fourLetters _ P.weight_four).injective
      (hletters.symm.trans he)
    exact congrArg Subtype.val h
  have hc : V.normalizerMonoidHom ⟨t,t.property.1⟩ z = z := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr
      (((mem_omegaCenterIn_iff _ _).mp hz).2.1 t htT)
  have h := D.model.equivariant ⟨t,t.property.1⟩ z
  rw [hc] at h
  have hi := congrArg (fun w : EvenWord => w.val (D.model.permutation ⟨t,t.property.1⟩ i)) h
  simp only [evenRepresentation_apply,Equiv.symm_apply_apply] at hi
  rw [hij] at hi
  exact hi.symm

/-- The actual four-letter preimage fixes Z∩V. -/
theorem firstPointFactor_centralizes_omega_intersection
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    P.firstPointFactor ≤ centralizer (P.Z ⊓ V : Subgroup G) := by
  rintro x ⟨n,hn,rfl⟩
  apply mem_centralizer_iff.mpr
  rintro z ⟨hzZ,hzV⟩
  let v : V := ⟨z,hzV⟩
  have hc : (P.pointBlockAction n).2 = 1 := hn.2
  have hfix : evenRepresentation (D.model.permutation ⟨n,n.property.1⟩)
      (D.model.coordinates v).toAdd = (D.model.coordinates v).toAdd := by
    apply Subtype.ext
    funext i
    let a := D.model.pointPermutation P.point n
    change (D.model.coordinates v).toAdd.val (a.val.symm i) = _
    by_cases hi : i ∈ WeightTwoGeometry.support (D.model.coordinates P.point).toAdd
    · have hi' := (WeightTwoGeometry.stabilizer_mem_support _ a⁻¹ i).mpr hi
      exact P.omega_word_support_constant structural escape v hzZ ⟨a.val.symm i,hi'⟩ ⟨i,hi⟩
    · let j : WeightTwoGeometry.Complement (D.model.coordinates P.point).toAdd :=
        ⟨i,Finset.mem_compl.mpr hi⟩
      have hh := P.pointBlockAction_second n j
      rw [hc] at hh
      have hj := (WeightFourLocal.threeLetters _ P.weight_four).injective hh.symm
      have hai : a.val i = i := congrArg Subtype.val hj
      have hinv : a.val.symm i = i := by
        apply a.val.injective
        rw [a.val.apply_symm_apply,hai]
      rw [hinv]
  have h := D.model.equivariant ⟨n,n.property.1⟩ v
  rw [hfix] at h
  have hc' := D.model.coordinates.injective (Multiplicative.toAdd.injective h)
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hc')).symm

/-- The first block residual fixes the entire omega center. -/
theorem firstPointResidual_centralizes_Z
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.firstPointResidual ≤ centralizer (P.Z : Set G) := by
  have hrL : P.firstPointResidual ≤ L :=
    (show P.firstPointResidual ≤ P.Le by
      rw [P.Le_eq_pointResidual_sup structural escape C]; exact le_sup_left).trans
        ((map_subtype_le _).trans inf_le_left)
  apply le_centralizer_iff.mpr
  rw [P.omega_split structural escape]
  exact sup_le (inf_le_right.trans (centralizer_le hrL))
    (le_centralizer_iff.mp ((map_subtype_le _).trans
      (P.firstPointFactor_centralizes_omega_intersection structural escape)))

/-- One inclusion in the identification with the published literal L₁. -/
theorem firstPointResidual_le_L1
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.firstPointResidual ≤ P.L1 := by
  have hrL : P.firstPointResidual ≤ L :=
    (show P.firstPointResidual ≤ P.Le by
      rw [P.Le_eq_pointResidual_sup structural escape C]; exact le_sup_left).trans
        ((map_subtype_le _).trans inf_le_left)
  have h := congrArg (map P.firstPointFactor.subtype)
    (embedded_primeToResidual_eq_of_normal 3
      (primeToResidual 3 P.firstPointFactor) le_rfl)
  rw [map_embedded_primeToResidual_of_hom] at h
  exact h.symm.le.trans (embedded_primeToResidual_mono 3
    (le_inf hrL (P.firstPointResidual_centralizes_Z structural escape C)))

/-- The second block image of C_L(Z) fixes the omitted letter of a
Sylow-central weight-six word, so its prime-to-three residual is trivial. -/
theorem L1_le_firstPointFactor
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : P.L1 ≤ P.firstPointFactor := by
  obtain ⟨z,hz6,hzT⟩ := D.naturalCoordinates.central_representative_weight structural
    (n := 6) (Or.inr (Or.inr rfl))
  have hzZ : (z : G) ∈ P.Z := by
    let := S.chosen.elementary
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow z.property,hzT,
      elemPow_eq_one_of_isElementaryAbelian _ z.property⟩
  obtain ⟨j,hj⟩ := WeightSixGeometry.exists_omitted (D.model.coordinates z).toAdd hz6
  have hz (i : Fin 7) : (D.model.coordinates z).toAdd.val i = 0 ↔ i = j := by
    have h := Finset.ext_iff.mp hj i
    simpa [WeightTwoGeometry.support] using h
  have hjC : j ∈ (WeightTwoGeometry.support (D.model.coordinates P.point).toAdd)ᶜ := by
    apply Finset.mem_compl.mpr
    intro hjS
    have hsub : WeightTwoGeometry.support (D.model.coordinates P.point).toAdd ⊆ {j} := by
      intro i hi
      apply Finset.mem_singleton.mpr
      apply (hz i).mp
      exact (P.omega_word_support_constant structural escape z hzZ ⟨i,hi⟩ ⟨j,hjS⟩).trans
        ((hz j).mpr rfl)
    have hc := Finset.card_le_card hsub
    have hfour : (WeightTwoGeometry.support (D.model.coordinates P.point).toAdd).card = 4 :=
      P.weight_four
    rw [hfour,Finset.card_singleton] at hc
    omega
  let j' : WeightTwoGeometry.Complement (D.model.coordinates P.point).toAdd := ⟨j,hjC⟩
  let k := WeightFourLocal.threeLetters _ P.weight_four j'
  let H := L ⊓ centralizer (P.Z : Set G)
  have hHN : H ≤ P.pointNormalizer := by
    apply le_inf (inf_le_left.trans S.chosen.normalizes)
    exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr P.central))
  let f : H →* Equiv.Perm (Fin 3) :=
    ((MonoidHom.snd _ _).comp P.pointBlockAction).comp (inclusion hHN)
  have hf (x : H) : f x k = k := by
    let n : P.pointNormalizer := inclusion hHN x
    have hfix : V.normalizerMonoidHom ⟨n,n.property.1⟩ z = z := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp x.property.2) _ hzZ).symm
    have he := D.model.equivariant ⟨n,n.property.1⟩ z
    rw [hfix] at he
    have hletter := (WeightSixGeometry.fixes_iff (D.model.coordinates z).toAdd hj _).mp he.symm
    have hc : WeightTwoGeometry.complementPermutation _ (D.model.pointPermutation P.point n) j' = j' :=
      Subtype.ext hletter
    change (P.pointBlockAction n).2 (WeightFourLocal.threeLetters _ P.weight_four j') = _
    rw [P.pointBlockAction_second n j',hc]
  let f' := f.codRestrict (MulAction.stabilizer (Equiv.Perm (Fin 3)) k) hf
  have hcard : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 3)) k) = 2 := by
    classical
    rw [Nat.card_eq_fintype_card]
    have h : ∀ k : Fin 3, Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin 3)) k) = 2 := by
      decide +kernel
    exact h k
  have hr : primeToResidual 3 H ≤ f'.ker :=
    primeToResidual_le_ker f' (by rw [hcard]; decide)
  rintro x ⟨y,hy,rfl⟩
  refine ⟨inclusion hHN y,⟨mem_top _,?_⟩,rfl⟩
  exact congrArg Subtype.val (hr hy)

/-- The first source block residual is the published literal L₁=O^{3′}(C_L(Z)). -/
theorem firstPointResidual_eq_L1
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.firstPointResidual = P.L1 := by
  apply le_antisymm (P.firstPointResidual_le_L1 structural escape C)
  have h := congrArg (map (L ⊓ centralizer (P.Z : Set G)).subtype)
    (embedded_primeToResidual_eq_of_normal 3
      (primeToResidual 3 (L ⊓ centralizer (P.Z : Set G) : Subgroup G)) le_rfl)
  rw [map_embedded_primeToResidual_of_hom] at h
  exact h.symm.le.trans (embedded_primeToResidual_mono 3
    (P.L1_le_firstPointFactor structural escape))

/-- The source product now has the published literal first factor. -/
theorem Le_eq_L1_sup_secondPointResidual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Le = P.L1 ⊔ P.secondPointResidual := by
  rw [P.Le_eq_pointResidual_sup structural escape C,
    P.firstPointResidual_eq_L1 structural escape C]

/-- Relative normality of the second block residual in the original point normalizer. -/
theorem secondPointResidual_normalized :
    P.pointNormalizer ≤ normalizer (P.secondPointResidual : Set G) :=
  P.secondPointFactor_normalized.trans (normalizer_le_normalizer_characteristic_image
    P.secondPointFactor (primeToResidual 3 P.secondPointFactor))

/-- The first factor fixes Z, so the second block residual moves the full seed. -/
theorem Le_commutator_eq_secondPointResidual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ⁅P.Z,P.Le⁆ = ⁅P.Z,P.secondPointResidual⁆ := by
  have hproduct := P.Le_eq_L1_sup_secondPointResidual structural escape C
  have hL1 : P.L1 ≤ P.Le := hproduct ▸ le_sup_left
  have hR : P.secondPointResidual ≤ P.Le := hproduct ▸ le_sup_right
  have hLeN : P.Le ≤ P.pointNormalizer := by
    rw [P.Le_eq_pointNormalizer_primeToResidual structural C]
    exact map_subtype_le _
  have hn : P.L1 ≤ normalizer (⁅P.Z,P.secondPointResidual⁆ : Subgroup G) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    let f := (MulAut.conj x).toMonoidHom
    have hZ : P.Z.map f = P.Z :=
      mem_normalizer_iff_map_conj_eq.mp ((P.L1_centralizes_Z.trans
        (Subgroup.centralizer_le_normalizer _)) hx)
    have hR : P.secondPointResidual.map f = P.secondPointResidual :=
      mem_normalizer_iff_map_conj_eq.mp
        (P.secondPointResidual_normalized (hLeN (hL1 hx)))
    have hm : (⁅P.Z,P.secondPointResidual⁆ : Subgroup G).map f =
        ⁅P.Z,P.secondPointResidual⁆ := by rw [map_commutator,hZ,hR]
    exact hm ▸ mem_map_of_mem f hy
  apply le_antisymm ?_ (commutator_mono le_rfl hR)
  rw [hproduct,commutator_comm P.Z]
  apply commutator_sup_le_of_relative_normal (P.L1 ⊔ P.secondPointResidual)
    P.L1 P.secondPointResidual P.Z ⁅P.Z,P.secondPointResidual⁆
    (sup_le hn (normalizer_commutator_ge_right P.Z P.secondPointResidual))
    le_sup_left le_sup_right
  · rw [commutator_eq_bot_iff_le_centralizer.mpr P.L1_centralizes_Z]
    exact bot_le
  · exact (commutator_comm P.secondPointResidual P.Z).le

/-- An original weight-two point in the actual second block residual seed. -/
theorem exists_weight_two_in_secondPointResidual_commutator
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ ⁅P.Z,P.secondPointResidual⁆ := by
  simpa only [P.Le_commutator_eq_secondPointResidual structural escape C] using
    P.exists_weight_two_in_Le_commutator structural

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
