module
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGroups
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Two cubic conjugates in prime-field PSL₂

The matrices A=[[0,-1],[1,-1]] and U=[[1,1],[0,1]] satisfy
A(U A U⁻¹)=-U(-2). Thus two conjugate cubics contain the entire upper
root group over a prime field. They also contain the Weyl element and
therefore generate the actual projective matrix group.
This supplies a native generating budget for the cubic displacement
comparison in Aschbacher--Smith 10.2.5, printed p.748.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree
open Theory.PSL2 Theory.PSL2.OuterSolvable Theory.PSL2.OuterSolvable.OddCoverage

private def cubicLift (F : Type*) [Field F] : SL(2,F) :=
  ⟨!![0,-1;1,-1],by simp [det_fin_two]⟩

private theorem cubicLift_cube (F : Type*) [Field F] : cubicLift F ^ 3 = 1 := by
  apply Subtype.ext
  change (cubicLift F).val ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicLift,pow_succ,Matrix.mul_apply,Fin.sum_univ_two]

private theorem cubicLift_product (F : Type*) [Field F] :
    cubicLift F * (slUpper 1 * cubicLift F * (slUpper 1)⁻¹) = -slUpper (-2) := by
  apply Subtype.ext
  change (cubicLift F).val * ((slUpper 1).val * (cubicLift F).val *
    Matrix.adjugate (slUpper 1).val) = -(slUpper (-2)).val
  simp only [slUpper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicLift,Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two] <;> ring

private theorem cubicLift_weyl (F : Type*) [Field F] :
    cubicLift F * slUpper 1 = slWeyl F := by
  apply Subtype.ext
  change (cubicLift F).val * (slUpper 1).val = (slWeyl F).val
  rw [slUpper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicLift,slWeyl,Matrix.mul_apply,Fin.sum_univ_two]

private theorem upper_pow {F : Type*} [Field F] (a : F) (n : ℕ) :
    upper a ^ n = upper ((n : F)*a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ,hn,←upper_add]
    congr 1
    simp [add_mul]

private theorem eq_top_of_roots_weyl {F : Type*} [Field F]
    (H : Subgroup PSL(2,F)) (hu : ∀ a : F,upper a ∈ H) (hw : weyl F ∈ H) : H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨A,rfl⟩ := quotientMap_surjective F x
  apply Matrix.SL2.transvection_induction (fun A => quotientMap F A ∈ H) ?_ ?_ A
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu a
    · have he : SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a =
          slWeyl F * slUpper (-a) * (slWeyl F)⁻¹ := by
        apply Subtype.ext
        change (SpecialLinearGroup.transvection one_ne_zero a).val =
          (slWeyl F).val * (slUpper (-a)).val * Matrix.adjugate (slWeyl F).val
        rw [slUpper_val]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [SpecialLinearGroup.transvection_coe,slWeyl,
            Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two]
      rw [he,map_mul,map_mul,map_inv]
      exact H.mul_mem (H.mul_mem hw (hu (-a))) (H.inv_mem hw)
    · exact (hij rfl).elim
  · intro A B ha hb
    rw [map_mul]
    exact H.mul_mem ha hb

/-- Two explicitly constructed conjugate elements of order three generate
the actual prime-field projective matrix group. -/
theorem exists_generating_cubic_pair (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a u : PSL(2,ZMod p), orderOf a = 3 ∧
      closure ({a,u*a*u⁻¹} : Set PSL(2,ZMod p)) = ⊤ := by
  let a := quotientMap (ZMod p) (cubicLift (ZMod p))
  let u : PSL(2,ZMod p) := upper 1
  have ha3 : a^3=1 := by rw [←map_pow,cubicLift_cube,map_one]
  have hane : a ≠ 1 := by
    intro he
    have hh : quotientMap (ZMod p) (cubicLift (ZMod p)) = quotientMap (ZMod p) 1 :=
      he.trans (map_one _).symm
    rcases (quotientMap_eq_iff _ _).mp hh with hh | hh
    · have hh' := congrArg (fun b : SL(2,ZMod p) => b.val 1 0) hh
      simp [cubicLift] at hh'
    · have hh' := congrArg (fun b : SL(2,ZMod p) => b.val 1 0) hh
      simp [cubicLift] at hh'
  refine ⟨a,u,orderOf_eq_prime ha3 hane,?_⟩
  let H := closure ({a,u*a*u⁻¹} : Set PSL(2,ZMod p))
  have ha : a ∈ H := subset_closure (by simp)
  have hb : u*a*u⁻¹ ∈ H := subset_closure (by simp)
  have hroot : upper (-2 : ZMod p) ∈ H := by
    have he : a*(u*a*u⁻¹) = upper (-2 : ZMod p) := by
      change quotientMap (ZMod p) _ * (quotientMap (ZMod p) _ *
        quotientMap (ZMod p) _ * (quotientMap (ZMod p) _)⁻¹) = quotientMap (ZMod p) _
      simp only [←map_mul,←map_inv]
      exact (quotientMap_eq_iff _ _).mpr (Or.inr (cubicLift_product (ZMod p)))
    exact he ▸ H.mul_mem ha hb
  have htwo : (-2 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero]
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  have hall (c : ZMod p) : upper c ∈ H := by
    have hh := H.pow_mem hroot (c/(-2)).val
    rwa [upper_pow,ZMod.natCast_zmod_val,div_mul_cancel₀ _ htwo] at hh
  have hw : weyl (ZMod p) ∈ H := by
    have hh := H.mul_mem ha (hall 1)
    change quotientMap (ZMod p) (cubicLift (ZMod p)) *
      quotientMap (ZMod p) (slUpper 1) ∈ H at hh
    rwa [←map_mul,cubicLift_weyl] at hh
  exact eq_top_of_roots_weyl H hall hw

private theorem cyclic_card_eq {G : Type*} [_root_.Group G] [Finite G] [IsCyclic G]
    (A B : Subgroup G) (hc : Nat.card A = Nat.card B) : A = B := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hsub : (B : Set G).toFinset ⊆
      Finset.univ.filter (fun a : G => a ^ Nat.card B = 1) := by
    intro a ha
    simp only [Set.mem_toFinset] at ha
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : B)))
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    simpa [Set.toFinset_card,←Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
      using IsCyclic.card_pow_eq_one_le (α := G) (Nat.card_pos (α := B)))
  apply eq_of_le_of_card_ge ?_ hc.ge
  intro a ha
  apply Set.mem_toFinset.mp
  rw [heq]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  rw [←hc]
  exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))

private theorem cubic_conjugate (p : ℕ) [Fact p.Prime]
    (P Q : Subgroup PSL(2,ZMod p)) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) :
    ∃ g : PSL(2,ZMod p), P.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨S,hPS⟩ := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hP)).exists_le_sylow
  obtain ⟨T,hQT⟩ := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hQ)).exists_le_sylow
  let : IsCyclic T := T.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (Theory.PSL2.primeField_odd_rank (p := p) (by decide))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(2,ZMod p) S T
  have hST : (S : Subgroup PSL(2,ZMod p)).map (MulAut.conj g).toMonoidHom = T :=
    congrArg Sylow.toSubgroup hg
  have hPT : P.map (MulAut.conj g).toMonoidHom ≤ T :=
    (map_mono hPS).trans_eq hST
  have he := cyclic_card_eq
    ((P.map (MulAut.conj g).toMonoidHom).subgroupOf T) (Q.subgroupOf T) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPT).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv,
        card_map_of_injective (MulAut.conj g).injective,hP,hQ])
  refine ⟨g,?_⟩
  have hh := congrArg (map (T : Subgroup PSL(2,ZMod p)).subtype) he
  simpa only [map_subgroupOf_eq_of_le hPT,map_subgroupOf_eq_of_le hQT] using hh

/-- Every actual order-three subgroup has one conjugate with which it
generates the whole prime-field PSL₂ group. -/
theorem cubic_sup_conjugate_eq_top (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (P : Subgroup PSL(2,ZMod p)) (hP : Nat.card P = 3) :
    ∃ g : PSL(2,ZMod p), P ⊔ P.map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨a,u,ha,hgen⟩ := exists_generating_cubic_pair p hp
  obtain ⟨g,hg⟩ := cubic_conjugate p P (zpowers a) hP ((Nat.card_zpowers a).trans ha)
  have hsup : zpowers a ⊔ (zpowers a).map (MulAut.conj u).toMonoidHom = ⊤ := by
    apply top_unique
    rw [←hgen]
    apply (Subgroup.closure_le _).2
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact (show zpowers a ≤ zpowers a ⊔ (zpowers a).map (MulAut.conj u).toMonoidHom from le_sup_left) (mem_zpowers a)
    · subst x
      exact (show (zpowers a).map (MulAut.conj u).toMonoidHom ≤ zpowers a ⊔ (zpowers a).map (MulAut.conj u).toMonoidHom from le_sup_right) (mem_map_of_mem _ (mem_zpowers a))
  refine ⟨g⁻¹*u*g,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [Subgroup.map_sup,hg,map_top_of_surjective _ (MulAut.conj g).surjective,←hsup,←hg]
  congr 1
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
  group

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree
