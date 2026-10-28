module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed

/-!
# Singular commutators in an outer unitary fixed module

Faithfulness recovers the quotient alignment from the same conjugator which
aligns the outer Hermitian involution. A two-subgroup of its fixed SL₂(q) lies
in an upper Sylow after conjugation over the fixed field, preserving the
symmetric fixed module. With two distinct nonzero root parameters t and u,
the displacements of diag(0,1/t) and diag(0,1/u) sum to diag(t+u,0).

This gives a nonzero singular sum of two actual displacements, fixed by all
the given actors. The ambient consumer transports it to a product of two
commutators in the SAME full fixed Sylow centralizer. No whole-inner-Sylow
identification or replacement of the selected involution is used.
Source: Aschbacher–Smith F.4.29(7),35,37, pp.289,292–293,
refs/quasithin.pdf; the explicit Hermitian calculation includes q=4.
-/

public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.OrthogonalFourMinus.RankOne.AmbientActions
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCommutators
variable (m : ℕ) [NeZero m]

theorem outer_lift_alignment
    (α : MulAut (SpecialLinearGroup (Fin 2) (Field m))) (hα : α^2=1)
    (hout : ¬ ∃ g, α=MulAut.conj g)
    (E : Space m ≃+ Space m) (hE2 : Function.Involutive E)
    (hE : ∀ g x, E (action m g x) = action m (α g) (E x)) :
    ∃ c : SpecialLinearGroup (Fin 2) (Field m),
      (∀ x, E (action m c x)=action m c (conjugationLinear m x)) ∧
      ∀ g, α (c*g*c⁻¹)=c*Theory.PSL2.sl2FieldAut (conjugation m) g*c⁻¹ := by
  obtain ⟨c,hc⟩ := FourOuterFixed.outer_lift_conjugation m α hα hout E hE2 hE
  refine ⟨c,hc,fun g => ?_⟩
  apply action_injective m
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (linearActionHom m c).surjective x
  obtain ⟨z,rfl⟩ := (conjugationLinear m).surjective y
  change action m (α (c*g*c⁻¹)) (action m c (conjugationLinear m z)) =
    action m (c*Theory.PSL2.sl2FieldAut (conjugation m) g*c⁻¹)
      (action m c (conjugationLinear m z))
  have hleft := hE (c*g*c⁻¹) (action m c z)
  rw [hc] at hleft
  have hcancel (v : SpecialLinearGroup (Fin 2) (Field m)) (w : Space m) :
      action m (c*v*c⁻¹) (action m c w)=action m c (action m v w) := by
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      Representation.inv_self_apply]
  rw [hcancel,hc,conjugationLinear_action] at hleft
  exact hleft.symm.trans (hcancel _ _).symm

private theorem root_pair (t u : fixedField m) (ht : t ≠ 0) (hu : u ≠ 0)
    (htu : t ≠ u) :
    ∃ X₁ X₂ : Space m, conjugationLinear m X₁=X₁ ∧ conjugationLinear m X₂=X₂ ∧
      let Y := (action m (upper m t.val) X₁-X₁)+(action m (upper m u.val) X₂-X₂)
      Y ≠ 0 ∧ form m Y=0 ∧ ∀ v : fixedField m, action m (upper m v.val) Y=Y := by
  let X₁ := (coordinates m).symm ((0,t⁻¹),0)
  let X₂ := (coordinates m).symm ((0,u⁻¹),0)
  let Y := (action m (upper m t.val) X₁-X₁)+(action m (upper m u.val) X₂-X₂)
  have ht' : t.val ≠ 0 := fun h => ht (Subtype.ext h)
  have hu' : u.val ≠ 0 := fun h => hu (Subtype.ext h)
  have htfix : conjugation m t.val=t.val := t.property
  have hufix : conjugation m u.val=u.val := u.property
  have hY : Y.val=!![t.val+u.val,0;0,0] := by
    change (rootDifference m t.val X₁).val+(rootDifference m u.val X₂).val=_
    rw [rootDifference_val,rootDifference_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X₁,X₂,coordinates_symm_val,htfix,hufix,ht',hu',CharTwo.add_self_eq_zero]
  refine ⟨X₁,X₂,?_,?_,?_,?_,?_⟩
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X₁,coordinates_symm_val]
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X₂,coordinates_symm_val]
  · intro hz
    have hz' := congrArg (fun X : Space m => X.val 0 0) hz
    change Y.val 0 0=0 at hz'
    rw [hY] at hz'
    apply htu
    apply Subtype.ext
    exact (CharTwo.add_eq_zero).mp hz'
  · apply Subtype.ext
    change Y.val.det=0
    rw [hY,Matrix.det_fin_two]
    simp
  · intro v
    exact ((mem_fixedSpace_upper_iff m Y).mpr
      (by rw [hY]; exact ⟨rfl,rfl⟩)) ⟨upper m v.val,(mem_upperUnipotent _ _).mpr ⟨v.val,rfl⟩⟩

/-- A two-subgroup fixed by quadratic conjugation lies in a fixed-field
conjugate of the fixed root group. -/
theorem fixed_two_group_alignment
    (A : Subgroup (SpecialLinearGroup (Fin 2) (Field m)))
    (hA : IsPGroup 2 A) (hfix : A ≤ involutionCentralizer m) :
    ∃ c : SpecialLinearGroup (Fin 2) (Field m), c ∈ involutionCentralizer m ∧
      A ≤ (fixedRootGroup m).map (MulAut.conj c).toMonoidHom := by
  let j := fixedFieldEmbedding m
  let B := A.comap j
  have hB : IsPGroup 2 B := hA.comap_of_injective j (fixedFieldEmbedding_injective m)
  obtain ⟨P,hP⟩ := hB.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) (fixedField m))
    (upperUnipotentSylow (fixedField m) 2) P
  have hPc : (P : Subgroup _) =
      (upperUnipotent (fixedField m)).map (MulAut.conj c).toMonoidHom := by
    rw [←hc]; rfl
  refine ⟨j c,?_,?_⟩
  · rw [←range_fixedFieldEmbedding]
    exact ⟨c,rfl⟩
  · intro a ha
    have har : a ∈ j.range := by
      change a ∈ (fixedFieldEmbedding m).range
      rw [range_fixedFieldEmbedding]
      exact hfix ha
    obtain ⟨b,rfl⟩ := har
    have hb : b ∈ B := ha
    have hbP := hP hb
    rw [hPc] at hbP
    obtain ⟨v,hv,hvb⟩ := hbP
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent _ _).mp hv
    refine ⟨upper m t.val,(mem_fixedRootGroup_iff m _).mpr ⟨t,rfl⟩,?_⟩
    have hh := congrArg j hvb
    change j (c*transvection zero_ne_one t*c⁻¹)=j b at hh
    rw [map_mul,map_mul,map_inv] at hh
    exact hh

private theorem two_nonidentity {J : Type*} [Group J] [Finite J] (hcard : 4 ≤ Nat.card J) :
    ∃ a b : J, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  let := Fintype.ofFinite J
  have hn : Nontrivial J := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : J)
  have hlt : ({1,a} : Finset J).card < (Finset.univ : Finset J).card := by
    rw [Finset.card_univ,←Nat.card_eq_fintype_card]
    have hb : ({1,a} : Finset J).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hb
  exact ⟨a,b,ha,hb.1,Ne.symm hb.2⟩

/-- Simultaneous alignment of the outer involution, its module lift, and
all the fixed inner actors, using a second conjugator over the fixed field. -/
theorem outer_root_alignment
    (α : MulAut (SpecialLinearGroup (Fin 2) (Field m))) (hα : α^2=1)
    (hout : ¬ ∃ g, α=MulAut.conj g)
    (E : Space m ≃+ Space m) (hE2 : Function.Involutive E)
    (hE : ∀ g x, E (action m g x) = action m (α g) (E x))
    (A : Subgroup (SpecialLinearGroup (Fin 2) (Field m)))
    (hA : IsPGroup 2 A) (hfix : ∀ g : A, α g.val=g.val) :
    ∃ c : SpecialLinearGroup (Fin 2) (Field m),
      (∀ x, E (action m c x)=action m c (conjugationLinear m x)) ∧
      A ≤ (fixedRootGroup m).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c,hc,hαc⟩ := outer_lift_alignment m α hα hout E hE2 hE
  let B := A.map (MulAut.conj c⁻¹).toMonoidHom
  have hB : IsPGroup 2 B := hA.map _
  have hBF : B ≤ involutionCentralizer m := by
    rintro _ ⟨a,ha,rfl⟩
    let g := (MulAut.conj c⁻¹) a
    have hcg : c*g*c⁻¹=a := by dsimp [g]; group
    have hg := hαc g
    rw [hcg,hfix ⟨a,ha⟩] at hg
    have he : Theory.PSL2.sl2FieldAut (conjugation m) g=g := by
      apply (MulAut.conj c).injective
      exact hg.symm.trans hcg.symm
    apply (mem_involutionCentralizer_iff m _).mpr
    intro i j
    exact congrArg (fun M : SpecialLinearGroup (Fin 2) (Field m) => M.val i j) he
  obtain ⟨b,hb,hBb⟩ := fixed_two_group_alignment m B hB hBF
  have hbfix : Matrix.SpecialLinearGroup.map (conjugation m).toRingHom b=b := by
    apply Subtype.ext
    ext i j
    exact (mem_involutionCentralizer_iff m b).mp hb i j
  refine ⟨c*b,?_,?_⟩
  · intro x
    rw [map_mul,Module.End.mul_apply,hc,conjugationLinear_action,hbfix]
    rfl
  · intro a ha
    have hag : (MulAut.conj c⁻¹) a ∈ B := mem_map_of_mem _ ha
    obtain ⟨v,hv,he⟩ := hBb hag
    refine ⟨v,hv,?_⟩
    have hh := congrArg (MulAut.conj c) he
    change c*(b*v*b⁻¹)*c⁻¹=c*(c⁻¹*a*(c⁻¹)⁻¹)*c⁻¹ at hh
    change (c*b)*v*(c*b)⁻¹=a
    calc
      _ = c*(b*v*b⁻¹)*c⁻¹ := by group
      _ = _ := hh
      _ = a := by group

/-- Actual outer fixed two-groups of order at least four have a nonzero
singular sum of two commutators, fixed by the same entire actor group. -/
theorem outer_fixed_displacements
    (α : MulAut (SpecialLinearGroup (Fin 2) (Field m))) (hα : α^2=1)
    (hout : ¬ ∃ g, α=MulAut.conj g)
    (E : Space m ≃+ Space m) (hE2 : Function.Involutive E)
    (hE : ∀ g x, E (action m g x) = action m (α g) (E x))
    (A : Subgroup (SpecialLinearGroup (Fin 2) (Field m)))
    (hA : IsPGroup 2 A) (hfix : ∀ g : A, α g.val=g.val) (hcard : 4 ≤ Nat.card A) :
    ∃ a b : A, a.val ≠ 1 ∧ b.val ≠ 1 ∧
      ∃ X₁ X₂ : Space m, E X₁=X₁ ∧ E X₂=X₂ ∧
        let Y := (action m a.val X₁-X₁)+(action m b.val X₂-X₂)
        Y ≠ 0 ∧ form m Y=0 ∧ ∀ g : A, action m g.val Y=Y := by
  obtain ⟨c,hc,hAc⟩ := outer_root_alignment m α hα hout E hE2 hE A hA hfix
  obtain ⟨a,b,ha,hb,hab⟩ := two_nonidentity hcard
  obtain ⟨a₀,ha₀,he₀⟩ := hAc a.property
  obtain ⟨b₀,hb₀,he₁⟩ := hAc b.property
  obtain ⟨t,rfl⟩ := (mem_fixedRootGroup_iff m _).mp ha₀
  obtain ⟨u,rfl⟩ := (mem_fixedRootGroup_iff m _).mp hb₀
  have ht : t ≠ 0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [←he₀,he]
    change c*transvection zero_ne_one 0*c⁻¹=1
    rw [transvection_coeff_zero,mul_one,mul_inv_cancel]
  have hu : u ≠ 0 := by
    intro he
    apply hb
    apply Subtype.ext
    rw [←he₁,he]
    change c*transvection zero_ne_one 0*c⁻¹=1
    rw [transvection_coeff_zero,mul_one,mul_inv_cancel]
  have htu : t ≠ u := fun he => hab (Subtype.ext (he₀.symm.trans (he ▸ he₁)))
  obtain ⟨X₁,X₂,hX₁,hX₂,hY,hYs,hYfix⟩ := root_pair m t u ht hu htu
  let Y := (action m (upper m t.val) X₁-X₁)+(action m (upper m u.val) X₂-X₂)
  have hconj (v : SpecialLinearGroup (Fin 2) (Field m)) (X : Space m) :
      action m ((MulAut.conj c).toMonoidHom v) (action m c X)=action m c (action m v X) := by
    change action m (c*v*c⁻¹) (action m c X)=_
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      Representation.inv_self_apply]
  have hYc : (action m a.val (action m c X₁)-action m c X₁)+
      (action m b.val (action m c X₂)-action m c X₂)=action m c Y := by
    rw [←he₀,←he₁,hconj,hconj]
    dsimp only [Y]
    rw [map_add,map_sub,map_sub]
  refine ⟨a,b,(fun hh => ha (Subtype.ext hh)),(fun hh => hb (Subtype.ext hh)),
    action m c X₁,action m c X₂,?_,?_,?_,?_,?_⟩
  · rw [hc,hX₁]
  · rw [hc,hX₂]
  · rw [hYc]
    exact fun hh => hY ((linearActionHom m c).injective (hh.trans (map_zero _).symm))
  · rw [hYc,form_preserved]
    exact hYs
  · intro g
    obtain ⟨v,hv,hev⟩ := hAc g.property
    obtain ⟨w,rfl⟩ := (mem_fixedRootGroup_iff m _).mp hv
    rw [hYc,←hev,hconj,hYfix w]

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCommutators
