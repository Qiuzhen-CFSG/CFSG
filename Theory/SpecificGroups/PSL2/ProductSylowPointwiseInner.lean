module

public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Pointwise Sylow fixers in a product of binary SL₂ groups

An automorphism fixing the product of the upper root groups preserves both
actual factors: each cross-coordinate homomorphism kills the upper root group,
and its normal closure is the full SL₂ group by transvection generation.
The established PSL₂ pointwise-fixer theorem then makes both restrictions inner.
Sylow conjugacy transports the calculation to every Sylow two-subgroup.

No factor-permutation or semilinear description is assumed. The argument even
includes the field of two elements. Source application: Aschbacher–Smith,
G.9.3(15) and the exclusion in 15.3.58, printed pp.354,1149.
-/

public section
open Matrix Subgroup BenderSuzuki.Converse BenderSuzuki.ZD.Linear
open BenderSuzuki.MatrixGroups
namespace Theory.PSL2
variable {F : Type*} [Field F] [CharP F 2]

private theorem hom_eq_one_of_upper {D : Type*} [Group D] (f : SL2 F →* D)
    (hf : ∀ t : F, f (uni t) = 1) (g : SL2 F) : f g = 1 := by
  apply Matrix.SL2.transvection_induction (fun g => f g = 1) ?_ ?_ g
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [upper_transvection_eq_uni] using hf t
    · rw [lower_transvection_eq_weyl_uni, map_mul, map_mul, hf, mul_one,
        ← map_mul, weyl_sq, map_one]
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul, hA, hB, one_mul]

variable [Finite F]

private theorem sl2_fixer_inner (a : MulAut (SL2 F))
    (ha : ∀ t : F, a (uni t) = uni t) : ∃ g, a = MulAut.conj g := by
  let e := BenderSuzuki.ZD.Linear.sl2QuotientEquiv F
  let P := (SpecialLinearGroup.upperUnipotentSylow F 2).mapSurjective
    (f := e.toMonoidHom) e.surjective
  apply (MulAut.congr_inner_iff e a).mp
  obtain ⟨g, _, hg⟩ := Theory.PSL2.aut_fixing_sylow_inner P (MulAut.congr e a) (by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F x).mp hx
    change e (a (e.symm (e _))) = e _
    rw [e.symm_apply_apply, upper_transvection_eq_uni, ha])
  exact ⟨g, hg⟩

private theorem product_upper_fixer_inner (a : MulAut (SL2 F × SL2 F))
    (ha : ∀ t : F, a (uni t, 1) = (uni t, 1))
    (hb : ∀ t : F, a (1, uni t) = (1, uni t)) : ∃ g, a = MulAut.conj g := by
  let f₁ : SL2 F →* SL2 F := (MonoidHom.fst _ _).comp
    (a.toMonoidHom.comp (MonoidHom.inl _ _))
  let f₂ : SL2 F →* SL2 F := (MonoidHom.snd _ _).comp
    (a.toMonoidHom.comp (MonoidHom.inr _ _))
  have hcross₁ (g : SL2 F) : (a (g, 1)).2 = 1 :=
    hom_eq_one_of_upper ((MonoidHom.snd _ _).comp
      (a.toMonoidHom.comp (MonoidHom.inl _ _))) (fun t => congrArg Prod.snd (ha t)) g
  have hcross₂ (g : SL2 F) : (a (1, g)).1 = 1 :=
    hom_eq_one_of_upper ((MonoidHom.fst _ _).comp
      (a.toMonoidHom.comp (MonoidHom.inr _ _))) (fun t => congrArg Prod.fst (hb t)) g
  have hf₁ : Function.Injective f₁ := by
    intro g h hgh
    have he := a.injective (Prod.ext hgh ((hcross₁ g).trans (hcross₁ h).symm))
    exact congrArg Prod.fst he
  have hf₂ : Function.Injective f₂ := by
    intro g h hgh
    have he := a.injective (Prod.ext ((hcross₂ g).trans (hcross₂ h).symm) hgh)
    exact congrArg Prod.snd he
  let a₁ : MulAut (SL2 F) := MulEquiv.ofBijective f₁
    ⟨hf₁, Finite.surjective_of_injective hf₁⟩
  let a₂ : MulAut (SL2 F) := MulEquiv.ofBijective f₂
    ⟨hf₂, Finite.surjective_of_injective hf₂⟩
  obtain ⟨g₁, hg₁⟩ := sl2_fixer_inner a₁ (fun t => congrArg Prod.fst (ha t))
  obtain ⟨g₂, hg₂⟩ := sl2_fixer_inner a₂ (fun t => congrArg Prod.snd (hb t))
  refine ⟨(g₁, g₂), ?_⟩
  apply MulEquiv.ext
  intro x
  have he : a x = a (x.1, 1) * a (1, x.2) := by rw [← map_mul]; simp
  have he₁ := congrArg (fun b : MulAut (SL2 F) => b x.1) hg₁
  have he₂ := congrArg (fun b : MulAut (SL2 F) => b x.2) hg₂
  apply Prod.ext
  · simpa [he, hcross₂, MulAut.conj_apply, a₁, f₁] using he₁
  · simpa [he, hcross₁, MulAut.conj_apply, a₂, f₂] using he₂

/-- Every automorphism of the two actual SL₂ factors fixing a Sylow two-subgroup
pointwise is inner. Factor preservation follows from root generation. -/
theorem product_aut_fixing_sylow_inner (S : Sylow 2 (SL2 F × SL2 F))
    (a : MulAut (SL2 F × SL2 F)) (ha : ∀ x ∈ S, a x = x) :
    ∃ g, a = MulAut.conj g := by
  let U := SpecialLinearGroup.upperUnipotent F
  have hsq (x : SL2 F) (hx : x ∈ U) : x * x = 1 := by
    obtain ⟨t, rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F x).mp hx
    rw [upper_transvection_eq_uni, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]
  have hp : IsPGroup 2 (U.prod U) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (x.val : SL2 F × SL2 F) ^ 2 = 1
    rw [pow_two]
    exact Prod.ext (hsq _ x.property.1) (hsq _ x.property.2)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F × SL2 F) P S
  let e : MulAut (SL2 F × SL2 F) := MulAut.conj g
  have hfix (x : SL2 F × SL2 F) (hx : x ∈ P) :
      MulAut.congr e.symm a x = x := by
    have hmem : e x ∈ S := by
      rw [← hg]
      change e x ∈ (P : Subgroup (SL2 F × SL2 F)).map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom hx
    change e.symm (a (e x)) = x
    rw [ha _ hmem]
    exact e.symm_apply_apply x
  apply (MulAut.congr_inner_iff e.symm a).mp
  apply product_upper_fixer_inner
  · intro t
    apply hfix
    apply hP
    refine ⟨?_, U.one_mem⟩
    exact (SpecialLinearGroup.mem_upperUnipotent F _).mpr
      ⟨t, upper_transvection_eq_uni t⟩
  · intro t
    apply hfix
    apply hP
    refine ⟨U.one_mem, ?_⟩
    exact (SpecialLinearGroup.mem_upperUnipotent F _).mpr
      ⟨t, upper_transvection_eq_uni t⟩

end Theory.PSL2
