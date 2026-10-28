module
public import Theory.GroupTheory.SylowCharacteristicKernelLifting
public import Theory.GroupTheory.MinimalParabolicCentral
/-!
# Generating Sylow pairs with no invariant normal subgroup

A specified automorphism of S fixes no nontrivial subgroup whose ambient
image is normal. This implies the usual characteristic-subgroup condition.
For a nontrivial Sylow with a unique maximal overgroup, a conjugate generates
the ambient group together with S. Twisting that conjugacy by the specified
automorphism then fixes no nontrivial S-normal subgroup. All subgroup maps
are the literal inclusions and conjugation maps.

Source: Niles, *Pushing-up in finite groups* (1979), Main Hypothesis and
Lemmas 2.2(4), 2.3, printed pp.29–30. This is the initial pair for the
intersection diagram, not its later structure theorem.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H]

@[expose] def NoInvariantNormal (S : Subgroup H) (α : MulAut S) : Prop :=
  ∀ A : Subgroup S, (A.map S.subtype).Normal → A.map α.toMonoidHom = A → A = ⊥

theorem NoInvariantNormal.noCharacteristicNormal {S : Subgroup H} {α : MulAut S}
    (h : NoInvariantNormal S α) : NoCharacteristicNormal S := by
  intro A hA hn
  exact h A hn ((characteristic_iff_map_eq.mp hA) α)

noncomputable def twistedConjugacy (S : Subgroup H) (α : MulAut S) (g : H) :
    S ≃* S.map (MulAut.conj g).toMonoidHom :=
  α.trans ((MulAut.conj g).subgroupMap S)

private theorem normal_map_normalizes (S : Subgroup H) (A : Subgroup S) [A.Normal] :
    S ≤ normalizer (A.map S.subtype : Set H) := by
  have h := A.le_normalizer_map S.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, S.range_subtype] using h

private theorem twistedConjugacy_map (S : Subgroup H) (α : MulAut S) (g : H)
    (A : Subgroup S) :
    (A.map (twistedConjugacy S α g).toMonoidHom).map
        (S.map (MulAut.conj g).toMonoidHom).subtype =
      ((A.map α.toMonoidHom).map S.subtype).map (MulAut.conj g).toMonoidHom := by
  simp only [map_map]
  rfl

/-- Niles 2.3: the literal twist of a generating Sylow pair fixes no nontrivial normal subgroup. -/
theorem twistedConjugacy_no_fixed_normal (S : Subgroup H) (α : MulAut S) (g : H)
    (hno : NoInvariantNormal S α)
    (hgen : S ⊔ S.map (MulAut.conj g).toMonoidHom = ⊤)
    (A : Subgroup S) [A.Normal]
    (hfix : (A.map (twistedConjugacy S α g).toMonoidHom).map
      (S.map (MulAut.conj g).toMonoidHom).subtype = A.map S.subtype) : A = ⊥ := by
  let T := S.map (MulAut.conj g).toMonoidHom
  let φ := twistedConjugacy S α g
  have hS := normal_map_normalizes S A
  have hT : T ≤ normalizer (A.map S.subtype : Set H) := by
    have : (A.map φ.toMonoidHom).Normal := (inferInstance : A.Normal).map _ φ.surjective
    simpa only [T, φ, hfix] using normal_map_normalizes T (A.map φ.toMonoidHom)
  have hN : (A.map S.subtype).Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hS hT))
  let _ := hN
  apply hno A hN
  apply map_injective S.subtype_injective
  apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [←twistedConjugacy_map, hfix]
  exact (Normal.map_conj_eq (A.map S.subtype) g).symm

/-- The generating conjugate pair in Niles 2.2(4), in the nonnormal Sylow case. -/
theorem exists_conjugate_sup_eq_top_of_uniqueMaximal [Finite H]
    {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (hn : ¬ (S : Subgroup H).Normal) :
    ∃ g : H, (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ := by
  by_contra hbad
  push Not at hbad
  obtain ⟨M,hM,_⟩ := hu.2
  have hNM : normalClosure (S : Set H) ≤ M := by
    rw [normalClosure,closure_le]
    intro x hx
    obtain ⟨y,hy,hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hxy
    exact (le_sup_right.trans (hu.le_maximal hM le_sup_left
      (lt_top_iff_ne_top.mpr (hbad g)))) (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)
  have he := S.normal_eq_top_of_uniqueMaximal hu hn (normalClosure (S : Set H)) le_normalClosure
  exact hM.2.ne (top_unique (he ▸ hNM))

/-- A nontrivial Sylow satisfying the Main Hypothesis is not ambient-normal. -/
theorem NoInvariantNormal.not_normal {S : Subgroup H} {α : MulAut S}
    (hno : NoInvariantNormal S α) (hne : S ≠ ⊥) : ¬ S.Normal := by
  intro hn
  let _ := hn
  have ht : (⊤ : Subgroup S) = ⊥ := hno ⊤
    (by simpa only [← MonoidHom.range_eq_map, range_subtype] using hn)
    (by simp)
  have hh := congrArg (Subgroup.map S.subtype) ht
  exact hne (by simpa only [← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] using hh)

/-- The specified Main Hypothesis automorphism supplies the actual initial pair. -/
theorem exists_twisted_generating_pair [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (hno : NoInvariantNormal (S : Subgroup H) α) (hne : (S : Subgroup H) ≠ ⊥) :
    ∃ g : H, (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      ∀ A : Subgroup S, A.Normal →
        (A.map (twistedConjugacy (S : Subgroup H) α g).toMonoidHom).map
          ((S : Subgroup H).map (MulAut.conj g).toMonoidHom).subtype =
          A.map (S : Subgroup H).subtype → A = ⊥ := by
  obtain ⟨g,hg⟩ := exists_conjugate_sup_eq_top_of_uniqueMaximal S hu (hno.not_normal hne)
  refine ⟨g,hg,?_⟩
  intro A hA hfix
  let _ := hA
  exact twistedConjugacy_no_fixed_normal (S : Subgroup H) α g hno hg A hfix

end Theory.GroupTheory
