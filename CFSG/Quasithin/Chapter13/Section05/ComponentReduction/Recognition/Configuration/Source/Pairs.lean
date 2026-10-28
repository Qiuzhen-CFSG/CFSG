module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SourceDefs
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.ConjugatePairs
public import Theory.GroupTheory.SymmetricThreeImage

/-!
# Original condition(iv) in the marked component quotient

A conjugator in X/C_X(K*) lifts to the original X. On the generated pair,
the marked quotient has a larger kernel than the actual H/O₂(H) map.
The proved F.9.5(6.i) theorem recognizes the latter pair; a non-two image
of S₃ is still S₃. Thus the literal marked pair condition is supplied.
Source: Aschbacher–Smith13.5.21(iv), printed p.923.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}

private theorem map_conjugate {A B : Type*} [Group A] [Group B]
    (S : Subgroup A) (f : A →* B) (x : A) :
    (S.map (MulAut.conj x).toMonoidHom).map f =
      (S.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext a
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- The source pair condition descends through the actual component centralizer. -/
theorem source_pair_condition (s : Selected D K) (h : D.Hypothesis)
    [(componentCentralizer s h).Normal]
    (hv : D.V ≤ X D K)
    (hp : ∀ x : Hstar D.H, ¬ IsPGroup 2
      (starImage D.H D.V ⊔ (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup _) →
      Nonempty ((starImage D.H D.V ⊔
        (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup _) ≃* Equiv.Perm (Fin 3))) :
    PairCondition s h := by
  intro x hn
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (componentCentralizer s h) x
  let q := QuotientGroup.mk' (componentCentralizer s h)
  let A := D.V.subgroupOf (X D K)
  let P := A ⊔ A.map (MulAut.conj x).toMonoidHom
  let f := (starHom s h).comp P.subtype
  let g := q.comp P.subtype
  have hf : f.range = starImage D.H D.V ⊔
      (starImage D.H D.V).map (MulAut.conj (starHom s h x)).toMonoidHom := by
    rw [MonoidHom.range_comp,range_subtype,Subgroup.map_sup,map_conjugate,starHom_map s h D.V hv]
  have hg : g.range = markedPair s h (q x) := by
    rw [MonoidHom.range_comp,range_subtype,Subgroup.map_sup,map_conjugate]
    rfl
  have hk : f.ker ≤ g.ker := by
    intro a ha
    change q (a : X D K) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    change starHom s h (a : X D K) ∈ centralizer (starImage D.H K : Set (Hstar D.H))
    change starHom s h (a : X D K) = 1 at ha
    rw [ha]
    exact one_mem _
  have hs : IsPGroup 2 f.range ∨ Nonempty (f.range ≃* Equiv.Perm (Fin 3)) := by
    by_cases hh : IsPGroup 2 f.range
    · exact Or.inl hh
    · right
      rw [hf]
      exact hp (starHom s h x) (hf ▸ hh)
  have hn' : ¬ IsPGroup 2 g.range := fun hh => hn (hg ▸ hh)
  obtain ⟨e⟩ := symmetricThree_range_of_kernel_le f g hk hs hn'
  exact ⟨(MulEquiv.subgroupCongr hg.symm).trans e⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
