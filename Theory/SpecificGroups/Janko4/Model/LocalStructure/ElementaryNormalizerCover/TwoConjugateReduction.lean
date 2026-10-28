module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuUniqueness
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive
public import Theory.Quasithin.Rank

/-!
# The one-or-two-F argument in the native octad container

Let X lie in a self-centralizing subgroup F, with C(X) contained in the literal
native octad pullback D. Suppose D contains only F and one specified global
conjugate of F, and their intersection lies in the native Mathieu kernel E.
The full N(X) permutes those conjugates which lie in C(X). If only one occurs,
N(X) normalizes F. If both occur, N(X) normalizes their intersection I. Both
self-centralizers contain X, so X ≤ I, and hence C(I) ≤ C(X) ≤ D ≤ max1.
The proved uniqueness of E now gives N(I) ≤ max1.

The maximal-two-local and radical consumers retain the actual conjugator,
whole local normalizer, subgroup inclusions and intrinsic normalizer core.
They do not require a full ambient Sylow or odd index. The native F construction,
self-centralizer, two-occurrence catalogue, intersection and centralizer-container
premises remain explicit inputs from the independent LinearFive owner. In
particular, this module neither asserts that an arbitrary F has an SL5 quotient
nor supplies the full four-local cover. Final assembly must instantiate all these
native inputs.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 1.1.2(ii),
p.485, and the first paragraph of the proof of Proposition 2.2.3, p.491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover
attribute [local irreducible] modelGroup matrixA matrixB

private theorem conjugate_conjugate {G : Type*} [Group G] (F : Subgroup G) (g k : G) :
    (F.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      F.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_le_centralizer {G : Type*} [Group G]
    (X K : Subgroup G) (hK : K ≤ centralizer (X : Set G)) (g : G)
    (hg : g ∈ normalizer (X : Set G)) :
    K.map (MulAut.conj g).toMonoidHom ≤ centralizer (X : Set G) := by
  have he := mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer X hg)
  rw [← he]
  exact map_mono hK

private theorem conjugate_self_centralizing {G : Type*} [Group G]
    (F : Subgroup G) (hF : centralizer (F : Set G) = F) (k : G) :
    centralizer (F.map (MulAut.conj k).toMonoidHom : Set G) =
      F.map (MulAut.conj k).toMonoidHom := by
  let e := MulAut.conj k
  apply le_antisymm
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [← hF]
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
  · have hh := map_centralizer_le_centralizer_image (F : Set G) e.toMonoidHom
    simpa only [hF, Subgroup.coe_map, e] using hh

/-- The two actual global occurrences are permuted by the whole normalizer. -/
theorem normalizer_le_intersection_of_two_conjugates
    (F X D : Subgroup Model) (k : Model)
    (hne : F ≠ F.map (MulAut.conj k).toMonoidHom)
    (hFC : F ≤ centralizer (X : Set Model))
    (hKC : F.map (MulAut.conj k).toMonoidHom ≤ centralizer (X : Set Model))
    (hCD : centralizer (X : Set Model) ≤ D)
    (hocc : ∀ g : Model, F.map (MulAut.conj g).toMonoidHom ≤ D →
      F.map (MulAut.conj g).toMonoidHom = F ∨
        F.map (MulAut.conj g).toMonoidHom = F.map (MulAut.conj k).toMonoidHom) :
    normalizer (X : Set Model) ≤
      normalizer ((F ⊓ F.map (MulAut.conj k).toMonoidHom : Subgroup Model) : Set Model) := by
  intro g hg
  let e := MulAut.conj g
  have h1 := hocc g ((conjugate_le_centralizer X F hFC g hg).trans hCD)
  have h2 : (F.map (MulAut.conj k).toMonoidHom).map e.toMonoidHom = F ∨
      (F.map (MulAut.conj k).toMonoidHom).map e.toMonoidHom =
        F.map (MulAut.conj k).toMonoidHom := by
    have hh := hocc (g*k) (by
      rw [← conjugate_conjugate]
      exact (conjugate_le_centralizer X _ hKC g hg).trans hCD)
    simpa only [e, conjugate_conjugate] using hh
  have hneq : F.map e.toMonoidHom ≠
      (F.map (MulAut.conj k).toMonoidHom).map e.toMonoidHom := by
    intro he
    exact hne (Subgroup.map_injective e.injective he)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (F ⊓ F.map (MulAut.conj k).toMonoidHom).map e.toMonoidHom = _
  rw [map_inf _ _ _ e.injective]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (hneq (h1.trans h2.symm)).elim
  · exact congrArg₂ (· ⊓ ·) h1 h2
  · exact (congrArg₂ (· ⊓ ·) h1 h2).trans (inf_comm _ _)
  · exact (hneq (h1.trans h2.symm)).elim

/-- The F branch of KW 2.2.3, from its literal two-occurrence geometry. -/
theorem two_occurrence_normalizer_alternatives
    (F X : Subgroup Model) (k : Model)
    (hF : centralizer (F : Set Model) = F)
    (hXF : X ≤ F) (hCD : centralizer (X : Set Model) ≤ LinearFive.D)
    (hocc : ∀ g : Model, F.map (MulAut.conj g).toMonoidHom ≤ LinearFive.D →
      F.map (MulAut.conj g).toMonoidHom = F ∨
        F.map (MulAut.conj g).toMonoidHom = F.map (MulAut.conj k).toMonoidHom)
    (hIE : F ⊓ F.map (MulAut.conj k).toMonoidHom ≤ embeddedKernel) :
    normalizer (X : Set Model) ≤ normalizer (F : Set Model) ∨
      normalizer (X : Set Model) ≤ max1 := by
  have hFC : F ≤ centralizer (X : Set Model) := by
    rw [← hF]
    exact centralizer_le hXF
  by_cases heq : F = F.map (MulAut.conj k).toMonoidHom
  · left
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (hocc g ((conjugate_le_centralizer X F hFC g hg).trans hCD)).elim
      id (fun hh => hh.trans heq.symm)
  by_cases hKC : F.map (MulAut.conj k).toMonoidHom ≤ centralizer (X : Set Model)
  · right
    have hXK : X ≤ F.map (MulAut.conj k).toMonoidHom := by
      rw [← conjugate_self_centralizing F hF k]
      intro x hx y hy
      exact (hKC hy x hx).symm
    have hXI : X ≤ F ⊓ F.map (MulAut.conj k).toMonoidHom := le_inf hXF hXK
    have hCM : centralizer ((F ⊓ F.map (MulAut.conj k).toMonoidHom : Subgroup Model) : Set Model) ≤ max1 :=
      (centralizer_le hXI).trans (hCD.trans LinearFive.D_le_M)
    exact (normalizer_le_intersection_of_two_conjugates F X LinearFive.D k heq hFC hKC hCD hocc).trans
      (normalizer_le_mathieu_of_kernel_and_centralizer _ hIE hCM)
  · left
    intro g hg
    have hgC := conjugate_le_centralizer X F hFC g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (hocc g (hgC.trans hCD)).resolve_right (fun he => hKC (he ▸ hgC))


/-- The native F branch after an arbitrary literal ambient conjugation. The
occurrence catalogue is still the one in the fixed octad pullback D. -/
theorem two_occurrence_conjugate_normalizer_alternatives
    (F X : Subgroup Model) (k g : Model)
    (hF : centralizer (F : Set Model) = F)
    (hXF : X ≤ F) (hCD : centralizer (X : Set Model) ≤ LinearFive.D)
    (hocc : ∀ q : Model, F.map (MulAut.conj q).toMonoidHom ≤ LinearFive.D →
      F.map (MulAut.conj q).toMonoidHom = F ∨
        F.map (MulAut.conj q).toMonoidHom = F.map (MulAut.conj k).toMonoidHom)
    (hIE : F ⊓ F.map (MulAut.conj k).toMonoidHom ≤ embeddedKernel) :
    normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model) ≤
        (normalizer (F : Set Model)).map (MulAut.conj g).toMonoidHom ∨
      normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model) ≤
        max1.map (MulAut.conj g).toMonoidHom := by
  rw [← map_equiv_normalizer_eq]
  exact (two_occurrence_normalizer_alternatives F X k hF hXF hCD hocc hIE).imp
    (fun h => map_mono h) (fun h => map_mono h)

/-- Maximality among two-locals turns the two occurrence alternatives into
an equality with the full F-normalizer or the literal Mathieu local. -/
theorem maximal_twoLocal_of_two_occurrences
    (F X M : Subgroup Model) [IsElementaryAbelian 2 F] (hFne : F ≠ ⊥)
    (k g : Model) (hF : centralizer (F : Set Model) = F)
    (hXF : X ≤ F) (hCD : centralizer (X : Set Model) ≤ LinearFive.D)
    (hocc : ∀ q : Model, F.map (MulAut.conj q).toMonoidHom ≤ LinearFive.D →
      F.map (MulAut.conj q).toMonoidHom = F ∨
        F.map (MulAut.conj q).toMonoidHom = F.map (MulAut.conj k).toMonoidHom)
    (hIE : F ⊓ F.map (MulAut.conj k).toMonoidHom ≤ embeddedKernel)
    (hM : IsMaximalTwoLocal M)
    (hMX : M = normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model)) :
    M = (normalizer (F : Set Model)).map (MulAut.conj g).toMonoidHom ∨
      M = max1.map (MulAut.conj g).toMonoidHom := by
  have hlocal : IsTwoLocal (normalizer (F : Set Model)) :=
    ⟨F,hFne,IsElementaryAbelian.isPGroup 2 F,rfl⟩
  rcases two_occurrence_conjugate_normalizer_alternatives F X k g hF hXF hCD hocc hIE
    with h | h
  · exact Or.inl (hM.eq_of_le (hlocal.map_equiv (MulAut.conj g)) (hMX ▸ h))
  · exact Or.inr (hM.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g)) (hMX ▸ h))

/-- Literal radical restriction for the native two-occurrence branch. The
normalizer, denominator and core all refer to the same embedded local conjugate. -/
theorem radical_local_of_two_occurrences
    (P F X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 F] (hFne : F ≠ ⊥)
    (k g : Model) (hF : centralizer (F : Set Model) = F)
    (hXF : X ≤ F) (hCD : centralizer (X : Set Model) ≤ LinearFive.D)
    (hocc : ∀ q : Model, F.map (MulAut.conj q).toMonoidHom ≤ LinearFive.D →
      F.map (MulAut.conj q).toMonoidHom = F ∨
        F.map (MulAut.conj q).toMonoidHom = F.map (MulAut.conj k).toMonoidHom)
    (hIE : F ⊓ F.map (MulAut.conj k).toMonoidHom ≤ embeddedKernel)
    (hNX : normalizer (P : Set Model) ≤
      normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model)) :
    ∃ M : Subgroup Model, IsTwoLocal M ∧
      (M = (normalizer (F : Set Model)).map (MulAut.conj g).toMonoidHom ∨
        M = max1.map (MulAut.conj g).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  have hlocal : IsTwoLocal (normalizer (F : Set Model)) :=
    ⟨F,hFne,IsElementaryAbelian.isPGroup 2 F,rfl⟩
  obtain ⟨M,hM,hrow,hNM⟩ : ∃ M : Subgroup Model, IsTwoLocal M ∧
      (M = (normalizer (F : Set Model)).map (MulAut.conj g).toMonoidHom ∨
        M = max1.map (MulAut.conj g).toMonoidHom) ∧ normalizer (P : Set Model) ≤ M := by
    rcases two_occurrence_conjugate_normalizer_alternatives F X k g hF hXF hCD hocc hIE
      with h | h
    · exact ⟨_,hlocal.map_equiv (MulAut.conj g),Or.inl rfl,hNX.trans h⟩
    · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g),Or.inr rfl,hNX.trans h⟩
  have hPM := P.le_normalizer.trans hNM
  have hN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hN
  refine ⟨M,hM,hrow,hNM,hPM,?_,hP.subgroupOf_of_normalizer_normalizes M hPM hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
