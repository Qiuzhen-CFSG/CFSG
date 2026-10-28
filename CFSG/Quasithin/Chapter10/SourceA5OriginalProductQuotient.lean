module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.CComponent.SimplePairProduct

/-!
# The original marked A₅ product quotient

The original nonnormal component has exactly two Sylow conjugates. Inside
its literal orbit L₀, they are distinct C-components with prescribed A₅
quotients. The simple-pair product theorem constructs L₀/O₂(L₀) as their
product, preserving the chosen quotient on L and the same quotient on tLt⁻¹.
No representation, module-type, or odd-core assumption enters the construction.

Source: Aschbacher–Smith D.3.5–7 and 10.1.1, printed pp.195–199 and741.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Conjugation by the chosen Sylow element, included in the literal orbit. -/
def originalConjugateOrbitInclusion {t : G} (ht : t ∈ (T : Subgroup G)) :
    L →* localOrbit T L :=
  ((MulAut.conj t).toMonoidHom.comp L.subtype).codRestrict _ (fun l =>
    (le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj (s : G)).toMonoidHom)
      ⟨t,ht⟩) (mem_map.mpr ⟨l,l.property,rfl⟩))

/-- The original marked product quotient with exact formulas on both factors. -/
theorem source_a5_original_product_quotient (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ q : localOrbit T L →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
        (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) =
        (1,e (QuotientGroup.mk' _ l))) := by
  let R := localOrbit T L
  have hLR : L ≤ R := le_componentOrbit L T
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  let τ : MulAut R := ((MulAut.conj t).subgroupMap R).trans (MulEquiv.subgroupCongr hRt)
  let A := L.subgroupOf R
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hmapA : A.map R.subtype = L := map_subgroupOf_eq_of_le hLR
  have hmapB : B.map R.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show R.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp R.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map R.subtype) he).symm.trans hmapA)
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,←MonoidHom.range_eq_map,range_subtype,hp]
  let a : A ≃* L := subgroupOfEquivOfLe hLR
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let b : A ≃* B := τ.subgroupMap A
  let eB := (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eA
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨q,hq,hk,hfirst,hsecond⟩ :=
    exists_twoCore_product_of_simple_pair A B hA hB hne hgen eA eB
  refine ⟨q,hq,hk,?_,?_⟩
  · intro l
    exact hfirst (a.symm l)
  · intro l
    have hh := hsecond (b (a.symm l))
    change q (originalConjugateOrbitInclusion ht l) =
      (1,eA (QuotientGroup.mk' _ (b.symm (b (a.symm l))))) at hh
    rw [b.symm_apply_apply] at hh
    exact hh


variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

/-- The marked quotient onto the original A₅ factor and its chosen conjugate. -/
noncomputable def originalA5ProductProjection :
    localOrbit T L →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
  (source_a5_original_product_quotient D e hn ht htn).choose

/-- The marked original product projection is onto. -/
theorem originalA5ProductProjection_surjective :
    Function.Surjective (originalA5ProductProjection D e hn ht htn) :=
  (source_a5_original_product_quotient D e hn ht htn).choose_spec.1

/-- Its kernel is the intrinsic two-core of the original orbit. -/
theorem originalA5ProductProjection_ker :
    (originalA5ProductProjection D e hn ht htn).ker = pCore 2 (localOrbit T L) :=
  (source_a5_original_product_quotient D e hn ht htn).choose_spec.2.1

/-- The first coordinate is exactly the prescribed quotient marking of L. -/
theorem originalA5ProductProjection_first (l : L) :
    originalA5ProductProjection D e hn ht htn ⟨l,le_componentOrbit L T l.property⟩ =
      (e (QuotientGroup.mk' _ l),1) :=
  (source_a5_original_product_quotient D e hn ht htn).choose_spec.2.2.1 l

/-- The second coordinate uses the same marking after conjugation by t. -/
theorem originalA5ProductProjection_second (l : L) :
    originalA5ProductProjection D e hn ht htn (originalConjugateOrbitInclusion ht l) =
      (1,e (QuotientGroup.mk' _ l)) :=
  (source_a5_original_product_quotient D e hn ht htn).choose_spec.2.2.2 l

end CFSG.Quasithin.Chapter10
