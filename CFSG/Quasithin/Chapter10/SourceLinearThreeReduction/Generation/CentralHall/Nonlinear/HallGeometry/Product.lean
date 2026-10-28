module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The original marked simple product quotient

The two original Sylow conjugates of L are distinct C-components of L₀.
Their prescribed simple quotients give a surjection with kernel O₂(L₀),
retaining the literal inclusions of L and its chosen conjugate. The
resulting quotient isomorphism supplies the component field required by
`Nonlinear.CartanCoordinates`. In the binary SL₂ application simplicity
is deduced from the source component's quasisimplicity and the model's
trivial center; no additional model classification is assumed.

This generalizes the construction in `SourceA5OriginalProductQuotient`
without modifying that shared module. Source: Aschbacher--Smith, D.3.5--6
and 10.1.1, printed pp.195--196 and 741, used in 10.1.2(5), p.742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The two original C-components have the prescribed simple product quotient. -/
theorem marked_pair_projection (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (e : (L ⧸ pCore 2 L) ≃* S)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ q : localOrbit T L →* S × S,
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

/-- The product marking retains the literal quotient map from the first component. -/
theorem marked_pair_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (e : (L ⧸ pCore 2 L) ≃* S)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (S × S),
      ∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e (QuotientGroup.mk' (pCore 2 L) l), 1) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨f,hf,hk,hfirst,_⟩ := marked_pair_projection D e hn ht htn
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), ?_⟩
  exact hfirst

/-- In the binary SL₂ rows, quasisimplicity comes from the actual component
and trivial center upgrades it to simplicity. No model classification is used. -/
theorem marked_sl2_pair_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {F : Type*} [Field F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
        (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e (QuotientGroup.mk' (pCore 2 L) l), 1) := by
  let := D.quasisimple
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      center (Matrix.SpecialLinearGroup (Fin 2) F)) := IsQuasisimple.simple
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ((QuotientGroup.quotientMulEquivOfEq (Theory.PSL2.sl2_center_eq_bot F)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  exact marked_pair_quotient D e hn

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
