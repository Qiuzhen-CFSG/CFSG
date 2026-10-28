module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolicData
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondRecognition

/-!
# The original cubic vertex: marked core input and conditional recognition

The first endpoint marks the original common Sylow by the concrete Tits Sylow.
Pulling back the actual two-core retains its original embedding in X = YT.
Its index is two, and the original elementary plane V of order four lies in
its center because O₂(X) = C_X(V). These facts supply the finite core census.

The separate conditional consumer identifies the whole original X from a
marked reflection satisfying the concrete three-coset equations. It derives
all orders and generation from the source. Constructing that reflection and
identifying the pulled-back core remain separate obligations; this module
does not assert that the second endpoint has been identified from hfirst alone.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21,
pp.988--989. Concrete generator conventions: Parrott (1972), §5, p.683.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]

/-- Restrict the first-endpoint equivalence and use conjugacy of its Sylows. -/
noncomputable def sylowEquivOfFirst (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (eH : first ≃* H) : S ≃* (T : Subgroup G) := by
  let P := T.subtype hTH
  let Q := P.mapSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let a : P ≃* Q := (P : Subgroup H).equivMapOfInjective
    eH.symm.toMonoidHom eH.symm.injective
  let b : firstSylowTwo ≃* S :=
    (MulEquiv.subgroupCongr firstSylowTwo_coe).trans (subgroupOfEquivOfLe sylow_le_first)
  exact b.symm.trans ((Sylow.equiv firstSylowTwo Q).trans
    (a.symm.trans (subgroupOfEquivOfLe hTH)))

/-- The marking followed by the actual inclusion of the common Sylow in X. -/
def sylowMap (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G)) : S →* X :=
  (inclusion hTX).comp σ.toMonoidHom

/-- Pull back the intrinsic core along the original Sylow inclusion. -/
def coreInMarkedSylow (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G)) : Subgroup S :=
  (pCore 2 X).comap (sylowMap T X hTX σ)

/-- The pullback is the original core, since that normal two-group lies in T. -/
noncomputable def coreEquiv (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G)) :
    coreInMarkedSylow T X hTX σ ≃* pCore 2 X := by
  let j := sylowMap T X hTX σ
  let K := coreInMarkedSylow T X hTX σ
  let f : K →* pCore 2 X := (j.comp K.subtype).codRestrict _ (fun x => x.property)
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact σ.injective ((inclusion_injective hTX) (congrArg Subtype.val h))
  · intro q
    have hq : q.val.val ∈ (T : Subgroup G) :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hTX) q.property
    obtain ⟨s,hs⟩ := σ.surjective ⟨q.val.val,hq⟩
    have hj : j s = q.val := by
      apply Subtype.ext
      exact congrArg (fun t : (T : Subgroup G) => (t : G)) hs
    exact ⟨⟨s,show j s ∈ pCore 2 X from hj ▸ q.property⟩,Subtype.ext hj⟩

omit [Finite G] in
theorem sylowMap_range (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G)) :
    (sylowMap T X hTX σ).range = (T : Subgroup G).subgroupOf X := by
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    exact (σ s).property
  · intro hx
    obtain ⟨s,hs⟩ := σ.surjective ⟨x.val,hx⟩
    exact ⟨s,Subtype.ext (congrArg (fun t : (T : Subgroup G) => (t : G)) hs)⟩

private theorem center_card_of_core_centralizer (X V : Subgroup G)
    [IsMulCommutative V] (hVX : V ≤ X)
    (hcore : X.pCoreIn 2 = X ⊓ centralizer (V : Set G)) :
    Nat.card V ≤ Nat.card (center (pCore 2 X)) := by
  let Q := X.pCoreIn 2
  have hVQ : V ≤ Q := by
    rw [show Q = X ⊓ centralizer (V : Set G) from hcore]
    exact le_inf hVX (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hQV : Q ≤ centralizer (V : Set G) := by
    change X.pCoreIn 2 ≤ _
    rw [hcore]
    exact inf_le_right
  let f : V → center Q := fun v => ⟨inclusion hVQ v, mem_center_iff.mpr (by
    intro q
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hQV q.property) v v.property).symm)⟩
  have hf : Function.Injective f := by
    intro x y h
    exact (inclusion_injective hVQ) (congrArg Subtype.val h)
  let eQ : pCore 2 X ≃* Q :=
    (pCore 2 X).equivMapOfInjective X.subtype X.subtype_injective
  exact (Nat.card_le_card_of_injective f hf).trans_eq
    (Nat.card_congr (centerCongr eQ.symm).toEquiv)

/-- The literal source core has index two in the marked Sylow, and its center
contains the original plane. This is the input to the finite core census. -/
theorem source_core_input
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ σ : S ≃* (T : Subgroup G),
      let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      (coreInMarkedSylow T X le_sup_right σ).index = 2 ∧
        4 ≤ Nat.card (center (coreInMarkedSylow T X le_sup_right σ)) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let σ := sylowEquivOfFirst T H hH.1.1.2 hfirst.some
  let d := coreEquiv T X le_sup_right σ
  obtain ⟨_,hMX,_,_,_,hQ,_⟩ :=
    source_tits_first_second_data hG T hempty hM hu hmany hcard e H hH hi hfirst
  have hK : Nat.card (coreInMarkedSylow T X le_sup_right σ) = 1024 :=
    (Nat.card_congr d.toEquiv).trans hQ
  have hcount := (coreInMarkedSylow T X le_sup_right σ).card_mul_index
  rw [hK,sylow_card] at hcount
  have hcore := (source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1
  let := InitialSource.localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hVX : localModule T M ≤ X := (localModule_le T hM.1.2).trans_eq hMX
  have hz := center_card_of_core_centralizer X (localModule T M) hVX hcore
  rw [hcard] at hz
  refine ⟨σ,?_,?_⟩
  · change (coreInMarkedSylow T X le_sup_right σ).index = 2
    omega
  · exact hz.trans_eq (Nat.card_congr (centerCongr d.symm).toEquiv)

/-- Conditional source consumer: the original marked reflection equations
identify the entire original cubic vertex. The equations remain explicit. -/
theorem source_second_of_collection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (σ : S ≃* (T : Subgroup G))
    (r : (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G))
    (hr : (r : G) ∉ (T : Subgroup G))
    (hc : Tits.AmalgamRigidity.SecondExtension.CosetRelations
      (SecondRecognition.generators
        (sylowMap T (sourceResidual M Mc ⊔ (T : Subgroup G)) le_sup_right σ) r)) :
    Nonempty (second ≃* (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let j := sylowMap T X le_sup_right σ
  obtain ⟨_,_,_,_,hX,_,⟨eX⟩⟩ :=
    source_tits_first_second_data hG T hempty hM hu hmany hcard e H hH hi hfirst
  have hj : j.range.index = 3 := by
    rw [sylowMap_range]
    exact SymmetricThreeTwoCore.sylow_index_three eX (T.subtype le_sup_right)
  have hrj : r ∉ j.range := by
    rw [sylowMap_range]
    exact hr
  obtain ⟨a,_,_⟩ := SecondRecognition.exists_marked_equiv j r hc
    (SecondRecognition.generators_generate j r hj hrj) hX
  exact ⟨a⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
