module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.BinaryFixed
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.SourceAssembly
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking
public import Theory.GroupTheory.PerfectHalfOrderImage

/-!
# The marked A₈ overcomponent in the original A₆ branch

An actual fixed A₆ removes the possible double cover of the containing A₈.
The compatible eight-point marking then identifies the original involution
with a transposition. Its fixed group has order at most 720, so the embedded
perfect A₆ has index at most two and is exactly the fixed solvable residual.
The final constructor preserves the literal overcomponent and actor from
the source pumpup and supplies the exceptional alternative used by 2.5.26.

Source: Aschbacher–Smith 2.5.19(3)(4), printed pp.561–562, and 2.5.26,
printed pp.568–569, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6
open CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
open Theory.SpecificGroups.SymmetricEight.ComponentMarking
open BinaryNaturalDual.FourActors.PermutationCatalogue
variable {G : Type*} [Group G] [Finite G]

/-- A split A₆ subgroup removes the central cover of the A₈ quotient. -/
theorem a8_model_of_quotient
    (L E : Subgroup G) [IsQuasisimple E]
    (hLE : L ≤ E) (eL : L ≃* alternatingGroup (Fin 6))
    (eQ : (E ⧸ center E) ≃* alternatingGroup (Fin 8)) :
    Nonempty (E ≃* alternatingGroup (Fin 8)) := by
  have hm : ClassicalGroup.IsPSL (E ⧸ center E) 4 2 :=
    ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨eQ.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
  have hz : center E = ⊥ := center_eq_bot_four_of_no_six_in_double_cover
    GLS3.Chapter5.SchurPresentation.not_injective_six_to_schurAlternatingGroup_three
    hm (L.subgroupOf E) ⟨(subgroupOfEquivOfLe hLE).trans eL⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans eQ⟩

/-- The actual fixed A₆ marks the containing A₈ and is its fixed solvable residual. -/
theorem marked_a8_fixed_component
    (L E : Subgroup G) [IsQuasisimple E]
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (E : Set G))
    (hL : IsComponentIn L (E ⊓ centralizer ({t} : Set G)))
    (eL : L ≃* alternatingGroup (Fin 6))
    (eQ : (E ⧸ center E) ≃* alternatingGroup (Fin 8)) :
    ∃ e : E ≃* alternatingGroup (Fin 8),
      (∀ k : E, (e.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (e k)) : G) =
        t * k * t⁻¹) ∧
      L = (solvableResidual (E ⊓ centralizer ({t} : Set G) : Subgroup G)).map
        (E ⊓ centralizer ({t} : Set G)).subtype := by
  have hLE : L ≤ E := hL.1.trans inf_le_left
  obtain ⟨eE⟩ := a8_model_of_quotient L E hLE eL eQ
  have hLc : Nat.card L = 360 := (Nat.card_congr eL.toEquiv).trans (by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  have hEc : Nat.card E = 20160 := (Nat.card_congr eE.toEquiv).trans (by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  have hlt : L < E := lt_of_le_of_ne hLE (by
    intro he
    have hc := congrArg (fun D : Subgroup G => Nat.card D) he
    rw [hLc,hEc] at hc
    omega)
  obtain ⟨f,hft,hfE,_⟩ := exists_marked_equiv eE htN ht hlt hL hLc
  let J := E ⊔ zpowers t
  let C := E ⊓ centralizer ({t} : Set G)
  let τ : Equiv.Perm (Fin 8) := Equiv.swap 0 1
  let e : E ≃* alternatingGroup (Fin 8) :=
    (subgroupOfEquivOfLe (show E ≤ J from le_sup_left)).symm.trans
      ((f.subgroupMap (E.subgroupOf J)).trans (MulEquiv.subgroupCongr hfE))
  have he (k : E) : (e k : Equiv.Perm (Fin 8)) =
      f ⟨k, (le_sup_left : E ≤ J) k.property⟩ := rfl
  have htJ : t ∈ J := mem_sup_right (mem_zpowers t)
  have hact (k : E) :
      e (E.normalizerMonoidHom ⟨t,htN⟩ k) = MulAut.conjNormal τ (e k) := by
    apply Subtype.ext
    rw [he]
    change f ((⟨t,htJ⟩ : J) * ⟨k,(le_sup_left : E ≤ J) k.property⟩ *
      (⟨t,htJ⟩ : J)⁻¹) = τ * (e k : Equiv.Perm (Fin 8)) * τ⁻¹
    rw [map_mul,map_mul,map_inv,hft,← he]
  refine ⟨e,?_,?_⟩
  · intro k
    have hh := congrArg (fun y : alternatingGroup (Fin 8) => (e.symm y : G)) (hact k)
    simpa only [e.symm_apply_apply, normalizerMonoidHom_apply_apply_coe] using hh.symm
  · let P : Subgroup (Equiv.Perm (Fin 8)) := (C.subgroupOf J).map f.toMonoidHom
    have hCP : C ≃* P :=
      (subgroupOfEquivOfLe (show C ≤ J from inf_le_left.trans le_sup_left)).symm.trans
        (f.subgroupMap (C.subgroupOf J))
    have hPC : P ≤ alternatingGroup (Fin 8) ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 8))) := by
      rintro _ ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← hfE]
        exact mem_map_of_mem f.toMonoidHom hx.1
      · apply mem_centralizer_singleton_iff.mpr
        have hh : x * (⟨t,htJ⟩ : J) = (⟨t,htJ⟩ : J) * x :=
          Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
        simpa only [map_mul,hft,τ,MulEquiv.coe_toMonoidHom] using congrArg f hh
    have hCc : Nat.card C ≤ 720 := by
      have hh := card_le_of_le hPC
      rw [← Nat.card_congr hCP.toEquiv] at hh
      have hec : Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 8))) :
          Subgroup (Equiv.Perm (Fin 8))) = 720 := by
        change Nat.card (alternatingGroup (Fin 8) ⊓ centralizer
          ({Theory.SpecificGroups.SymmetricEight.Involutions.onePair} : Set (Equiv.Perm (Fin 8))) :
          Subgroup (Equiv.Perm (Fin 8))) = 720
        rw [Nat.card_congr onePairCentralizerEquiv.toEquiv]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      exact hec ▸ hh
    let B := L.subgroupOf C
    have hBc : Nat.card B = 360 := (Nat.card_congr (subgroupOfEquivOfLe hL.1).toEquiv).trans hLc
    have hidx : B.index ≤ 2 := by
      have hh := B.index_mul_card
      rw [hBc] at hh
      omega
    have hres : solvableResidual C ≤ B :=
      (solvableResidual_le_derivedSeries 1).trans (by
        rw [derivedSeries_one]
        exact PerfectHalfOrderImage.commutator_le_of_index_le_two B hidx)
    let : IsQuasisimple L := hL.quasisimple
    apply le_antisymm (le_map_solvableResidual_of_isPerfect L C hL.1)
    have hLC : L ≤ C := hL.1
    exact (map_mono (f := C.subtype) hres).trans_eq (map_subgroupOf_eq_of_le hLC)


/-- The marked A₈ row of the original pumpup supplies the literal exceptional
alternative used in 2.5.26, including its residual and actor equations. -/
theorem source_a8_marked_overcomponent
    (K : Subgroup G) (t i : G) (ht : orderOf t = 2)
    (hKt : IsComponentIn K (centralizer ({t} : Set G)))
    (eK : K ≃* alternatingGroup (Fin 6))
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      t * ((x : centralizer ({i} : Set G)) : G) * t⁻¹)
    (hKX : K ≤ X.map (centralizer ({i} : Set G)).subtype)
    (eQ : (X ⧸ center X) ≃* alternatingGroup (Fin 8)) :
    ∃ E : Subgroup G, IsComponentIn E (centralizer ({i} : Set G)) ∧
      ∃ e : E ≃* alternatingGroup (Fin 8),
        (∀ k : E, (e.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (e k)) : G) =
          t * k * t⁻¹) ∧
        K = (solvableResidual (E ⊓ centralizer ({t} : Set G) : Subgroup G)).map
          (E ⊓ centralizer ({t} : Set G)).subtype := by
  let Gi := centralizer ({i} : Set G)
  let E := X.map Gi.subtype
  have hE : IsComponentIn E Gi := by
    refine ⟨map_subtype_le _,?_⟩
    change IsComponent Gi ((X.map Gi.subtype).comap Gi.subtype)
    rwa [comap_map_eq_self_of_injective Gi.subtype_injective]
  let : IsQuasisimple E := hE.quasisimple
  let f : X ≃* E := X.equivMapOfInjective Gi.subtype Gi.subtype_injective
  have hcenter : (center X).map f.toMonoidHom = center E := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr f ⟨x,hx⟩).property
    · intro x hx
      exact ⟨f.symm x,(centerCongr f).symm ⟨x,hx⟩ |>.property,f.apply_symm_apply x⟩
  let eEQ : (E ⧸ center E) ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.congr _ _ f hcenter).symm.trans eQ
  have htN : t ∈ normalizer (E : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨x,hx,rfl⟩ := hx
      refine ⟨(a ⟨x,hx⟩ : Gi),(a ⟨x,hx⟩).property,?_⟩
      exact hact ⟨x,hx⟩
    · rintro x ⟨y,hy,rfl⟩
      refine ⟨((a.symm ⟨y,hy⟩ : Gi) : G),?_,?_⟩
      · exact mem_map_of_mem Gi.subtype (a.symm ⟨y,hy⟩).property
      · have hh := hact (a.symm ⟨y,hy⟩)
        change t * ((a.symm ⟨y,hy⟩ : Gi) : G) * t⁻¹ = (y : G)
        simpa only [a.apply_symm_apply] using hh.symm
  obtain ⟨e,he,hr⟩ := marked_a8_fixed_component K E t ht htN
    (hKt.restrict (le_inf hKX hKt.1) inf_le_right) eK eEQ
  exact ⟨E,hE,e,he,hr⟩

/-- Application to the exact exceptional-alternative interface of 2.5.26. -/
theorem a8_alternative_of_quotient
    (d : A6ShadowRankOne.RankOneSetup G) (i : G)
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      d.t * ((x : centralizer ({i} : Set G)) : G) * d.t⁻¹)
    (hKX : d.K ≤ X.map (centralizer ({i} : Set G)).subtype)
    (eQ : (X ⧸ center X) ≃* alternatingGroup (Fin 8)) :
    Nonempty (A6ShadowRankOne.A8Alternative d i) := by
  have hKt : d.K ≤ centralizer ({d.t} : Set G) := by
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    have hh : d.t ∈ centralizer (d.K : Set G) :=
      (d.centralizer_K ▸ d.t_mem : d.t ∈ d.S ⊓ centralizer (d.K : Set G)).2
    exact hh k hk
  obtain ⟨E,hE,e,he,hr⟩ := source_a8_marked_overcomponent d.K d.t i d.t_order
    ⟨hKt,d.component_t⟩ d.modelK X hX a hact hKX eQ
  exact ⟨{
    Ki := E
    modelKi := e
    Ki_le_centralizer := hE.1
    component := hE.2
    residual := hr
    t_action := he }⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6
