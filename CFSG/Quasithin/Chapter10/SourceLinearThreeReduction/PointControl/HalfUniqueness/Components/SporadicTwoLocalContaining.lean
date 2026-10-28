module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.OddThreeContaining
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsTwoLocal

/-!
# The source module and the Held/Rudvalis local two-core

If a quasisimple containing component contains the full original orbit, then
V_M survives its central two-core quotient: otherwise L centralizes V_M,
contrary to the nonzero moved module. Every intermediate subgroup inside M
normalizes V_M, so its quotient image has a nontrivial two-core.

Apply this to the join of the original orbit with the full intrinsic Sylow.
The actual Held and Rudvalis two-local catalogues give uniqueness of its
C-components. Solvable-kernel lifting then contradicts the original exchanger.
Thus the original containing pair is distinct in either strict model row,
without a distinctness callback or a claim about arbitrary core-free overgroups.
HeldContaining applies the result to exclude Held and restrict Rudvalis to
an original Suzuki quotient. The remaining model exclusions and zero-kernel
normalizer stay with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only
independent source input, supplied by qt-d-10-nona5-point-selection and finally
discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private theorem uniqueness (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The surviving full module supplies the literal quotient overgroup two-core. -/
theorem source_fullModule_core_image_ne_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {K P : Subgroup G} [IsQuasisimple K]
    (hOP : localOrbit T L ≤ P) (hPM : P ≤ D.maximalLocal) (hPK : P ≤ K) :
    pCore 2 ((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ ⊥ := by
  let V := D.fullModule
  let q := QuotientGroup.mk' (pCore 2 K)
  let A := (P.subgroupOf K).map q
  let W := (V.subgroupOf K).map q
  have hVP : V ≤ P := D.fullModule_le_orbit.trans hOP
  have hVK : V ≤ K := hVP.trans hPK
  have hLK : L ≤ K := (le_componentOrbit L T).trans (hOP.trans hPK)
  have hWA : W ≤ A := map_mono (comap_mono hVP)
  have hn : A ≤ normalizer (W : Set (K ⧸ pCore 2 K)) := by
    have hh : P.subgroupOf K ≤ normalizer (V.subgroupOf K : Set K) := by
      rw [←subgroupOf_normalizer_eq hVK]
      exact comap_mono (hPM.trans D.maximalLocal_normalizes_fullModule)
    exact (map_mono hh).trans (le_normalizer_map q)
  let := D.fullModule_elementary (uniqueness D)
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 (W.subgroupOf A) := IsElementaryAbelian.subgroupOf hWA
  have hWn : (W.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hWA).mpr hn
  have hcore : W.subgroupOf A ≤ pCore 2 A := le_sSup ⟨hWn,IsElementaryAbelian.isPGroup 2 _⟩
  have hW : W ≠ ⊥ := by
    intro he
    have hk : V.subgroupOf K ≤ pCore 2 K := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
    have hc : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      exact congrArg K.subtype (mem_center_iff.mp
        (IsQuasisimple.pCore_le_center 2 (hk (show (⟨v,hVK hv⟩ : K) ∈ V.subgroupOf K from hv)))
        ⟨l,hLK hl⟩)
    exact source_full_moved_ne_bot D (commutator_eq_bot_iff_le_centralizer.mpr hc)
  intro he
  apply hW
  have hb : W.subgroupOf A = ⊥ := bot_unique (hcore.trans_eq he)
  have hm := congrArg (Subgroup.map A.subtype) hb
  simpa only [map_subgroupOf_eq_of_le hWA,Subgroup.map_bot] using hm

/-- Two-local component uniqueness suffices after the source module supplies the core. -/
theorem ContainingPair.not_orbit_le_of_twoLocal_component_unique
    (C : ContainingPair D H t K₁ K₂) {K : Subgroup G}
    [IsQuasisimple K] (hK : K ∈ cComponentsIn H)
    (hu : ∀ (S : Sylow 2 (K ⧸ pCore 2 K)) (P : Subgroup (K ⧸ pCore 2 K)),
      (S : Subgroup (K ⧸ pCore 2 K)) ≤ P → pCore 2 P ≠ ⊥ →
      ∀ B C : Subgroup P, B.IsCComponent → C.IsCComponent → B = C) :
    ¬ localOrbit T L ≤ K := by
  intro hOK
  let O := localOrbit T L
  have hLO : L ≤ O := le_componentOrbit L T
  have hLK : L ≤ K := hLO.trans hOK
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  have hLK' : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K := by
    simpa only [hid,Subgroup.map_id] using hLK
  obtain ⟨S,hS,_⟩ := C.local_sylow_in_containing (one_mem _) hK hLK'
  let P := O ⊔ (S : Subgroup K).map K.subtype
  have hPK : P ≤ K := sup_le hOK (map_subtype_le _)
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rw [hS,subgroupOf_map_subtype]
    exact inf_le_left.trans inf_le_left
  have hON : (O.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show O ≤ P from le_sup_left)).mpr
      (sup_le O.le_normalizer (hST.trans (le_normalizer_componentOrbit L T)))
  let e : O ≃* O.subgroupOf P := (subgroupOfEquivOfLe (show O ≤ P from le_sup_left)).symm
  let f : O →* P := (O.subgroupOf P).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := (O.subgroupOf P).subtype_injective.comp e.injective
  have hOt : O.map (MulAut.conj t).toMonoidHom = O :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T C.t_mem)
  let τ : MulAut O := ((MulAut.conj t).subgroupMap O).trans (MulEquiv.subgroupCongr hOt)
  let A := L.subgroupOf O
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent := D.maximal.1.1.subgroupOf_of_le hLO (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hAf : (A.map f).IsCComponent := by
    simpa only [map_map] using (hA.map_equiv e).map_subtype hON.isSubnormal
  have hBf : (B.map f).IsCComponent := by
    simpa only [map_map] using (hB.map_equiv e).map_subtype hON.isSubnormal
  let j : P ≃* P.subgroupOf K := (subgroupOfEquivOfLe hPK).symm
  have hSP : (S : Subgroup K) ≤ P.subgroupOf K := by
    intro x hx
    exact (show (S : Subgroup K).map K.subtype ≤ P from le_sup_right) (mem_map_of_mem K.subtype hx)
  have hPM : P ≤ D.maximalLocal :=
    sup_le O.le_normalizer (hST.trans (le_normalizer_componentOrbit L T))
  have hcore := source_fullModule_core_image_ne_bot D
    (show localOrbit T L ≤ P from le_sup_left) hPM hPK
  let q := QuotientGroup.mk' (pCore 2 K)
  let g := q.subgroupMap (P.subgroupOf K)
  let : Group.IsNilpotent q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isNilpotent
  let : Group.IsSolvable g.ker := by
    rw [show g = q.subgroupMap (P.subgroupOf K) from rfl,ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (P.subgroupOf K).subtype.subgroupComap q.ker) (fun a b he =>
        Subtype.ext (Subtype.ext (congrArg (fun x : q.ker => (x : K)) he)))
  have hjA := hAf.map_equiv j
  have hjB := hBf.map_equiv j
  have hh := hu (S.mapSurjective (QuotientGroup.mk'_surjective _))
    ((P.subgroupOf K).map q) (map_mono hSP) hcore _ _
    (cComponent_map_of_solvable_ker hjA g (q.subgroupMap_surjective _))
    (cComponent_map_of_solvable_ker hjB g (q.subgroupMap_surjective _))
  have he : A.map f = B.map f := by
    apply map_injective (f := j.toMonoidHom) j.injective
    let e := QuotientGroup.quotientKerEquivOfSurjective g (q.subgroupMap_surjective _)
    apply hjA.eq_of_map_quotient_eq hjB g.ker
    apply map_injective (f := e.toMonoidHom) e.injective
    have hc : e.toMonoidHom.comp (QuotientGroup.mk' g.ker) = g := by
      ext x
      rfl
    have hm (I : Subgroup (P.subgroupOf K)) :
        (I.map (QuotientGroup.mk' g.ker)).map e.toMonoidHom = I.map g := by
      rw [map_map,hc]
    rw [hm,hm]
    exact hh
  have hab : A = B := map_injective hf he
  have hmA : A.map O.subtype = L := map_subgroupOf_eq_of_le hLO
  have hmB : B.map O.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show O.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp O.subtype from rfl,←map_map,hmA]
  exact C.t_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr
    (hmB.symm.trans ((congrArg (map O.subtype) hab).symm.trans hmA)))


/-- Uniqueness in the first literal quotient forces distinct containing components. -/
theorem ContainingPair.distinct_of_first_held_or_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂) [IsQuasisimple K₁]
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Held.He) ∨
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Rudvalis.Model)) : K₁ ≠ K₂ := by
  intro he
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let : IsQuasisimple (K₁.map H.subtype) := IsQuasisimple.of_mulEquiv a.symm
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hK : K₁.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
  refine C.not_orbit_le_of_twoLocal_component_unique hK ?_ ?_
  · intro S P hSP hc B E hB hE
    rcases hm with e | e
    · exact Section02.MovedMaximality.held_eq_of_le_overgroup_twoCore_ne_bot
        ⟨b.trans e.some⟩ S P P hSP le_rfl hc hB hE
    · exact Section02.MovedMaximality.rudvalis_eq_of_le_overgroup_twoCore_ne_bot
        ⟨b.trans e.some⟩ S P P hSP le_rfl hc hB hE
  rw [C.orbit_eq]
  apply sup_le
  · simpa only [map_subgroupOf_eq_of_le C.left_le] using map_mono (f := H.subtype) C.first_le
  · have hh := map_mono (f := H.subtype) C.second_le
    rwa [map_subgroupOf_eq_of_le C.right_le,←he] at hh

/-- The corresponding second-factor conclusion uses the same source exchanger. -/
theorem ContainingPair.distinct_of_second_held_or_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂) [IsQuasisimple K₂]
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Held.He) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Rudvalis.Model)) : K₁ ≠ K₂ := by
  intro he
  subst K₂
  exact C.distinct_of_first_held_or_rudvalis_quotient hm rfl

/-- Source strictness discharges quasisimplicity for the first actual containing factor. -/
theorem ContainingPair.distinct_of_first_strict_held_or_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁)
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Held.He) ∨
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Rudvalis.Model)) : K₁ ≠ K₂ := by
  let := C.first_quasisimple_of_strict hchoice hmany hn hna hstrict
  exact C.distinct_of_first_held_or_rudvalis_quotient hm

/-- The second source application retains the same exchanger and original half-join. -/
theorem ContainingPair.distinct_of_second_strict_held_or_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂)
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Held.He) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Rudvalis.Model)) : K₁ ≠ K₂ := by
  let := C.second_quasisimple_of_strict hchoice hmany hn hna hstrict
  exact C.distinct_of_second_held_or_rudvalis_quotient hm

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
