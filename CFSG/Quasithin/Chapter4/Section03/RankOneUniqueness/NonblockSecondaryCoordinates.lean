module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryGeometry
public import Theory.Representation.SL3.NaturalParabolicFixed
/-!
# Constructing the nonblock root coordinates from the actual local images

The natural section of MSData supplies compatible additive coordinates on
U=Z(Q). Explicit transvections in the covector stabilizer show that
W=[U,L] is exactly the coordinate plane. The actual Sylow image is the
standard upper unipotent group: its fixed points in that plane are exactly
the first coordinate line. This constructs RootCoordinates on the original
root C_W(S∩L), rather than requiring a separately marked root subgroup.

The final application gives the literal secondary PSL₂ quotient, generation
of K by L and K₂, strict component containment, and nontrivial R₂-action on
the full component quotient. The original nonbinary MS classification and
the simultaneous parabolic/Sylow markings, component selection and 4.3.14
bounds remain with qt-d-1222-rankone-uniqueness-nonblock. This conditional
family does not assert existence of MSData or SecondaryData.

Source: Aschbacher--Smith, original 4.3.10--15, printed pp.617--618,
and the line-parabolic clause of C.4.1(3), printed p.151.
-/

noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (d : MSData c n)

private def naturalConjugate (k : K c) (u : U c) : U c :=
  (U c).normalizerMonoidHom ⟨k,d.natural.2.1 k.property⟩ u

private theorem naturalConjugate_coe (k : K c) (u : U c) :
    (naturalConjugate d k u : G) = k * (u : G) * (k : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe (U c) _ _

private theorem natural_coordinates :
    ∃ e : U c ≃* Multiplicative (Fin 3 → d.field.Carrier),
      ∀ (k : K c) (u : U c), (e (naturalConjugate d k u)).toAdd =
        Representation.specialLinearNatural 3 (linearThreeActor d.model k) (e u).toAdd := by
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,he⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans e,
    fun k u => he k u (naturalConjugate d k u) (naturalConjugate_coe d k u)⟩

private def coordinatePlane (F : Type*) [Field F] : Subgroup (Multiplicative (Fin 3 → F)) where
  carrier := {v | v.toAdd 2 = 0}
  one_mem' := rfl
  mul_mem' := by intro x y hx hy; change x.toAdd 2 + y.toAdd 2 = 0; rw [hx,hy,add_zero]
  inv_mem' := by intro x hx; change -x.toAdd 2 = 0; rw [hx,neg_zero]

section Coordinates
variable (e : U c ≃* Multiplicative (Fin 3 → d.field.Carrier))
    (he : ∀ (k : K c) (u : U c), (e (naturalConjugate d k u)).toAdd =
      Representation.specialLinearNatural 3 (linearThreeActor d.model k) (e u).toAdd)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)

include he hL

private theorem displacement_mem (a : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier)
    (ha : a ∈ lineLocalSL d.field.Carrier) (v : Fin 3 → d.field.Carrier) :
    (e.symm (Multiplicative.ofAdd (a.val.mulVec v - v)) : G) ∈ W c := by
  obtain ⟨k,hk,hka⟩ := hL.ge ha
  let u := e.symm (Multiplicative.ofAdd v)
  let w := naturalConjugate d k u * u⁻¹
  have hw : (w : G) = ⁅(k : G),(u : G)⁆ := by
    simp only [w,Subgroup.coe_mul,Subgroup.coe_inv,naturalConjugate_coe]
    rfl
  have hwc : (e w).toAdd = a.val.mulVec v - v := by
    simp only [w,map_mul,map_inv,toAdd_mul,toAdd_inv,he,hka,
      u,MulEquiv.apply_symm_apply,toAdd_ofAdd,Representation.specialLinearNatural_apply,sub_eq_add_neg]
  have hw' : e.symm (Multiplicative.ofAdd (a.val.mulVec v - v)) = w := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hwc.symm
  rw [hw',hw,←d.fullModule,commutator_comm]
  exact commutator_mem_commutator hk u.property

private theorem plane_mem_fullModule (v : Fin 3 → d.field.Carrier) (hv : v 2 = 0) :
    (e.symm (Multiplicative.ofAdd v) : G) ∈ W c := by
  have haxis {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 2) (a : d.field.Carrier) :
      (e.symm (Multiplicative.ofAdd (Pi.single i a)) : G) ∈ W c := by
    let g := transvection hij a
    have hg : g ∈ lineLocalSL d.field.Carrier := by
      rw [mem_lineLocalSL_iff]
      simp [g,transvection_coe,hi]
    have hh := displacement_mem d e he hL g hg (Pi.single j 1)
    have hm : g.val.mulVec (Pi.single j 1) - Pi.single j 1 = Pi.single i a := by
      have ht := Representation.OneCohomology.SLHigherNatural.action_transvection hij a (Pi.single j 1)
      change g.val.mulVec (Pi.single j 1) = _ at ht
      rw [ht,add_sub_cancel_left]
      simp
    rwa [hm] at hh
  have h0 := haxis (by decide : (0 : Fin 3) ≠ 1) (by decide) (v 0)
  have h1 := haxis (by decide : (1 : Fin 3) ≠ 0) (by decide) (v 1)
  have hsum : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    ext i
    fin_cases i <;> simp [hv]
  have hh := (W c).mul_mem h0 h1
  have hm : (e.symm (Multiplicative.ofAdd v) : G) =
      (e.symm (Multiplicative.ofAdd (Pi.single 0 (v 0))) : G) *
      (e.symm (Multiplicative.ofAdd (Pi.single 1 (v 1))) : G) := by
    conv_lhs => rw [hsum]
    rw [ofAdd_add,map_mul,Subgroup.coe_mul]
  rwa [←hm] at hh

private theorem fullModule_mem_plane (u : U c) (hu : (u : G) ∈ W c) : (e u).toAdd 2 = 0 := by
  let P := ((coordinatePlane d.field.Carrier).comap e.toMonoidHom).map (U c).subtype
  have hWP : W c ≤ P := by
    rw [←d.fullModule,commutator_comm]
    apply commutator_le.mpr
    intro k hk z hz
    let k' : K c := ⟨k,c.le_component hk⟩
    let u' : U c := ⟨z,hz⟩
    let w := naturalConjugate d k' u' * u'⁻¹
    have hki : linearThreeActor d.model k' ∈ lineLocalSL d.field.Carrier :=
      hL.le (mem_map_of_mem _ hk)
    have hg := (mem_lineLocalSL_iff _ _).mp hki
    refine ⟨w,?_,?_⟩
    · change (e w).toAdd 2 = 0
      simp only [w,map_mul,map_inv,toAdd_mul,toAdd_inv,he,
        Representation.specialLinearNatural_apply]
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,hg.1,hg.2.1,hg.2.2]
    · change (naturalConjugate d k' u' : G) * (u' : G)⁻¹ = ⁅k,z⁆
      rw [naturalConjugate_coe]
      rfl
  have hp := hWP hu
  have huP : u ∈ (coordinatePlane d.field.Carrier).comap e.toMonoidHom :=
    (mem_map_iff_mem (U c).subtype_injective).mp hp
  exact huP

private theorem root_coordinates_of_sylow
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (u : U c) : (u : G) ∈ root c ↔
      ∃ a : d.field.Carrier, (e u).toAdd = a • (![1,0,0] : Fin 3 → d.field.Carrier) := by
  constructor
  · intro hu
    have h2 := fullModule_mem_plane d e he hL u hu.1
    let g := transvection (by decide : (0 : Fin 3) ≠ 1) (1 : d.field.Carrier)
    have hg : g ∈ unipotentSL d.field.Carrier := by
      change g ∈ pointLocalSL d.field.Carrier ∧ g ∈ lineLocalSL d.field.Carrier
      constructor
      · rw [mem_pointLocalSL_iff]; simp [g,transvection_coe]
      · rw [mem_lineLocalSL_iff]; simp [g,transvection_coe]
    obtain ⟨k,hk,hkg⟩ := hSL.ge hg
    have hku : naturalConjugate d k u = u := by
      apply Subtype.ext
      rw [naturalConjugate_coe,mem_centralizer_iff.mp hu.2 k hk,mul_inv_cancel_right]
    have hfixed := he k u
    rw [hku,hkg] at hfixed
    have h1 : (e u).toAdd 1 = 0 := by
      have ht := Representation.OneCohomology.SLHigherNatural.action_transvection
        (by decide : (0 : Fin 3) ≠ 1) (1 : d.field.Carrier) (e u).toAdd
      rw [ht] at hfixed
      have hh := congrFun hfixed 0
      simpa using hh
    refine ⟨(e u).toAdd 0,?_⟩
    ext i
    fin_cases i <;> simp [h1,h2]
  · rintro ⟨a,ha⟩
    change (u : G) ∈ W c ∧ (u : G) ∈ Subgroup.centralizer (S c ⊓ L : Set G)
    refine ⟨?_,?_⟩
    · have hv : (e u).toAdd 2 = 0 := by rw [ha]; simp
      have hh := plane_mem_fullModule d e he hL (e u).toAdd hv
      simpa only [ofAdd_toAdd,e.symm_apply_apply] using hh
    · intro k hk
      let k' : K c := ⟨k,c.le_component hk.2⟩
      have hki : linearThreeActor d.model k' ∈ unipotentSL d.field.Carrier :=
        hSL.le (mem_map_of_mem _ hk)
      have hf : Representation.specialLinearNatural 3 (linearThreeActor d.model k')
          (![1,0,0] : Fin 3 → d.field.Carrier) = ![1,0,0] := hki.1
      have hku : naturalConjugate d k' u = u := by
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [he,ha,map_smul,hf]
      have hh := congrArg Subtype.val hku
      rw [naturalConjugate_coe] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
end Coordinates

/-- The original natural module, line-local image and its actual Sylow image
construct the root marking; no root or secondary model is a hypothesis. -/
public theorem MSData.rootCoordinates_of_marked_parabolic (d : MSData c n)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    Nonempty (RootCoordinates d) := by
  obtain ⟨e,he⟩ := natural_coordinates d
  refine ⟨⟨e,?_,root_coordinates_of_sylow d e he hL hSL⟩⟩
  intro k u u' hu'
  have hh : u' = naturalConjugate d k u := Subtype.ext (hu'.trans (naturalConjugate_coe d k u).symm)
  rw [hh]
  exact he k u


/-- The literal 4.3.13--15 application from the two original marked local
images, with no root marking, secondary quotient or generation callback. -/
public theorem MSData.secondary_structure_of_marked_parabolic [Finite G]
    (d : MSData c n) (hn : 1 < n)
    {V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ normalizer (secondary c : Set G)) :
    L ⊔ secondary c = K c ∧
    ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n) ∧
    secondary c < B.map (rootNormalizer c).subtype ∧
    letI := hBn
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction B (pCore 2 B)) ≠ ⊥ := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact ⟨m.original_sup_secondary hn D hL.ge,
    m.strict_component_and_action hn D hL.ge B hB hBn hsec hcore hnorm⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
