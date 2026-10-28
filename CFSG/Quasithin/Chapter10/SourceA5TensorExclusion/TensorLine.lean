module
public import Theory.GroupTheory.Commutator.PerfectConjugateCentralizer
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneOrbit
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowFixed
public import Theory.Representation.BinaryConjugationSection.JoinImage
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# The original tensor singular line and its Sylow centralizer

The common Sylow subgroup T ∩ L₀ fixes an F₄-line in the literal full
module. Its coordinate image has four elements, and normalization by T
gives an original T-central involution in that line. The L-generated
orbit is centralized by O₂(L).

An element of T centralizing the orbit cannot interchange L with a
distinct conjugate: their induced actions would coincide and commute,
and perfection would force L to act trivially. The first tensor factor
has no nonzero fixed vector, contradicting the nontrivial original line.

Source: Aschbacher–Smith 9.1.2,9.2.2(3),9.3.6, combined manuscript,
printed pp.729–731 and733. The common fixed subgroup is T ∩ L₀;
fixing only the first-factor Sylow subgroup would instead give an F₄-plane.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

def tensorLine (_m : SourceA5TensorModel D e) : Subgroup G := D.fullModule ⊓ centralizer ((T : Subgroup G) ⊓ localOrbit T L : Set G)
def tensorPlane : Subgroup G := componentOrbit m.tensorLine L

theorem tensorLine_le_fullModule : m.tensorLine ≤ D.fullModule := inf_le_left

theorem tensorLine_normalized : (T : Subgroup G) ≤ normalizer (m.tensorLine : Set G) := by
  have hS : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ localOrbit T L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer (le_normalizer_componentOrbit L T)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
    (hS.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

theorem tensorPlane_le_fullModule : m.tensorPlane ≤ D.fullModule := by
  change (⨆ l : L, m.tensorLine.map (MulAut.conj (l : G)).toMonoidHom) ≤ _
  apply iSup_le
  intro l
  rintro _ ⟨v,hv,rfl⟩
  exact (mem_normalizer_iff.mp
    (D.maximalLocal_normalizes_fullModule
      ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer l.property)) v).mp
        (m.tensorLine_le_fullModule hv)

theorem component_core_centralizes_tensorPlane : L.pCoreIn 2 ≤ centralizer (m.tensorPlane : Set G) :=
  (source_component_core_centralizes_fullModule D).trans (centralizer_le m.tensorPlane_le_fullModule)

private theorem exists_orbit_sylow : ∃ P : Sylow 2 (localOrbit T L),
    (P : Subgroup (localOrbit T L)).map (localOrbit T L).subtype =
      (T : Subgroup G) ⊓ localOrbit T L := by
  let M := normalizer (localOrbit T L : Set G)
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  obtain ⟨P,hP⟩ := (T.subtype hTM).exists_map_subtype_eq_inf_of_normalizes
    (localOrbit T L).le_normalizer (show M ≤ normalizer (localOrbit T L : Set G) from le_rfl)
  refine ⟨P,?_⟩
  rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] at hP

private theorem fixed_iff_line (P : Sylow 2 (localOrbit T L))
    (hP : (P : Subgroup (localOrbit T L)).map (localOrbit T L).subtype =
      (T : Subgroup G) ⊓ localOrbit T L) (v : D.fullModule) :
    (∀ p ∈ P, Binary.action (m.quotient p) (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd) ↔ (v : G) ∈ m.tensorLine := by
  constructor
  · intro hf
    refine ⟨v.property,?_⟩
    intro s hs
    obtain ⟨p,hp,hps⟩ := hP.ge hs
    change (p : G) = s at hps
    subst s
    have he := (m.sectionData.equivariant p v).trans (hf p hp)
    have hc := m.coordinates_injective (Multiplicative.toAdd.injective he)
    have hh := congrArg Subtype.val hc
    change (p : G) * (v : G) * (p : G)⁻¹ = (v : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro hv p hp
    have hcomm := hv.2 p (hP.le (mem_map_of_mem _ hp))
    have he := m.sectionData.equivariant p v
    have hconj : (⟨(p : G)*v*(p : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized p.property) v).mp v.property⟩ : D.fullModule) = v := by
      apply Subtype.ext
      change (p : G)*(v : G)*(p : G)⁻¹ = (v : G)
      rw [hcomm,mul_inv_cancel_right]
    rw [hconj] at he
    exact he.symm

theorem card_tensorLine : Nat.card m.tensorLine = 4 := by
  obtain ⟨P,hP⟩ := exists_orbit_sylow (T := T) (L := L)
  let Q := P.mapSurjective m.onto
  let f : m.tensorLine → fixedSpace Binary.action (Q : Subgroup Binary.G) := fun v =>
    ⟨(m.sectionData.coordinates ⟨v,m.tensorLine_le_fullModule v.property⟩).toAdd, by
      intro a
      obtain ⟨p,hp,hpa⟩ := a.property
      change m.quotient p = a.val at hpa
      change Binary.action a.val (m.sectionData.coordinates ⟨v,m.tensorLine_le_fullModule v.property⟩).toAdd = _
      rw [←hpa]
      exact (m.fixed_iff_line P hP ⟨v,m.tensorLine_le_fullModule v.property⟩).mpr v.property p hp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have hc := m.coordinates_injective
        (Multiplicative.toAdd.injective (congrArg Subtype.val h))
      exact Subtype.ext (congrArg (fun x : D.fullModule => (x : G)) hc)
    · intro w
      obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd w.val)
      have hm : (v : G) ∈ m.tensorLine := (m.fixed_iff_line P hP v).mp (by
        intro p hp
        have hw := w.property ⟨m.quotient p,mem_map_of_mem _ hp⟩
        change Binary.action (m.quotient p) w.val = w.val at hw
        have hv' : (m.sectionData.coordinates v).toAdd = w.val := congrArg Multiplicative.toAdd hv
        rw [hv']
        exact hw)
      exact ⟨⟨v,hm⟩,Subtype.ext (congrArg Multiplicative.toAdd hv)⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  exact Binary.card_fixedSpace_sylow Q

theorem tensorLine_elementary : IsElementaryAbelian 2 m.tensorLine := by
  let := m.fullModule_elementary
  exact IsElementaryAbelian.of_le m.tensorLine_le_fullModule

theorem tensorLine_binary_finrank :
    Module.finrank (ZMod 2) (m.sectionData.imageSpace m.tensorLine) = 2 := by
  apply m.sectionData.imageSpace_finrank_of_index m.tensorLine m.tensorLine_le_fullModule 2
  rw [relIndex_bot_left,m.card_tensorLine]
  rfl

theorem tensorLine_ne_bot : m.tensorLine ≠ ⊥ := by
  intro h
  have hc := m.card_tensorLine
  rw [h,Subgroup.card_bot] at hc
  omega

theorem tensorLine_le_sylow : m.tensorLine ≤ (T : Subgroup G) :=
  m.tensorLine_le_fullModule.trans m.fullModule_le_sylow

theorem exists_central_involution_tensorLine :
    ∃ z : G, orderOf z = 2 ∧ z ∈ m.tensorLine ∧
      ∀ t ∈ (T : Subgroup G), t * z = z * t := by
  let U := m.tensorLine.subgroupOf (T : Subgroup G)
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer m.tensorLine_le_sylow).mpr
    m.tensorLine_normalized
  have hU : U ≠ ⊥ := by
    intro h
    apply m.tensorLine_ne_bot
    have he := congrArg (Subgroup.map (T : Subgroup G).subtype) h
    simpa only [U,map_subgroupOf_eq_of_le m.tensorLine_le_sylow,Subgroup.map_bot] using he
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (center_inf_ne_bot_of_normal T.isPGroup' U hU)
  have hzline : ((z : (T : Subgroup G)) : G) ∈ m.tensorLine := z.property.2
  refine ⟨z.val.val,?_,hzline,?_⟩
  · apply orderOf_eq_prime_iff.mpr
    constructor
    · have hs := m.sectionData.square_eq_one_of_trivial_kernel rfl
        ⟨z.val.val,m.tensorLine_le_fullModule hzline⟩
      exact congrArg Subtype.val hs
    · intro he
      apply hz
      apply Subtype.ext
      exact Subtype.ext he
  · intro t ht
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.property.1) ⟨t,ht⟩)


include m in
/-- The original component has no fixed point on the full tensor module. -/
theorem fullModule_component_fixed_eq_bot :
    D.fullModule ⊓ centralizer (L : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  apply (m.sectionData.coordinates_eq_one_iff ⟨a,ha.1⟩).mp
  apply Multiplicative.toAdd.injective
  apply Binary.first_factor_common_fixed_eq_zero
  intro g
  obtain ⟨l,hl⟩ := (m.firstMarking.surjective.comp e.surjective).comp
    (QuotientGroup.mk'_surjective (pCore 2 L)) g
  change m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)) = g at hl
  let l0 : localOrbit T L := ⟨l,le_componentOrbit L T l.property⟩
  have hq : m.quotient l0 = (g,1) := (m.first_factor l).trans (by rw [hl])
  have he := m.sectionData.equivariant l0 ⟨a,ha.1⟩
  have hs : (⟨(l0 : G)*a*(l0 : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized l0.property) a).mp ha.1⟩ : D.fullModule) = ⟨a,ha.1⟩ := by
    apply Subtype.ext
    change (l : G)*a*(l : G)⁻¹ = a
    rw [ha.2 l l.property,mul_inv_cancel_right]
  rw [hs] at he
  change (m.sectionData.coordinates ⟨a,ha.1⟩).toAdd =
    Binary.action (m.quotient l0) (m.sectionData.coordinates ⟨a,ha.1⟩).toAdd at he
  simpa only [hq] using he.symm

include D in
private theorem conjugate_commutator_le_component_core
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅L,L.map (MulAut.conj t).toMonoidHom⁆ ≤ L.pCoreIn 2 := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    dsimp only [B]
    rw [map_map,show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hB : B.IsCComponent := D.maximal.1.1.map_equiv (MulAut.conj tH)
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE D.maximal.1.2.2
  have hc := ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hQ D.maximal.1.1 hB hne
  have hm := map_mono (f := H.subtype) (hc.1.trans inf_le_left)
  rw [map_commutator,hmapA,hmapB,map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    hmapA] at hm
  exact hm

/-- Centralizing the original singular-plane orbit forces stabilization of L. -/
theorem sylow_centralizer_tensorPlane_le_stabilizer :
    (T : Subgroup G) ⊓ centralizer (m.tensorPlane : Set G) ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  rintro t ⟨ht,hct⟩
  refine ⟨ht,?_⟩
  by_contra htn
  have hLM : L ≤ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  let := D.component_in_maximalLocal.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLM).toMonoidHom)
    (subgroupOfEquivOfLe hLM).surjective
  have hc : L ≤ centralizer (m.tensorPlane : Set G) :=
    perfect_centralizes_of_centralizing_conjugator L m.tensorPlane
      (le_normalizer_componentOrbit m.tensorLine L) t hct
      ((conjugate_commutator_le_component_core (D := D) ht htn).trans
        m.component_core_centralizes_tensorPlane)
  apply m.tensorLine_ne_bot
  apply le_bot_iff.mp
  calc
    m.tensorLine ≤ D.fullModule ⊓ centralizer (L : Set G) :=
      le_inf m.tensorLine_le_fullModule
        ((le_componentOrbit m.tensorLine L).trans (le_centralizer_iff.mp hc))
    _ = ⊥ := m.fullModule_component_fixed_eq_bot

theorem exists_tensorLine_coordinates_sylow :
    ∃ Q : Sylow 2 Binary.G,
      m.sectionData.imageSpace m.tensorLine = fixedSpace Binary.action (Q : Subgroup Binary.G) := by
  obtain ⟨P,hP⟩ := exists_orbit_sylow (T := T) (L := L)
  let Q := P.mapSurjective m.onto
  refine ⟨Q,?_⟩
  ext w
  rw [m.sectionData.mem_imageSpace_iff]
  constructor
  · rintro ⟨v,hv,rfl⟩ a
    obtain ⟨p,hp,hpa⟩ := a.property
    change m.quotient p = a.val at hpa
    change Binary.action a.val (m.sectionData.coordinates v).toAdd = _
    rw [←hpa]
    exact (m.fixed_iff_line P hP v).mpr hv p hp
  · intro hw
    obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
    have hv' : (m.sectionData.coordinates v).toAdd = w := congrArg Multiplicative.toAdd hv
    refine ⟨v,(m.fixed_iff_line P hP v).mp ?_,hv'⟩
    intro p hp
    have hh := hw ⟨m.quotient p,mem_map_of_mem _ hp⟩
    change Binary.action (m.quotient p) w = w at hh
    rw [hv']
    exact hh

theorem tensorPlane_coordinates_firstOrbit :
    m.sectionData.imageSpace m.tensorPlane =
      Binary.firstOrbit (m.sectionData.imageSpace m.tensorLine) := by
  have hLN : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hmap (l : L) : m.tensorLine.map (MulAut.conj (l : G)).toMonoidHom ≤ D.fullModule := by
    rintro _ ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (hLN l.property) v).mp (m.tensorLine_le_fullModule hv)
  change m.sectionData.imageSpace (⨆ l : L,m.tensorLine.map (MulAut.conj (l : G)).toMonoidHom) = _
  rw [m.sectionData.imageSpace_iSup _ hmap]
  have himage (l : L) :
      m.sectionData.imageSpace (m.tensorLine.map (MulAut.conj (l : G)).toMonoidHom) =
        (m.sectionData.imageSpace m.tensorLine).map
          (Binary.action (m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)),1)) := by
    have hh := m.sectionData.imageSpace_conjBy m.tensorLine m.tensorLine_le_fullModule
      (⟨l,le_componentOrbit L T l.property⟩ : localOrbit T L)
    change m.sectionData.imageSpace (m.tensorLine.map (MulAut.conj (l : G)).toMonoidHom) =
      (m.sectionData.imageSpace m.tensorLine).map (Binary.action (m.quotient ⟨l,le_componentOrbit L T l.property⟩)) at hh
    rwa [m.first_factor] at hh
  simp_rw [himage]
  apply le_antisymm
  · apply iSup_le
    intro l
    exact le_iSup (fun g : Matrix.SpecialLinearGroup (Fin 2) Binary.F =>
      (m.sectionData.imageSpace m.tensorLine).map (Binary.action (g,1))) _
  · apply iSup_le
    intro g
    obtain ⟨l,hl⟩ := (m.firstMarking.surjective.comp e.surjective).comp
      (QuotientGroup.mk'_surjective (pCore 2 L)) g
    change m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)) = g at hl
    rw [←hl]
    exact le_iSup (fun k : L => (m.sectionData.imageSpace m.tensorLine).map
      (Binary.action (m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) k)),1))) l

theorem card_tensorPlane : Nat.card m.tensorPlane = 16 := by
  have hc := m.sectionData.imageSpace_card_eq_relIndex m.tensorPlane m.tensorPlane_le_fullModule
  rw [relIndex_bot_left] at hc
  rw [←hc,m.tensorPlane_coordinates_firstOrbit]
  obtain ⟨Q,hQ⟩ := m.exists_tensorLine_coordinates_sylow
  rw [hQ]
  exact Binary.card_firstOrbit_fixedSpace_sylow Q

theorem tensorPlane_binary_finrank :
    Module.finrank (ZMod 2) (m.sectionData.imageSpace m.tensorPlane) = 4 := by
  apply m.sectionData.imageSpace_finrank_of_index m.tensorPlane m.tensorPlane_le_fullModule 4
  rw [relIndex_bot_left,m.card_tensorPlane]
  rfl


/-- Every vector of the original fixed line is singular in determinant coordinates. -/
theorem tensorLine_singular (v : m.tensorLine) :
    ((m.sectionData.coordinates ⟨v,m.tensorLine_le_fullModule v.property⟩).toAdd).det = 0 := by
  obtain ⟨Q,hQ⟩ := m.exists_tensorLine_coordinates_sylow
  apply Binary.sylow_fixed_singular Q
  have hv := (m.sectionData.mem_imageSpace_iff m.tensorLine _).mpr
    ⟨⟨v,m.tensorLine_le_fullModule v.property⟩,v.property,rfl⟩
  rw [hQ] at hv
  intro g hg
  exact hv ⟨g,hg⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
