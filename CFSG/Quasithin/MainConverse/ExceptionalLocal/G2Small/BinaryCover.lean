module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.BinaryCover.Geometry
public import Theory.AtlasPort.LinearGroups.G2.BinarySmallLocals
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint

/-!
# Coverage by the two restricted binary parabolics

Every nonidentity two-subgroup of the full octonion model fixes an edge of
its hexagon. The proved hexagon geometry and invariant-tree argument give
a vertex fixed by its normalizer, hence containment in a conjugate parabolic.
For a two-subgroup of the actual commutator group, map its normalizer into
the full model. The quotient has two elements, and the short-root involution
lies in both parabolics and represents the nontrivial quotient element.
Multiplication by that involution therefore makes the conjugator internal
to the commutator group without losing the containment.

The two restricted parabolics are nontrivial and have characteristic two.
Their nontrivial two-cores supply two-local overgroups, so maximality turns
each containment into equality. The final theorem has exactly the
Sylow-containing interface required by the parent even-characteristic proof.
The argument also proves coverage for all maximal two-locals.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed pp.3–4, repeated on
pp.481–482; the concrete binary pair is discussed in Lemma 14.2.21,
printed p.988. All models, parabolics, and conjugations here are the actual
ones from the licensed ATLAS octonion port.
-/

public section

namespace Atlas.G2.BinaryParabolicPair
open Subgroup BinaryCore EvenLocal.NormalizerCover

private theorem derived_of_projection_eq_one (g : Model (ZMod 2))
    (hg : BinaryException.projection g = 1) : g ∈ DerivedModel := by
  change g ∈ commutator (Model (ZMod 2))
  rw [commutator_eq_longRootClosure]
  exact (QuotientGroup.eq_one_iff _).mp hg

/-- Multiplying by the short-root involution removes the nontrivial quotient bit. -/
private theorem adjust_conjugator (P : Subgroup (Model (ZMod 2)))
    (hs : shortRoot ∈ P) (Q : Subgroup DerivedModel) (g : Model (ZMod 2))
    (hg : ∀ x ∈ Q, g * x.val * g⁻¹ ∈ P) :
    ∃ h : DerivedModel, Q.map (MulAut.conj h).toMonoidHom ≤ P.subgroupOf DerivedModel := by
  let := singularPoints_primitive (K := ZMod 2)
  rcases BinaryException.quotient_eq_one_or_bit g with hbit | hbit
  · let h : DerivedModel := ⟨g, derived_of_projection_eq_one g hbit⟩
    refine ⟨h, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact hg x hx
  · have hh : shortRoot * g ∈ DerivedModel := by
      apply derived_of_projection_eq_one
      rw [map_mul,hbit]
      change BinaryException.quotientBit * BinaryException.quotientBit = 1
      exact (pow_two _).symm.trans BinaryException.quotientBit_sq
    let h : DerivedModel := ⟨shortRoot*g,hh⟩
    refine ⟨h, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    change (shortRoot*g) * x.val * (shortRoot*g)⁻¹ ∈ P
    have he : (shortRoot*g) * x.val * (shortRoot*g)⁻¹ =
        shortRoot * (g*x.val*g⁻¹) * shortRoot⁻¹ := by group
    rw [he]
    exact P.mul_mem (P.mul_mem hs (hg x hx)) (P.inv_mem hs)

private theorem ambient_normalizer_conjugate_le (Q : Subgroup (Model (ZMod 2)))
    (hQ : Q ≠ ⊥) (hpQ : IsPGroup 2 Q) :
    ∃ g : Model (ZMod 2),
      (normalizer (Q : Set (Model (ZMod 2)))).map (MulAut.conj g).toMonoidHom ≤ firstParabolic ∨
      (normalizer (Q : Set (Model (ZMod 2)))).map (MulAut.conj g).toMonoidHom ≤ secondParabolic := by
  obtain ⟨v,hv⟩ := normalizer_fixed_vertex_of_fixed_edge BinaryCoverGeometry.hexagonData
    Q hQ hpQ (exists_fixed_edge Q hpQ)
  obtain ⟨g,hg | hg⟩ := normalizer_conjugate_le_of_fixed_vertex Q v hv
  · exact ⟨g,Or.inl (LieParabolicSetup.parabolic₁_binary ▸ hg)⟩
  · exact ⟨g,Or.inr hg⟩

private theorem restrict_normalizer_conjugate (P : Subgroup (Model (ZMod 2)))
    (hs : shortRoot ∈ P) (R : Subgroup DerivedModel) (g : Model (ZMod 2))
    (hg : (normalizer (R.map DerivedModel.subtype : Set (Model (ZMod 2)))).map
      (MulAut.conj g).toMonoidHom ≤ P) :
    ∃ h : DerivedModel, (normalizer (R : Set DerivedModel)).map
      (MulAut.conj h).toMonoidHom ≤ P.subgroupOf DerivedModel := by
  apply adjust_conjugator P hs (normalizer (R : Set DerivedModel)) g
  intro x hx
  have hn : x.val ∈ normalizer (R.map DerivedModel.subtype : Set (Model (ZMod 2))) :=
    R.le_normalizer_map DerivedModel.subtype (mem_map.mpr ⟨x,hx,rfl⟩)
  exact hg (mem_map.mpr ⟨x.val,hn,rfl⟩)

/-- A derived-group two-subgroup normalizer is conjugate into one of the actual restrictions. -/
theorem binary_normalizer_conjugate_le (R : Subgroup DerivedModel)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ g : DerivedModel,
      (normalizer (R : Set DerivedModel)).map (MulAut.conj g).toMonoidHom ≤ derivedFirst ∨
      (normalizer (R : Set DerivedModel)).map (MulAut.conj g).toMonoidHom ≤ derivedSecond := by
  have hQ : R.map DerivedModel.subtype ≠ ⊥ := fun h => hR
    ((R.map_eq_bot_iff_of_injective DerivedModel.subtype_injective).mp h)
  obtain ⟨g,hg | hg⟩ := ambient_normalizer_conjugate_le _ hQ (hp.map _)
  · obtain ⟨h,hh⟩ := restrict_normalizer_conjugate firstParabolic
      (unipotent_le_firstParabolic shortRoot_mem_unipotent) R g hg
    exact ⟨h,Or.inl hh⟩
  · obtain ⟨h,hh⟩ := restrict_normalizer_conjugate secondParabolic
      (unipotent_le_parabolic shortRoot_mem_unipotent) R g hg
    exact ⟨h,Or.inr hh⟩

private theorem core_ne_bot_of_characteristicTwo {G : Type*} [Group G]
    (P : Subgroup G) (hP : P ≠ ⊥)
    (hc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) : pCore 2 P ≠ ⊥ := by
  intro he
  apply hP
  apply le_bot_iff.mp
  intro x hx
  have hm : (⟨x,hx⟩ : P) ∈ centralizer (pCore 2 P : Set P) := by
    rw [he]
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy : y = 1 := hy
    simp [hy]
  have hh : (⟨x,hx⟩ : P) = 1 := by simpa only [he,mem_bot] using hc hm
  exact congrArg Subtype.val hh

private theorem maximal_eq_of_le_characteristicTwo {G : Type*} [Group G]
    (M P : Subgroup G) (hM : IsMaximalTwoLocal M) (hMP : M ≤ P) (hP : P ≠ ⊥)
    (hc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) : M = P := by
  have hn : P ≤ normalizer (P.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 P).le_normalizer_map P.subtype
  have hQ : P.pCoreIn 2 ≠ ⊥ := fun h => core_ne_bot_of_characteristicTwo P hP hc
    (((pCore 2 P).map_eq_bot_iff_of_injective P.subtype_injective).mp h)
  exact le_antisymm hMP (hn.trans (hM.2 ⟨P.pCoreIn 2,hQ,isPGroup_pCoreIn 2 P,rfl⟩
    (hMP.trans hn)))

private theorem derivedFirst_ne_bot : derivedFirst ≠ ⊥ := by
  intro he
  have hz : (⟨z,rootA_one_mem_commutator⟩ : DerivedModel) ∈ derivedFirst :=
    core_le_firstParabolic (elementary_le_core z_mem_elementary)
  rw [he,mem_bot] at hz
  exact z_ne_one (congrArg Subtype.val hz)

private theorem derivedSecond_ne_bot : derivedSecond ≠ ⊥ := by
  intro he
  have hz : (⟨z,rootA_one_mem_commutator⟩ : DerivedModel) ∈ derivedSecond :=
    elementary_le_secondParabolic z_mem_elementary
  rw [he,mem_bot] at hz
  exact z_ne_one (congrArg Subtype.val hz)

private theorem eq_map_conj_inv_of_map_conj_eq {G : Type*} [Group G]
    (M P : Subgroup G) (g : G) (he : M.map (MulAut.conj g).toMonoidHom = P) :
    M = P.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) he
  rwa [Subgroup.map_map,hcomp,Subgroup.map_id] at hh

/-- Every maximal two-local of the actual binary derived group is one of the restricted parabolics up to internal conjugacy. -/
theorem binary_maximalTwoLocal_conjugate (M : Subgroup DerivedModel)
    (hM : IsMaximalTwoLocal M) :
    ∃ g : DerivedModel, M = derivedFirst.map (MulAut.conj g).toMonoidHom ∨
      M = derivedSecond.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨R,hR,hp,hRM⟩ := hM.1
  obtain ⟨g,hg | hg⟩ := binary_normalizer_conjugate_le R hR hp
  · have he : M.map (MulAut.conj g).toMonoidHom = derivedFirst := by
      apply maximal_eq_of_le_characteristicTwo _ _
        (Theory.Quasithin.isMaximalTwoLocal_map (MulAut.conj g) hM)
        (by simpa only [hRM] using hg) derivedFirst_ne_bot derivedFirst_centralizer_pCore
    refine ⟨g⁻¹,Or.inl ?_⟩
    exact eq_map_conj_inv_of_map_conj_eq _ _ g he
  · have he : M.map (MulAut.conj g).toMonoidHom = derivedSecond := by
      apply maximal_eq_of_le_characteristicTwo _ _
        (Theory.Quasithin.isMaximalTwoLocal_map (MulAut.conj g) hM)
        (by simpa only [hRM] using hg) derivedSecond_ne_bot derivedSecond_centralizer_pCore
    refine ⟨g⁻¹,Or.inr ?_⟩
    exact eq_map_conj_inv_of_map_conj_eq _ _ g he

/-- Coverage in exactly the form required by the binary even-characteristic assembly. -/
theorem binary_sylow_maximalTwoLocal_conjugate
    (T : Sylow 2 DerivedModel) (M : Subgroup DerivedModel)
    (hM : IsMaximalTwoLocal M) (_hTM : (T : Subgroup DerivedModel) ≤ M) :
    ∃ g : DerivedModel, M = derivedFirst.map (MulAut.conj g).toMonoidHom ∨
      M = derivedSecond.map (MulAut.conj g).toMonoidHom :=
  binary_maximalTwoLocal_conjugate M hM

end Atlas.G2.BinaryParabolicPair
