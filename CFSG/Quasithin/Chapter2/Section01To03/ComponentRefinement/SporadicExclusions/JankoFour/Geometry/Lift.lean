module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Geometry.SourceModel
public import Theory.GroupTheory.PCoreSurjective

/-!
# Lifting the Sylow-adapted Mathieu seed into the component

The model seed is pulled back through the specified quotient by O₂(L) and
embedded into the ambient group. Its normalizers come from the actual action
of N_S(L), which preserves L ∩ S and therefore its model Sylow image.

Fixed points lift through the central two-kernel: displacement on the preimage
of the model fixed subgroup is a homomorphism into O₂(L), and it vanishes on
a Sylow subgroup. Model generation thus lifts with the literal C_G(z).
The preimage surjection and the actual max1 equivalence give both a
self-centralizing two-core and a surjection onto the fixed M₂₄ carrier with
two-group kernel. No assertion about the layer after adjoining all of S is used.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3i.
The fixed-point and normalizer transport arguments are adapted from
`SporadicExclusions.Held.LocalGeometry.Transport`, without importing that branch.
-/

public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- A central two-displacement vanishing on a Sylow subgroup vanishes everywhere in the fixed preimage. -/
private theorem modelFixed_preimage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    (modelAut d d.action).fixedSubgroup.comap (modelMap d) = d.action.fixedSubgroup := by
  let := h.finite
  let V := (modelAut d d.action).fixedSubgroup.comap (modelMap d)
  have hdiff (x : V) : (x : L)⁻¹ * d.action x ∈ pCore 2 L := by
    rw [← modelMap_ker d]
    change modelMap d ((x : L)⁻¹ * d.action x) = 1
    rw [map_mul, map_inv, ← modelAut_apply]
    have hx : modelAut d d.action (modelMap d x) = modelMap d x :=
      (MulAut.mem_fixedSubgroup _ _).mp x.property
    rw [hx, inv_mul_cancel]
  let delta : V →* pCore 2 L := {
    toFun x := ⟨(x : L)⁻¹ * d.action x, hdiff x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ((x : L) * y)⁻¹ * d.action ((x : L) * y) =
        ((x : L)⁻¹ * d.action x) * ((y : L)⁻¹ * d.action y)
      rw [mul_inv_rev, map_mul]
      have hc := mem_center_iff.mp (twoCore_le_center h (hdiff x)) (y : L)⁻¹
      calc
        _ = ((y : L)⁻¹ * ((x : L)⁻¹ * d.action x)) * d.action y := by group
        _ = (((x : L)⁻¹ * d.action x) * (y : L)⁻¹) * d.action y := by rw [hc]
        _ = _ := by group }
  have hRV : (componentSylow h : Subgroup L) ≤ V := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [modelAut_apply, componentSylow_fixed h d x hx]
  let T := (componentSylow h).subtype hRV
  let U := T.mapSurjective delta.rangeRestrict_surjective
  have hU : (U : Subgroup delta.range) = ⊤ := by
    apply (U.is_maximal' (pCore_isPGroup.to_subgroup delta.range |>.to_subgroup ⊤) le_top).symm
  have hUbot : (U : Subgroup delta.range) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro y ⟨x, hx, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change (x : L)⁻¹ * d.action x = 1
    rw [componentSylow_fixed h d x hx, inv_mul_cancel]
  have hd (x : V) : delta x = 1 := by
    have hx : delta.rangeRestrict x ∈ (U : Subgroup delta.range) := hU.symm ▸ mem_top _
    rw [hUbot, mem_bot] at hx
    exact congrArg Subtype.val hx
  apply le_antisymm
  · intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hd' := congrArg Subtype.val (hd ⟨x, hx⟩)
    change x⁻¹ * d.action x = 1 at hd'
    exact (inv_mul_eq_one.mp hd').symm
  · intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [modelAut_apply, (MulAut.mem_fixedSubgroup _ _).mp hx]

/-- Pull a specified model subgroup back through the quotient and embed it in G. -/
private def componentPreimage (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) : Subgroup G :=
  (P.comap (modelMap d)).map L.subtype

private theorem mem_componentPreimage (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) (x : G) :
    x ∈ componentPreimage d P ↔ ∃ hx : x ∈ L, modelMap d ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

private theorem componentPreimage_le (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) : componentPreimage d P ≤ L := map_subtype_le _

private theorem componentPreimage_sup (d : SporadicQuotientInput L z .j4)
    (P Q : Subgroup Janko4.Model) :
    componentPreimage d (P ⊔ Q) = componentPreimage d P ⊔ componentPreimage d Q := by
  unfold componentPreimage
  rw [← comap_sup_eq _ P Q (modelMap_surjective d), Subgroup.map_sup]

private theorem componentPreimage_top (d : SporadicQuotientInput L z .j4) :
    componentPreimage d ⊤ = L := by
  rw [componentPreimage, comap_top, ← MonoidHom.range_eq_map, range_subtype]

/-- The lifted fixed subgroup is exactly the component intersection with the ambient centralizer. -/
private theorem componentPreimage_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    componentPreimage d (modelAut d d.action).fixedSubgroup =
      L ⊓ centralizer ({z} : Set G) := by
  rw [componentPreimage, modelFixed_preimage h d]
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := d.conjugation x
    rw [(MulAut.mem_fixedSubgroup _ _).mp hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply (MulAut.mem_fixedSubgroup d.action ⟨x, hx⟩).mpr
    apply Subtype.ext
    rw [d.conjugation, ← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

/-- Only N_A(L) acts on L; no action of all of A on L is asserted. -/
private def normalizerModelAction (d : SporadicQuotientInput L z .j4) (A : Subgroup G) :
    (A ⊓ normalizer (L : Set G) : Subgroup G) →* MulAut Janko4.Model :=
  (modelAut d).comp (L.normalizerMonoidHom.comp (inclusion inf_le_right))

private theorem normalizerModelAction_apply (d : SporadicQuotientInput L z .j4)
    (A : Subgroup G) (a : (A ⊓ normalizer (L : Set G) : Subgroup G)) (x : L) :
    normalizerModelAction d A a (modelMap d x) =
      modelMap d ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp a.property.2 x).mp x.property⟩ :=
  modelAut_apply d _ x

/-- The actual image of the normalizer action, including any outer automorphisms. -/
private def modelActors (d : SporadicQuotientInput L z .j4) (A : Subgroup G) :
    Subgroup (MulAut Janko4.Model) := (normalizerModelAction d A).range

/-- Elements of N_S(L) preserve the actual component Sylow subgroup and its model image. -/
private theorem modelActors_preserve_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) (a : MulAut Janko4.Model)
    (ha : a ∈ modelActors d ((S : Subgroup H).map H.subtype)) :
    (modelSylow h d : Subgroup Janko4.Model).map a.toMonoidHom = modelSylow h d := by
  obtain ⟨s, rfl⟩ := ha
  have hstable (s : (((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) : Subgroup G))
      (r : Janko4.Model) (hr : r ∈ (modelSylow h d : Subgroup Janko4.Model)) :
      normalizerModelAction d ((S : Subgroup H).map H.subtype) s r ∈
        (modelSylow h d : Subgroup Janko4.Model) := by
    obtain ⟨x, hx, rfl⟩ := hr
    rw [normalizerModelAction_apply]
    apply mem_map_of_mem
    apply (mem_componentSylow h _).mpr
    exact ((S : Subgroup H).map H.subtype).mul_mem
      (((S : Subgroup H).map H.subtype).mul_mem s.property.1
        ((mem_componentSylow h x).mp hx))
      (((S : Subgroup H).map H.subtype).inv_mem s.property.1)
  apply le_antisymm
  · rintro r ⟨x, hx, rfl⟩
    exact hstable s x hx
  · intro r hr
    refine ⟨normalizerModelAction d ((S : Subgroup H).map H.subtype) s⁻¹ r,
      hstable s⁻¹ r hr, ?_⟩
    rw [map_inv]
    exact MulEquiv.apply_symm_apply _ _

/-- Proved model invariance lifts to N_A(L)-normalization of the full preimage. -/
private theorem componentPreimage_normalized (d : SporadicQuotientInput L z .j4)
    (A : Subgroup G) (P : Subgroup Janko4.Model)
    (hP : ∀ a ∈ modelActors d A, P.map a.toMonoidHom = P) :
    A ⊓ normalizer (L : Set G) ≤ normalizer (componentPreimage d P) := by
  have hstable (s : (A ⊓ normalizer (L : Set G) : Subgroup G))
      (x : G) (hx : x ∈ componentPreimage d P) :
      (s : G) * x * (s : G)⁻¹ ∈ componentPreimage d P := by
    obtain ⟨x, hx, rfl⟩ := hx
    apply (mem_componentPreimage d P _).mpr
    refine ⟨(mem_normalizer_iff.mp s.property.2 x).mp x.property, ?_⟩
    have hm : normalizerModelAction d A s (modelMap d x) ∈ P := by
      rw [← hP _ ⟨s, rfl⟩]
      exact mem_map_of_mem _ hx
    exact (normalizerModelAction_apply d A s x) ▸ hm
  intro s hs
  apply mem_normalizer_iff.mpr
  intro x
  refine ⟨hstable ⟨s, hs⟩ x, ?_⟩
  intro hx
  have hi := hstable (⟨s, hs⟩ : (A ⊓ normalizer (L : Set G) : Subgroup G))⁻¹ _ hx
  simpa only [coe_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
    mul_assoc, inv_mul_cancel, mul_one] using hi

/-- The ambient preimage maps onto the specified model seed. -/
private def componentPreimageMap (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) : componentPreimage d P →* P where
  toFun x := ⟨modelMap d ⟨x, componentPreimage_le d P x.property⟩,
    ((mem_componentPreimage d P x).mp x.property).2⟩
  map_one' := by apply Subtype.ext; exact map_one (modelMap d)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (modelMap d) ⟨x, componentPreimage_le d P x.property⟩
      ⟨y, componentPreimage_le d P y.property⟩

private theorem componentPreimageMap_surjective (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) : Function.Surjective (componentPreimageMap d P) := by
  intro y
  obtain ⟨x, hx⟩ := modelMap_surjective d y
  refine ⟨⟨x, (mem_componentPreimage d P x).mpr ⟨x.property, ?_⟩⟩, ?_⟩
  · exact hx.symm ▸ y.property
  · exact Subtype.ext hx

/-- The whole embedded component two-core remains in the preimage kernel. -/
private theorem componentPreimageMap_ker (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) :
    (componentPreimageMap d P).ker = (L.pCoreIn 2).subgroupOf (componentPreimage d P) := by
  ext x
  change (componentPreimageMap d P x : P) = 1 ↔ (x : G) ∈ (pCore 2 L).map L.subtype
  rw [Subtype.ext_iff]
  change modelMap d ⟨x, componentPreimage_le d P x.property⟩ = 1 ↔ _
  rw [← MonoidHom.mem_ker, modelMap_ker d]
  exact (mem_map_iff_mem L.subtype_injective).symm

private theorem componentPreimageMap_ker_isPGroup (d : SporadicQuotientInput L z .j4)
    (P : Subgroup Janko4.Model) : IsPGroup 2 (componentPreimageMap d P).ker := by
  rw [componentPreimageMap_ker]
  exact (isPGroup_pCoreIn 2 L).comap_subtype

/-- The actual component seed for the Mathieu local cover. All assertions concern
B itself; the Mathieu layer of B joined with S is a separate source step. -/
theorem exists_source_component_seed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    ∃ B : Subgroup G,
      B ≤ L ∧
      (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
        normalizer (B : Set G) ∧
      L ≤ centralizer ({z} : Set G) ⊔ B ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      ∃ f : B →* Sporadic.Mathieu.M24, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let := h.finite
  obtain ⟨P, _hP, ⟨e⟩, hinv, hgen⟩ := exists_source_model_seed h d
  let B := componentPreimage d P
  let K := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let q : B →* K := e.toMonoidHom.comp (componentPreimageMap d P)
  have hq : Function.Surjective q := e.surjective.comp (componentPreimageMap_surjective d P)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact componentPreimageMap_ker_isPGroup d P
  have hcore : (pCore 2 K).comap q = pCore 2 B :=
    q.comap_pCore_of_ker_isPGroup hq hk
  have hself : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    rw [← Janko4.LocalStructure.localKernel_eq_twoCore]
    exact (Janko4.LocalStructure.centralizer_localKernel _ _).le
  refine ⟨B, componentPreimage_le d P, ?_, ?_, ?_, ?_⟩
  · exact componentPreimage_normalized d _ P
      (fun a ha => hinv a (modelActors_preserve_sylow h d a ha))
  · have he := congrArg (componentPreimage d) hgen
    rw [componentPreimage_top, componentPreimage_sup, componentPreimage_fixed h d] at he
    exact he.ge.trans (sup_le_sup_right inf_le_right B)
  · intro x hx
    rw [← hcore]
    apply hself
    intro y hy
    obtain ⟨y, rfl⟩ := hq y
    have hy' : y ∈ pCore 2 B := by rwa [← hcore]
    simpa only [map_mul] using congrArg q (hx y hy')
  · let g : K →* Sporadic.Mathieu.M24 :=
      (Janko4.LocalStructure.localQuotientEquivM24 _ _).toMonoidHom.comp
        (QuotientGroup.mk' (Janko4.Cardinality.localKernel
          Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    have hg : Function.Surjective g :=
      (Janko4.LocalStructure.localQuotientEquivM24 _ _).surjective.comp
        (QuotientGroup.mk'_surjective _)
    have hgker : g.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _
        (Janko4.LocalStructure.localQuotientEquivM24 _ _).injective,
        QuotientGroup.ker_mk', Janko4.LocalStructure.localKernel_eq_twoCore]
    refine ⟨g.comp q, hg.comp hq, ?_⟩
    rw [← MonoidHom.comap_ker, hgker]
    exact pCore_isPGroup.comap_of_ker_isPGroup q hk

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
