module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.Seed
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.Quasithin.EvenCharacteristic

/-!
# Central-cover transport for the HS normalizer seed

The source is Aschbacher–Smith 2.3.9(7), printed p.526. The quotient map
retains the full central two-kernel. Perfectness makes the descended
involution action faithful. Its fixed two-residual lifts to the actual
centralizer, and the supplied Sylow subgroup supplies the remaining
fixed-subgroup supplement needed for generation.

Only the stabilizer of the component in the ambient Sylow subgroup acts
on this component. The invariant intrinsic seed therefore gives a full
component-orbit overgroup of characteristic two, without assuming that
the ambient Sylow subgroup normalizes the component.

The action and preimage constructions follow the same elementary transport
as the Held branch, but use the specified HS quotient and its single seed.
The normal direct-power section is constructed in the importing Transport
module using the general central-product orbit calculation.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.HS
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Quasisimplicity makes the entire retained two-kernel central. -/
theorem twoCore_le_center (h : LocalSetup H L M S z) :
    pCore 2 L ≤ center L := by
  let := h.finite
  let : IsQuasisimple L := h.quasisimple
  exact IsQuasisimple.pCore_le_center 2

/-- The genuine automorphism action on the characteristic two-core quotient. -/
def modelAut (d : SporadicQuotientInput L z .hs) : MulAut L →* MulAut Carrier :=
  (MulAut.congr d.quotientIso).toMonoidHom.comp (quotientAut (pCore 2 L))

theorem modelAut_apply (d : SporadicQuotientInput L z .hs) (a : MulAut L) (x : L) :
    modelAut d a (quotientMap d x) = quotientMap d (a x) := by
  change d.quotientIso (quotientAut (pCore 2 L) a
    (d.quotientIso.symm (d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [d.quotientIso.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- Perfectness detects an automorphism from its action modulo the central two-kernel. -/
theorem modelAut_injective (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) : Function.Injective (modelAut d) := by
  let : IsQuasisimple L := h.quasisimple
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  apply MulAut.eq_one_of_central_displacement a
  intro x
  apply twoCore_le_center h
  rw [← quotientMap_ker d]
  change quotientMap d (x⁻¹ * a x) = 1
  rw [map_mul, map_inv, ← modelAut_apply]
  change modelAut d a = 1 at ha
  rw [ha, MulAut.one_apply, inv_mul_cancel]

theorem modelAut_conj (d : SporadicQuotientInput L z .hs) (x : L) :
    modelAut d (MulAut.conj x) = MulAut.conj (quotientMap d x) := by
  ext y
  obtain ⟨y, rfl⟩ := quotientMap_surjective d y
  rw [modelAut_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem modelAction_order (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) : orderOf (modelAut d d.action) = 2 := by
  rw [orderOf_injective (modelAut d) (modelAut_injective h d)]
  exact h.action_order d.action d.conjugation

theorem modelAction_inner (d : SporadicQuotientInput L z .hs) :
    modelAut d d.action ∈ (MulAut.conj (G := Carrier)).range := by
  obtain ⟨x, hx⟩ := d.inner
  exact ⟨quotientMap d x, by rw [← hx, modelAut_conj]⟩

/-- The restricted Sylow subgroup; its underlying subgroup is uniquely determined by `componentSylow_map`. -/
def componentSylow (h : LocalSetup H L M S z) : Sylow 2 L :=
  h.exists_component_sylow.choose

theorem componentSylow_map (h : LocalSetup H L M S z) :
    (componentSylow h : Subgroup L).map L.subtype =
      L ⊓ (S : Subgroup H).map H.subtype := h.exists_component_sylow.choose_spec

/-- Membership is the actual intersection with the supplied S, independent of the existential presentation. -/
theorem mem_componentSylow (h : LocalSetup H L M S z) (x : L) :
    x ∈ (componentSylow h : Subgroup L) ↔
      (x : G) ∈ (S : Subgroup H).map H.subtype := by
  rw [← mem_map_iff_mem L.subtype_injective, componentSylow_map h]
  exact and_iff_right x.property

theorem componentSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (x : L)
    (hx : x ∈ (componentSylow h : Subgroup L)) : d.action x = x := by
  obtain ⟨R, hR, hfix⟩ := h.exists_fixed_component_sylow d.action d.conjugation
  have he : (componentSylow h : Subgroup L) = R :=
    (Subgroup.map_injective L.subtype_injective) ((componentSylow_map h).trans hR.symm)
  exact hfix x (he ▸ hx)

/-- The image of the actual component Sylow subgroup under the specified quotient. -/
def modelSylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) : Sylow 2 Carrier := by
  let := h.finite
  exact (componentSylow h).mapSurjective (quotientMap_surjective d)

theorem modelSylow_coe (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) :
    (modelSylow h d : Subgroup Carrier) = (componentSylow h).map (quotientMap d) := rfl

theorem modelSylow_preimage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) :
    (modelSylow h d : Subgroup Carrier).comap (quotientMap d) = componentSylow h := by
  rw [modelSylow_coe, comap_map_eq_self]
  rw [quotientMap_ker]
  exact pCore_isPGroup.le_sylow_of_normal _

theorem modelSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (x : Carrier)
    (hx : x ∈ (modelSylow h d : Subgroup Carrier)) : modelAut d d.action x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [modelAut_apply, componentSylow_fixed h d y hy]


/-- Pull a specified model subgroup back through the quotient and embed it in G. -/
def componentPreimage (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : Subgroup G :=
  (P.comap (quotientMap d)).map L.subtype

theorem mem_componentPreimage (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) (x : G) :
    x ∈ componentPreimage d P ↔ ∃ hx : x ∈ L, quotientMap d ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

theorem componentPreimage_le (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : componentPreimage d P ≤ L := map_subtype_le _

theorem componentPreimage_subgroupOf (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) :
    (componentPreimage d P).subgroupOf L = P.comap (quotientMap d) :=
  comap_map_eq_self_of_injective L.subtype_injective _

theorem twoCore_le_componentPreimage (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : L.pCoreIn 2 ≤ componentPreimage d P := by
  apply map_mono
  rw [← quotientMap_ker d]
  exact MonoidHom.ker_le_comap _ _

theorem componentPreimage_sup (d : SporadicQuotientInput L z .hs)
    (P Q : Subgroup Carrier) :
    componentPreimage d (P ⊔ Q) = componentPreimage d P ⊔ componentPreimage d Q := by
  unfold componentPreimage
  rw [← comap_sup_eq _ P Q (quotientMap_surjective d), Subgroup.map_sup]

theorem componentPreimage_top (d : SporadicQuotientInput L z .hs) :
    componentPreimage d ⊤ = L := by
  rw [componentPreimage, comap_top, ← MonoidHom.range_eq_map, range_subtype]

/-- Normalizer transport is relative to L, rather than an assertion of ambient normality. -/
theorem componentPreimage_normalizer (d : SporadicQuotientInput L z .hs)
    (U : Subgroup Carrier) :
    componentPreimage d (normalizer U) = L ⊓ normalizer (componentPreimage d U) := by
  change ((normalizer U).comap (quotientMap d)).map L.subtype = _
  rw [comap_normalizer_eq_of_surjective U (quotientMap_surjective d),
    ← componentPreimage_subgroupOf d U,
    ← subgroupOf_normalizer_eq (componentPreimage_le d U), subgroupOf_map_subtype,
    inf_comm]

/-- The actual surjection from the intrinsic preimage onto its specified model subgroup. -/
def preimageMap (d : SporadicQuotientInput L z .hs) (P : Subgroup Carrier) :
    P.comap (quotientMap d) →* P where
  toFun x := ⟨quotientMap d x, x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

theorem preimageMap_surjective (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : Function.Surjective (preimageMap d P) := by
  intro y
  obtain ⟨x, hx⟩ := quotientMap_surjective d y
  exact ⟨⟨x, show quotientMap d x ∈ P from hx.symm ▸ y.property⟩, Subtype.ext hx⟩

theorem preimageMap_ker (d : SporadicQuotientInput L z .hs) (P : Subgroup Carrier) :
    (preimageMap d P).ker = (pCore 2 L).subgroupOf (P.comap (quotientMap d)) := by
  ext x
  change (⟨quotientMap d x, _⟩ : P) = 1 ↔ (x : L) ∈ pCore 2 L
  rw [Subtype.ext_iff, ← quotientMap_ker d]
  rfl

theorem preimageMap_ker_isPGroup (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : IsPGroup 2 (preimageMap d P).ker := by
  rw [preimageMap_ker]
  exact pCore_isPGroup.comap_subtype

theorem preimageMap_ker_le_center (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (P : Subgroup Carrier) :
    (preimageMap d P).ker ≤ center (P.comap (quotientMap d)) := by
  rw [preimageMap_ker]
  intro x hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp (twoCore_le_center h hx) y

/-- The intrinsic local two-core is exactly the preimage of the model local two-core. -/
theorem preimageMap_pCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (P : Subgroup Carrier) :
    (pCore 2 P).comap (preimageMap d P) = pCore 2 (P.comap (quotientMap d)) := by
  let := h.finite
  exact (preimageMap d P).comap_pCore_of_ker_isPGroup
    (preimageMap_surjective d P) (preimageMap_ker_isPGroup d P)

/-- A self-centralizing model two-core lifts through the retained two-group kernel. -/
theorem preimage_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (P : Subgroup Carrier)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 (P.comap (quotientMap d)) : Set (P.comap (quotientMap d))) ≤
      pCore 2 (P.comap (quotientMap d)) := by
  intro x hx
  rw [← preimageMap_pCore h d P]
  apply hP
  intro y hy
  obtain ⟨y, rfl⟩ := preimageMap_surjective d P y
  have hy' : y ∈ pCore 2 (P.comap (quotientMap d)) := by
    rwa [← preimageMap_pCore h d P]
  simpa only [map_mul] using congrArg (preimageMap d P) (hx y hy')


/-- Only N_A(L) acts on L; no action of all of A on L is asserted. -/
def normalizerModelAction (d : SporadicQuotientInput L z .hs) (A : Subgroup G) :
    (A ⊓ normalizer (L : Set G) : Subgroup G) →* MulAut Carrier :=
  (modelAut d).comp (L.normalizerMonoidHom.comp (inclusion inf_le_right))

theorem normalizerModelAction_apply (d : SporadicQuotientInput L z .hs)
    (A : Subgroup G) (a : (A ⊓ normalizer (L : Set G) : Subgroup G)) (x : L) :
    normalizerModelAction d A a (quotientMap d x) =
      quotientMap d ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp a.property.2 x).mp x.property⟩ :=
  modelAut_apply d _ x

/-- The image of the component stabilizer's actual quotient action. -/
def modelActors (d : SporadicQuotientInput L z .hs) (A : Subgroup G) :
    Subgroup (MulAut Carrier) := (normalizerModelAction d A).range

/-- Elements of N_S(L) preserve the actual component Sylow subgroup and its model image. -/
theorem modelActors_preserve_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (a : MulAut Carrier)
    (ha : a ∈ modelActors d ((S : Subgroup H).map H.subtype)) :
    (modelSylow h d : Subgroup Carrier).map a.toMonoidHom = modelSylow h d := by
  obtain ⟨s, rfl⟩ := ha
  have hstable (s : (((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) : Subgroup G))
      (r : Carrier) (hr : r ∈ (modelSylow h d : Subgroup Carrier)) :
      normalizerModelAction d ((S : Subgroup H).map H.subtype) s r ∈
        (modelSylow h d : Subgroup Carrier) := by
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
theorem componentPreimage_normalized (d : SporadicQuotientInput L z .hs)
    (A : Subgroup G) (P : Subgroup Carrier)
    (hP : ∀ a ∈ modelActors d A, P.map a.toMonoidHom = P) :
    A ⊓ normalizer (L : Set G) ≤ normalizer (componentPreimage d P) := by
  have hstable (s : (A ⊓ normalizer (L : Set G) : Subgroup G))
      (x : G) (hx : x ∈ componentPreimage d P) :
      (s : G) * x * (s : G)⁻¹ ∈ componentPreimage d P := by
    obtain ⟨x, hx, rfl⟩ := hx
    apply (mem_componentPreimage d P _).mpr
    refine ⟨(mem_normalizer_iff.mp s.property.2 x).mp x.property, ?_⟩
    have hm : normalizerModelAction d A s (quotientMap d x) ∈ P := by
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



/-- The concrete model's centerlessness identifies, but does not discard,
the full center of the covering component. -/
theorem center_eq_twoCore (g : IntrinsicGeometry) (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) : center L = pCore 2 L := by
  apply le_antisymm ?_ (twoCore_le_center h)
  intro x hx
  rw [← quotientMap_ker d]
  apply MonoidHom.mem_ker.mpr
  have hc : quotientMap d x ∈ center Carrier := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := quotientMap_surjective d y
    simpa only [map_mul] using congrArg (quotientMap d) (mem_center_iff.mp hx y)
  simpa only [g.center_eq_bot, mem_bot] using hc

/-- All action hypotheses of the intrinsic seed are derived from the source setup. -/
def transportedSeed (g : IntrinsicGeometry) (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) :
    IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action) :=
  Classical.choice (g.seed (modelSylow h d) (modelAut d d.action)
    (modelAction_order h d) (modelAction_inner d) (modelSylow_fixed h d))

/-- The actual fixed subgroup in L embeds in the ambient involution centralizer. -/
theorem fixedSubgroup_eq_centralizer (d : SporadicQuotientInput L z .hs) :
    d.action.fixedSubgroup = (centralizer ({z} : Set G)).subgroupOf L := by
  ext x
  rw [MulAut.mem_fixedSubgroup]
  change d.action x = x ↔ (x : G) ∈ centralizer ({z} : Set G)
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have he := d.conjugation x
    rw [hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hx
    apply Subtype.ext
    rw [d.conjugation, ← hx, mul_inv_cancel_right]

/-- The fixed-subgroup two-residual has genuine centralizing lifts. -/
theorem fixedResidual_le_centralizerImage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) :
    (pResidual 2 (modelAut d d.action).fixedSubgroup).map
      (modelAut d d.action).fixedSubgroup.subtype ≤ centralizerImage d := by
  let := h.finite
  have hc : (quotientMap d).ker ≤ center L := by
    rw [quotientMap_ker]
    exact twoCore_le_center h
  have hp : IsPGroup 2 (quotientMap d).ker := by
    rw [quotientMap_ker]
    exact pCore_isPGroup
  rw [← MulAut.map_embedded_fixedResidual_of_central_pgroup_ker 2
    d.action (modelAut d d.action) (quotientMap d) (quotientMap_surjective d)
    hc hp (fun x => (modelAut_apply d d.action x).symm)]
  apply map_mono
  exact (map_subtype_le _).trans (fixedSubgroup_eq_centralizer d).le

/-- The fixed residual and the seed's Sylow subgroup supply every fixed point
needed for generation. No equality of quotient centralizers is assumed. -/
theorem seed_centralizerImage_sup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action)) :
    centralizerImage d ⊔ s.localSubgroup = ⊤ := by
  let C := (modelAut d d.action).fixedSubgroup
  have hRC : (modelSylow h d : Subgroup Carrier) ≤ C := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (modelSylow_fixed h d x hx)
  let T : Sylow 2 C := (modelSylow h d).subtype hRC
  have ht := congrArg (Subgroup.map C.subtype) (pResidual_sup_sylow_eq_top T)
  have hT : (T : Subgroup C).map C.subtype = modelSylow h d :=
    map_subgroupOf_eq_of_le hRC
  rw [Subgroup.map_sup, hT, ← MonoidHom.range_eq_map, range_subtype] at ht
  have hC : C ≤ centralizerImage d ⊔ s.localSubgroup := by
    rw [← ht]
    exact sup_le_sup (fixedResidual_le_centralizerImage h d) s.sylow_le
  exact top_unique (s.generated.symm.le.trans (sup_le hC le_sup_right))

/-- Every normalizer actor preserves the lifted seed, including the entire kernel. -/
theorem seed_normalized (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action)) :
    ((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) ≤
      normalizer (componentPreimage d s.localSubgroup : Set G) := by
  apply componentPreimage_normalized
  intro a ha
  exact s.invariant a (modelActors_preserve_sylow h d a ha)

/-- The full covering seed has a self-centralizing two-core. -/
theorem seed_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action)) :
    centralizer (pCore 2 (componentPreimage d s.localSubgroup) :
      Set (componentPreimage d s.localSubgroup)) ≤
        pCore 2 (componentPreimage d s.localSubgroup) := by
  have hi := preimage_selfCentralizingCore h d s.localSubgroup s.selfCentralizing
  let e := (s.localSubgroup.comap (quotientMap d)).equivMapOfInjective
    L.subtype L.subtype_injective
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hi

/-- Characteristic two lifts across the central kernel and the whole component orbit. -/
theorem seed_localOvergroup_even (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action)) :
    localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup ∈ Chapter1.He G := by
  let := h.finite
  exact h.component.relative_local_adjoin_centralizer h.component_le
    (componentPreimage_le d s.localSubgroup) (map_subtype_le _)
    (S.isPGroup'.map H.subtype) (seed_normalized h d s)
    ((inf_centralizer_pCoreIn_le_iff 2 _).mpr (seed_selfCentralizingCore h d s))

/-- The preimage seed has exactly the supplied quotient, with its own full two-core. -/
def preimageQuotientEquiv (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) (P : Subgroup Carrier) :
    ((P.comap (quotientMap d)) ⧸ pCore 2 (P.comap (quotientMap d))) ≃*
      (P ⧸ pCore 2 P) := by
  let f := (QuotientGroup.mk' (pCore 2 P)).comp (preimageMap d P)
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (preimageMap_surjective d P)
  have hk : f.ker = pCore 2 (P.comap (quotientMap d)) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact preimageMap_pCore h d P
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The embedded covering seed has the actual SL₃(2) two-core quotient. -/
def seedQuotientEquiv (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action)) :
    ((componentPreimage d s.localSubgroup) ⧸
      pCore 2 (componentPreimage d s.localSubgroup)) ≃* LinearThreeTwo := by
  let e := (s.localSubgroup.comap (quotientMap d)).equivMapOfInjective
    L.subtype L.subtype_injective
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    ((preimageQuotientEquiv h d s.localSubgroup).trans s.quotientIso)

/-- Assemble the fixed-residual generation and the local structural calculations. -/
def localGeometry_of_normalDirectPowerSection (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action))
    (q : NormalDirectPowerSection 2
      (localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup) LinearThreeTwo) :
    LocalGeometry ((S : Subgroup H).map H.subtype) d where
  localSubgroup := s.localSubgroup
  generatorA := by rw [seed_centralizerImage_sup h d s]; trivial
  generatorB := by rw [seed_centralizerImage_sup h d s]; trivial
  even := seed_localOvergroup_even h d s
  quotientSection := q

end CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
