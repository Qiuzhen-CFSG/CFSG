module

public import Theory.GroupAction.TypedCosetGeometry

/-!
# Quotient transport of typed coset geometries

A surjective homomorphism whose kernel lies in every parabolic induces an
actual type-preserving equivalence of the typed coset geometries. Coset
injectivity follows from subgroup correspondence. A common representative
descends under the homomorphism, and surjectivity lifts a common representative
back upstairs; thus incidence and flags are preserved and reflected.

The equivalence intertwines the actions, so the original action kernel is the
pullback of the transported action kernel. The existing coset-action kernel
theorem then transports the normal core of the chamber subgroup. We give both
pullback and image identities, arbitrary-family results, and explicit
specializations for quotienting two parabolics by a common normal subgroup.
No finiteness or normality of the parabolics is required.

Source: the subgroup correspondence theorem and the standard coset geometry
construction; used for local quotient geometries in Aschbacher–Smith,
*The Classification of Quasithin Groups*, I.5.3–4, printed pp. 419–420.
-/

@[expose] public section

namespace Subgroup.CosetGeometry.QuotientTransport
variable {H K I : Type*} [Group H] [Group K]

/-- The map of cosets induced by a homomorphism. -/
def cosetMap (P : Subgroup H) (φ : H →* K) : H ⧸ P → K ⧸ P.map φ :=
  Quotient.map φ (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, rfl⟩)

@[simp] theorem cosetMap_mk (P : Subgroup H) (φ : H →* K) (g : H) :
    cosetMap P φ (g : H ⧸ P) = (φ g : K ⧸ P.map φ) := rfl

/-- Kernel containment proves injectivity on cosets; no coset injectivity is assumed. -/
theorem cosetMap_injective (P : Subgroup H) (φ : H →* K) (hker : φ.ker ≤ P) :
    Function.Injective (cosetMap P φ) := by
  intro a b
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      intro hab
      apply QuotientGroup.eq.mpr
      have hmem : a⁻¹ * b ∈ (P.map φ).comap φ := by
        simpa only [Subgroup.mem_comap, map_mul, map_inv] using QuotientGroup.eq.mp hab
      rwa [Subgroup.comap_map_eq_self hker] at hmem

/-- Surjectivity on representatives implies surjectivity on cosets. -/
theorem cosetMap_surjective (P : Subgroup H) (φ : H →* K)
    (hφ : Function.Surjective φ) : Function.Surjective (cosetMap P φ) := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨h, rfl⟩ := hφ k
  exact ⟨(h : H ⧸ P), rfl⟩

/-- A surjection induces a coset bijection when its kernel lies in the subgroup. -/
noncomputable def cosetEquiv (P : Subgroup H) (φ : H →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ P) : H ⧸ P ≃ K ⧸ P.map φ :=
  Equiv.ofBijective (cosetMap P φ)
    ⟨cosetMap_injective P φ hker, cosetMap_surjective P φ hφ⟩

variable (F : I → Subgroup H) (φ : H →* K) (hφ : Function.Surjective φ)
    (hker : ∀ i, φ.ker ≤ F i)

/-- Type-preserving transport of the actual typed vertices along a surjection. -/
noncomputable def equiv : Vertex F ≃ Vertex (fun i => (F i).map φ) where
  toFun v := ⟨v.type, cosetEquiv (F v.type) φ hφ (hker v.type) v.coset⟩
  invFun v := ⟨v.type, (cosetEquiv (F v.type) φ hφ (hker v.type)).symm v.coset⟩
  left_inv v := by rcases v with ⟨i, q⟩; simp
  right_inv v := by rcases v with ⟨i, q⟩; simp

@[simp] theorem equiv_type (v : Vertex F) : (equiv F φ hφ hker v).type = v.type := rfl

@[simp] theorem equiv_symm_type (v : Vertex (fun i => (F i).map φ)) :
    ((equiv F φ hφ hker).symm v).type = v.type := rfl

@[simp] theorem equiv_base (i : I) :
    equiv F φ hφ hker (base F i) = base (fun i => (F i).map φ) i := by
  change Vertex.mk (F := fun i => (F i).map φ) i ((φ 1 : K) : K ⧸ (F i).map φ) = _
  rw [map_one]
  rfl

@[simp] theorem equiv_mk (i : I) (g : H) :
    equiv F φ hφ hker ⟨i, (g : H ⧸ F i)⟩ = ⟨i, (φ g : K ⧸ (F i).map φ)⟩ := rfl

/-- Transport intertwines the original action with the action through the homomorphism. -/
@[simp] theorem equiv_smul (g : H) (v : Vertex F) :
    equiv F φ hφ hker (g • v) = φ g • equiv F φ hφ hker v := by
  rcases v with ⟨i, q⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have hs : g • (⟨i, (a : H ⧸ F i)⟩ : Vertex F) = ⟨i, (g * a : H)⟩ :=
    congrArg (Vertex.mk i) (MulAction.Quotient.smul_mk (F i) g a)
  rw [hs, equiv_mk, equiv_mk]
  change Vertex.mk (F := fun i => (F i).map φ) i ((φ (g * a) : K) : K ⧸ (F i).map φ) =
    Vertex.mk (F := fun i => (F i).map φ) i (φ g • (φ a : K ⧸ (F i).map φ))
  rw [MulAction.Quotient.smul_mk, map_mul]
  rfl

/-- Common representatives descend and lift, so incidence is preserved and reflected. -/
@[simp] theorem incident_equiv_iff (v w : Vertex F) :
    Incident (fun i => (F i).map φ) (equiv F φ hφ hker v) (equiv F φ hφ hker w) ↔
      Incident F v w := by
  constructor
  · rintro ⟨k, hv, hw⟩
    obtain ⟨g, rfl⟩ := hφ k
    refine ⟨g, ?_, ?_⟩
    · exact (cosetEquiv (F v.type) φ hφ (hker v.type)).injective hv
    · exact (cosetEquiv (F w.type) φ hφ (hker w.type)).injective hw
  · rintro ⟨g, hv, hw⟩
    exact ⟨φ g, congrArg (cosetMap (F v.type) φ) hv,
      congrArg (cosetMap (F w.type) φ) hw⟩

/-- Transport preserves and reflects pairwise incident flags. -/
@[simp] theorem isFlag_image_iff (s : Set (Vertex F)) :
    IsFlag (fun i => (F i).map φ) (equiv F φ hφ hker '' s) ↔ IsFlag F s := by
  constructor
  · intro hs v hv w hw
    exact (incident_equiv_iff F φ hφ hker v w).mp
      (hs _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩)
  · rintro hs _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact (incident_equiv_iff F φ hφ hker v w).mpr (hs v hv w hw)

include hφ hker in
/-- An element acts trivially upstairs exactly when its image acts trivially downstairs. -/
theorem action_kernel_comap :
    (MulAction.toPermHom K (Vertex (fun i => (F i).map φ))).ker.comap φ =
      (MulAction.toPermHom H (Vertex F)).ker := by
  ext g
  change (MulAction.toPermHom K (Vertex (fun i => (F i).map φ)) (φ g) = 1) ↔
    (MulAction.toPermHom H (Vertex F) g = 1)
  constructor
  · intro hg
    apply Equiv.Perm.ext
    intro v
    apply (equiv F φ hφ hker).injective
    change equiv F φ hφ hker (g • v) = equiv F φ hφ hker v
    rw [equiv_smul]
    exact Equiv.Perm.ext_iff.mp hg _
  · intro hg
    apply Equiv.Perm.ext
    intro w
    obtain ⟨v, rfl⟩ := (equiv F φ hφ hker).surjective w
    change φ g • equiv F φ hφ hker v = equiv F φ hφ hker v
    rw [← equiv_smul]
    exact congrArg (equiv F φ hφ hker) (Equiv.Perm.ext_iff.mp hg v)

include hφ hker in
/-- The kernel of the transported action is the image of the original action kernel. -/
theorem action_kernel_map :
    ((MulAction.toPermHom H (Vertex F)).ker).map φ =
      (MulAction.toPermHom K (Vertex (fun i => (F i).map φ))).ker := by
  rw [← action_kernel_comap F φ hφ hker, Subgroup.map_comap_eq_self_of_surjective hφ]

include hφ hker in
/-- Pullback of the chamber normal core, for an arbitrary indexed family. -/
theorem normalCore_iInf_comap :
    (⨅ i, (F i).map φ).normalCore.comap φ = (⨅ i, F i).normalCore := by
  simpa only [action_kernel] using action_kernel_comap F φ hφ hker

include hφ hker in
/-- Image of the chamber normal core, with no nonemptiness or finiteness requirement. -/
theorem normalCore_iInf_map :
    ((⨅ i, F i).normalCore).map φ = (⨅ i, (F i).map φ).normalCore := by
  rw [← normalCore_iInf_comap F φ hφ hker,
    Subgroup.map_comap_eq_self_of_surjective hφ]

/-- Normal-core transport for two parabolics. -/
theorem normalCore_inf_comap (P0 P1 : Subgroup H) (φ : H →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ P0 ⊓ P1) :
    (P0.map φ ⊓ P1.map φ).normalCore.comap φ = (P0 ⊓ P1).normalCore := by
  have h : ∀ b : Bool, φ.ker ≤ cond b P0 P1 := by
    intro b
    cases b
    · exact hker.trans inf_le_right
    · exact hker.trans inf_le_left
  simpa only [iInf_bool_eq, Bool.cond_true, Bool.cond_false] using
    normalCore_iInf_comap (fun b : Bool => cond b P0 P1) φ hφ h

/-- The normal core downstairs is the image of the normal core upstairs. -/
theorem normalCore_inf_map (P0 P1 : Subgroup H) (φ : H →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ P0 ⊓ P1) :
    ((P0 ⊓ P1).normalCore).map φ = (P0.map φ ⊓ P1.map φ).normalCore := by
  rw [← normalCore_inf_comap P0 P1 φ hφ hker,
    Subgroup.map_comap_eq_self_of_surjective hφ]

section Quotient
variable (N : Subgroup H) [N.Normal]

/-- The actual typed-coset equivalence under quotient by a common normal subgroup. -/
noncomputable def quotientEquiv (hN : N ≤ ⨅ i, F i) :
    Vertex F ≃ Vertex (fun i => (F i).map (QuotientGroup.mk' N)) :=
  equiv F (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (fun i => by rw [QuotientGroup.ker_mk']; exact hN.trans (iInf_le F i))

@[simp] theorem quotientEquiv_type (hN : N ≤ ⨅ i, F i) (v : Vertex F) :
    (quotientEquiv F N hN v).type = v.type := rfl

@[simp] theorem quotientEquiv_mk (hN : N ≤ ⨅ i, F i) (i : I) (g : H) :
    quotientEquiv F N hN ⟨i, (g : H ⧸ F i)⟩ =
      ⟨i, ((QuotientGroup.mk' N g) : (H ⧸ N) ⧸ (F i).map (QuotientGroup.mk' N))⟩ := rfl

@[simp] theorem quotientEquiv_smul (hN : N ≤ ⨅ i, F i) (g : H) (v : Vertex F) :
    quotientEquiv F N hN (g • v) = (QuotientGroup.mk' N g) • quotientEquiv F N hN v :=
  equiv_smul F _ _ _ g v

@[simp] theorem incident_quotientEquiv_iff (hN : N ≤ ⨅ i, F i) (v w : Vertex F) :
    Incident (fun i => (F i).map (QuotientGroup.mk' N))
      (quotientEquiv F N hN v) (quotientEquiv F N hN w) ↔ Incident F v w :=
  incident_equiv_iff F _ _ _ v w

@[simp] theorem isFlag_quotientEquiv_image_iff (hN : N ≤ ⨅ i, F i)
    (s : Set (Vertex F)) :
    IsFlag (fun i => (F i).map (QuotientGroup.mk' N)) (quotientEquiv F N hN '' s) ↔
      IsFlag F s :=
  isFlag_image_iff F _ _ _ s

/-- Pullback of the action kernel along the quotient map. -/
theorem quotient_action_kernel_comap (hN : N ≤ ⨅ i, F i) :
    (MulAction.toPermHom (H ⧸ N)
      (Vertex (fun i => (F i).map (QuotientGroup.mk' N)))).ker.comap (QuotientGroup.mk' N) =
      (MulAction.toPermHom H (Vertex F)).ker :=
  action_kernel_comap F _ (QuotientGroup.mk'_surjective N)
    (fun i => by rw [QuotientGroup.ker_mk']; exact hN.trans (iInf_le F i))

/-- The quotient action kernel is the image of the original action kernel. -/
theorem quotient_action_kernel_map (hN : N ≤ ⨅ i, F i) :
    ((MulAction.toPermHom H (Vertex F)).ker).map (QuotientGroup.mk' N) =
      (MulAction.toPermHom (H ⧸ N)
        (Vertex (fun i => (F i).map (QuotientGroup.mk' N)))).ker :=
  action_kernel_map F _ (QuotientGroup.mk'_surjective N)
    (fun i => by rw [QuotientGroup.ker_mk']; exact hN.trans (iInf_le F i))

/-- Pair specialization, with `true` indexing `P0` and `false` indexing `P1`. -/
noncomputable def pairQuotientEquiv (P0 P1 : Subgroup H) (hN : N ≤ P0 ⊓ P1) :
    Vertex (fun b : Bool => cond b P0 P1) ≃
      Vertex (fun b : Bool => (cond b P0 P1).map (QuotientGroup.mk' N)) :=
  quotientEquiv (fun b : Bool => cond b P0 P1) N
    (by simpa only [iInf_bool_eq, Bool.cond_true, Bool.cond_false] using hN)

/-- The two-parabolic action-kernel identity with the common-normal-subgroup hypothesis. -/
theorem pair_quotient_action_kernel_comap (P0 P1 : Subgroup H) (hN : N ≤ P0 ⊓ P1) :
    (MulAction.toPermHom (H ⧸ N)
      (Vertex (fun b : Bool => (cond b P0 P1).map (QuotientGroup.mk' N)))).ker.comap
        (QuotientGroup.mk' N) =
      (MulAction.toPermHom H (Vertex (fun b : Bool => cond b P0 P1))).ker :=
  quotient_action_kernel_comap (fun b : Bool => cond b P0 P1) N
    (by simpa only [iInf_bool_eq, Bool.cond_true, Bool.cond_false] using hN)

/-- Normal-core pullback for a pair of parabolics under a quotient map. -/
theorem quotient_normalCore_inf_comap (P0 P1 : Subgroup H) (hN : N ≤ P0 ⊓ P1) :
    ((P0.map (QuotientGroup.mk' N) ⊓ P1.map (QuotientGroup.mk' N)).normalCore).comap
      (QuotientGroup.mk' N) = (P0 ⊓ P1).normalCore :=
  normalCore_inf_comap P0 P1 _ (QuotientGroup.mk'_surjective N)
    (by rwa [QuotientGroup.ker_mk'])

/-- The normal core in the quotient is the quotient image of the original core. -/
theorem quotient_normalCore_inf_map (P0 P1 : Subgroup H) (hN : N ≤ P0 ⊓ P1) :
    ((P0 ⊓ P1).normalCore).map (QuotientGroup.mk' N) =
      (P0.map (QuotientGroup.mk' N) ⊓ P1.map (QuotientGroup.mk' N)).normalCore :=
  normalCore_inf_map P0 P1 _ (QuotientGroup.mk'_surjective N)
    (by rwa [QuotientGroup.ker_mk'])
end Quotient

end Subgroup.CosetGeometry.QuotientTransport
