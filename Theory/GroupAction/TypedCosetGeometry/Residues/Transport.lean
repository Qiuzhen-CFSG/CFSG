module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Connectivity
public import Theory.GroupAction.TypedCosetGeometry.Residues.Local
public import Theory.GroupAction.TypedCosetGeometry.Residues.Quotient

/-!
# Residues in local quotients

A standard vertex residue is the intrinsic rank-two coset geometry in its
vertex group. Composing this identification with a surjection gives its
geometry in a local quotient whenever the kernel lies in both parabolics.
The composite preserves types, incidence and the action, and transports the
residue action kernel. Graph isomorphisms package the incidence identifications.

The middle product condition is used only for incidence reflection, not for
the underlying bijections, equivariance or action-kernel identities.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3–4,
printed pp. 419–420; the coset geometry construction of Aschbacher,
*Sporadic Groups*, §4.
-/

@[expose] public section
namespace Subgroup.CosetGeometry

variable {G K : Type*} [Group G] [Group K]
variable (F : Fin 3 → Subgroup G) (i : Fin 3)

/-- The intrinsic coset geometry is the actual induced residue graph. -/
noncomputable def residueIntrinsicGraphIso (hprod : MiddleProduct F) :
    incidenceGraph (intrinsicFamily F i) ≃g residueGraph F (base F i) where
  toEquiv := residueIntrinsicEquiv F i
  map_rel_iff' := by
    intro u v
    simp only [residueGraph_adj, incidenceGraph_adj, residueIntrinsicEquiv_type,
      residueIntrinsicEquiv_incident_iff F i hprod]
    exact and_congr (not_congr ⟨Subtype.ext, congrArg Subtype.val⟩) Iff.rfl

variable (φ : F i →* K) (hφ : Function.Surjective φ)
variable (hker : φ.ker ≤ intrinsicIntersection F i)

/-- The actual residue, expressed as typed cosets of the image parabolics. -/
noncomputable def residueTransportEquiv :
    Residue F (base F i) ≃ Vertex (fun j => (intrinsicPair F i j).map φ) :=
  (residueIntrinsicEquiv F i).symm.trans
    (QuotientTransport.equiv (intrinsicFamily F i) φ hφ
      (fun j => hker.trans (iInf_le _ j)))

@[simp] theorem residueTransportEquiv_type (v : Residue F (base F i)) :
    (residueTransportEquiv F i φ hφ hker v).type.val = v.val.type := by
  obtain ⟨w, rfl⟩ := (residueIntrinsicEquiv F i).surjective v
  simp [residueTransportEquiv]

/-- Translation in the vertex group becomes translation by its image. -/
@[simp] theorem residueTransportEquiv_smul (a : F i) (v : Residue F (base F i)) :
    residueTransportEquiv F i φ hφ hker (a • v) =
      φ a • residueTransportEquiv F i φ hφ hker v := by
  obtain ⟨w, rfl⟩ := (residueIntrinsicEquiv F i).surjective v
  rw [← residueIntrinsicEquiv_equivariant]
  simp [residueTransportEquiv]

/-- The local quotient preserves and reflects incidence in the actual residue. -/
@[simp] theorem residueTransportEquiv_incident_iff (hprod : MiddleProduct F)
    (u v : Residue F (base F i)) :
    Incident (fun j => (intrinsicPair F i j).map φ)
      (residueTransportEquiv F i φ hφ hker u)
      (residueTransportEquiv F i φ hφ hker v) ↔ Incident F u.val v.val := by
  obtain ⟨x, rfl⟩ := (residueIntrinsicEquiv F i).surjective u
  obtain ⟨y, rfl⟩ := (residueIntrinsicEquiv F i).surjective v
  simp [residueTransportEquiv, residueIntrinsicEquiv_incident_iff F i hprod]

/-- A local quotient identifies the residue graph with the image coset graph. -/
noncomputable def residueTransportGraphIso (hprod : MiddleProduct F) :
    residueGraph F (base F i) ≃g
      incidenceGraph (fun j => (intrinsicPair F i j).map φ) where
  toEquiv := residueTransportEquiv F i φ hφ hker
  map_rel_iff' := by
    intro u v
    simp only [incidenceGraph_adj, residueGraph_adj,
      residueTransportEquiv_incident_iff F i φ hφ hker hprod]
    apply and_congr _ Iff.rfl
    apply not_congr
    constructor
    · intro h
      simpa only [residueTransportEquiv_type] using congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      simpa only [residueTransportEquiv_type] using h

include hφ hker in
/-- Pulling back the local quotient action kernel gives the residue action kernel. -/
theorem residueTransport_action_kernel_comap :
    (MulAction.toPermHom K
      (Vertex (fun j => (intrinsicPair F i j).map φ))).ker.comap φ =
      (MulAction.toPermHom (F i) (Residue F (base F i))).ker := by
  rw [QuotientTransport.action_kernel_comap (intrinsicFamily F i) φ hφ
    (fun j => hker.trans (iInf_le _ j)), intrinsic_action_kernel,
    residue_action_kernel]
  rfl

include hφ hker in
/-- The local quotient action kernel is the image of the residue action kernel. -/
theorem residueTransport_action_kernel_map :
    ((MulAction.toPermHom (F i) (Residue F (base F i))).ker).map φ =
      (MulAction.toPermHom K
        (Vertex (fun j => (intrinsicPair F i j).map φ))).ker := by
  rw [← residueTransport_action_kernel_comap F i φ hφ hker,
    Subgroup.map_comap_eq_self_of_surjective hφ]

include hφ hker in
/-- The image chamber core pulls back to the core of the chamber in the vertex group. -/
theorem residueTransport_normalCore_comap :
    (⨅ j, (intrinsicPair F i j).map φ).normalCore.comap φ =
      ((⨅ j, F j).subgroupOf (F i)).normalCore := by
  rw [QuotientTransport.normalCore_iInf_comap (intrinsicFamily F i) φ hφ
    (fun j => hker.trans (iInf_le _ j))]
  exact congrArg Subgroup.normalCore (intrinsicIntersection_eq F i)

section Quotient
variable (N : Subgroup (F i)) [N.Normal]
variable (hN : N ≤ intrinsicIntersection F i)

/-- Quotient form of the residue identification; containment means that `N`
lies in both intrinsic parabolics. -/
noncomputable def residueQuotientEquiv :
    Residue F (base F i) ≃
      Vertex (fun j => (intrinsicPair F i j).map (QuotientGroup.mk' N)) :=
  residueTransportEquiv F i (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rwa [QuotientGroup.ker_mk'])

@[simp] theorem residueQuotientEquiv_type (v : Residue F (base F i)) :
    (residueQuotientEquiv F i N hN v).type.val = v.val.type :=
  residueTransportEquiv_type F i _ _ _ v

@[simp] theorem residueQuotientEquiv_smul (a : F i) (v : Residue F (base F i)) :
    residueQuotientEquiv F i N hN (a • v) =
      QuotientGroup.mk' N a • residueQuotientEquiv F i N hN v :=
  residueTransportEquiv_smul F i _ _ _ a v

@[simp] theorem residueQuotientEquiv_incident_iff (hprod : MiddleProduct F)
    (u v : Residue F (base F i)) :
    Incident (fun j => (intrinsicPair F i j).map (QuotientGroup.mk' N))
      (residueQuotientEquiv F i N hN u) (residueQuotientEquiv F i N hN v) ↔
      Incident F u.val v.val :=
  residueTransportEquiv_incident_iff F i _ _ _ hprod u v

include hN in
/-- Kernel pullback for the residue expressed in an actual quotient group. -/
theorem residueQuotient_action_kernel_comap :
    (MulAction.toPermHom (F i ⧸ N)
      (Vertex (fun j => (intrinsicPair F i j).map (QuotientGroup.mk' N)))).ker.comap
        (QuotientGroup.mk' N) =
      (MulAction.toPermHom (F i) (Residue F (base F i))).ker :=
  residueTransport_action_kernel_comap F i _ (QuotientGroup.mk'_surjective N)
    (by rwa [QuotientGroup.ker_mk'])

include hN in
/-- The action kernel in the quotient is the image of the local chamber core. -/
theorem residueQuotient_action_kernel_eq :
    (MulAction.toPermHom (F i ⧸ N)
      (Vertex (fun j => (intrinsicPair F i j).map (QuotientGroup.mk' N)))).ker =
      (((⨅ j, F j).subgroupOf (F i)).normalCore).map (QuotientGroup.mk' N) := by
  rw [← residueTransport_action_kernel_map F i (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk']),
    residue_action_kernel_chamber]

end Quotient
end Subgroup.CosetGeometry
