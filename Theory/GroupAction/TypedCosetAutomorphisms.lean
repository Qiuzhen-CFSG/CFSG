module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Connectivity
public import Theory.GroupAction.TypedCosetGeometry.Residues.Quotient

/-!
# Automorphisms of typed coset incidence graphs

A group automorphism preserving each member of a subgroup family acts on the
actual left cosets, preserves their types and incidence, and intertwines left
translation with the original group automorphism. Composing this graph action
with translation realizes an inner twist, with its exact conjugation formula.
No normality, finiteness or faithfulness assumption is needed.

The proof transports each coset along the automorphism, uses the subgroup
invariance to identify its target, and checks incidence on common
representatives. This is the semilinear building action used with fixed-tree
centers in the rank-two Borel--Tits argument (GLS3, Theorem 3.1.3).
-/

@[expose] public section
noncomputable section

namespace Subgroup.CosetGeometry
variable {G I : Type*} [Group G] (F : I → Subgroup G)

/-- The action on left cosets of an invariant subgroup, without normality. -/
def cosetAutomorphism (H : Subgroup G) (b : MulAut G)
    (hb : H.map b.toMonoidHom = H) : G ⧸ H ≃ G ⧸ H :=
  (QuotientTransport.cosetEquiv H b.toMonoidHom b.surjective
    (by rw [MonoidHom.ker_eq_bot _ b.injective]; exact bot_le)).trans
      (Subgroup.quotientEquivOfEq hb)

@[simp] theorem cosetAutomorphism_mk (H : Subgroup G) (b : MulAut G)
    (hb : H.map b.toMonoidHom = H) (g : G) :
    cosetAutomorphism H b hb (g : G ⧸ H) = (b g : G ⧸ H) :=
  Subgroup.quotientEquivOfEq_mk hb (b g)

@[simp] theorem cosetAutomorphism_smul (H : Subgroup G) (b : MulAut G)
    (hb : H.map b.toMonoidHom = H) (g : G) (q : G ⧸ H) :
    cosetAutomorphism H b hb (g • q) = b g • cosetAutomorphism H b hb q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [MulAction.Quotient.smul_mk, cosetAutomorphism_mk, smul_eq_mul, map_mul]

/-- An automorphism preserving each subgroup acts on its typed cosets. -/
def automorphismEquiv (b : MulAut G) (hb : ∀ i, (F i).map b.toMonoidHom = F i) :
    Vertex F ≃ Vertex F where
  toFun v := ⟨v.type, cosetAutomorphism (F v.type) b (hb v.type) v.coset⟩
  invFun v := ⟨v.type, (cosetAutomorphism (F v.type) b (hb v.type)).symm v.coset⟩
  left_inv v := by rcases v with ⟨i, q⟩; simp
  right_inv v := by rcases v with ⟨i, q⟩; simp

@[simp] theorem automorphismEquiv_type (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (v : Vertex F) :
    (automorphismEquiv F b hb v).type = v.type := rfl

@[simp] theorem automorphismEquiv_mk (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (i : I) (g : G) :
    automorphismEquiv F b hb ⟨i, (g : G ⧸ F i)⟩ = ⟨i, (b g : G ⧸ F i)⟩ := by
  exact congrArg (Vertex.mk i) (cosetAutomorphism_mk (F i) b (hb i) g)

@[simp] theorem automorphismEquiv_base (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (i : I) :
    automorphismEquiv F b hb (base F i) = base F i := by
  simpa only [base, map_one] using automorphismEquiv_mk F b hb i 1

@[simp] theorem automorphismEquiv_smul (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (g : G) (v : Vertex F) :
    automorphismEquiv F b hb (g • v) = b g • automorphismEquiv F b hb v := by
  rcases v with ⟨i, q⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change automorphismEquiv F b hb ⟨i, g • (x : G ⧸ F i)⟩ = _
  rw [MulAction.Quotient.smul_mk, automorphismEquiv_mk, automorphismEquiv_mk]
  change Vertex.mk i ((b (g * x) : G) : G ⧸ F i) =
    Vertex.mk i (b g • (b x : G ⧸ F i))
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, map_mul]

@[simp] theorem incident_automorphismEquiv_iff (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (v w : Vertex F) :
    Incident F (automorphismEquiv F b hb v) (automorphismEquiv F b hb w) ↔
      Incident F v w := by
  constructor
  · rintro ⟨x, hv, hw⟩
    obtain ⟨g, rfl⟩ := b.surjective x
    refine ⟨g, ?_, ?_⟩
    · apply (cosetAutomorphism (F v.type) b (hb v.type)).injective
      exact (cosetAutomorphism_mk (F v.type) b (hb v.type) g).trans hv
    · apply (cosetAutomorphism (F w.type) b (hb w.type)).injective
      exact (cosetAutomorphism_mk (F w.type) b (hb w.type) g).trans hw
  · rintro ⟨g, hv, hw⟩
    refine ⟨b g, ?_, ?_⟩
    · exact (cosetAutomorphism_mk (F v.type) b (hb v.type) g).symm.trans
        (congrArg (cosetAutomorphism (F v.type) b (hb v.type)) hv)
    · exact (cosetAutomorphism_mk (F w.type) b (hb w.type) g).symm.trans
        (congrArg (cosetAutomorphism (F w.type) b (hb w.type)) hw)

/-- A subgroup-preserving automorphism induces an automorphism of the incidence graph. -/
def automorphismGraphIso (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) :
    incidenceGraph F ≃g incidenceGraph F where
  toEquiv := automorphismEquiv F b hb
  map_rel_iff' := by intro v w; simp

@[simp] theorem automorphismGraphIso_type (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (v : Vertex F) :
    (automorphismGraphIso F b hb v).type = v.type := rfl

@[simp] theorem automorphismGraphIso_smul (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (g : G) (v : Vertex F) :
    automorphismGraphIso F b hb (g • v) = b g • automorphismGraphIso F b hb v :=
  automorphismEquiv_smul F b hb g v

/-- Translating the subgroup-preserving automorphism realizes an inner twist. -/
def innerAutomorphismGraphIso (k : G) (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) :
    incidenceGraph F ≃g incidenceGraph F :=
  (automorphismGraphIso F b hb).trans (translationGraphIso F k)

@[simp] theorem innerAutomorphismGraphIso_apply (k : G) (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (v : Vertex F) :
    innerAutomorphismGraphIso F k b hb v = k • automorphismGraphIso F b hb v := rfl

@[simp] theorem innerAutomorphismGraphIso_type (k : G) (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (v : Vertex F) :
    (innerAutomorphismGraphIso F k b hb v).type = v.type := rfl

/-- The inner twist is equivariant for the original automorphism of the group. -/
@[simp] theorem innerAutomorphismGraphIso_smul (k : G) (b : MulAut G)
    (hb : ∀ i, (F i).map b.toMonoidHom = F i) (g : G) (v : Vertex F) :
    innerAutomorphismGraphIso F k b hb (g • v) =
      (MulAut.conj k * b) g • innerAutomorphismGraphIso F k b hb v := by
  simp only [innerAutomorphismGraphIso_apply, automorphismGraphIso_smul,
    MulAut.mul_apply, MulAut.conj_apply, ← mul_smul, inv_mul_cancel_right]

end Subgroup.CosetGeometry
