module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreLineAction
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute.Irreducibility

/-!
# Faithfulness of the point radical on its neighbors

The kernel of the E-action on all neighbors is an invariant subspace of the
original Todd cocode: the literal semidirect-product complement conjugates
its vectors by the actual M₂₄ action. Irreducibility makes that kernel zero
or the whole module. The latter would trivialize the already proved order-four
line action, so the kernel is zero. Conjugation transports this to every
ambient point, supplying the unchanged neighbor-faithfulness Input field.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §§4–5, pp.598–600,
DOI 10.1007/BF01232280. The native cocode irreducibility is the proved
Mathieu module theorem, not an extra incidence hypothesis.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)

private noncomputable def toddLift : M24 →* G :=
  a.P.M.subtype.comp (a.P.toddEquiv.toMonoidHom.comp SemidirectProduct.inr)

private theorem toddLift_point (g : M24) :
    a.toddLift g • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
  rw [Cosets.smul_vertex,mul_one]
  exact (Cosets.vertex_eq_base _ _).mpr (a.P.toddEquiv (SemidirectProduct.inr g)).property

private theorem vector_action (g : M24) (v : Cocode) :
    a.P.vectorEmbedding (Multiplicative.ofAdd (cocodeRepresentation g v)) =
      a.toddLift g * a.P.vectorEmbedding (Multiplicative.ofAdd v) * (a.toddLift g)⁻¹ := by
  let j := a.P.M.subtype.comp a.P.toddEquiv.toMonoidHom
  have hh := congrArg j (SemidirectProduct.inl_aut (φ := toddAction) g (Multiplicative.ofAdd v))
  have hv : toddAction g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (cocodeRepresentation g v) := rfl
  rw [hv] at hh
  simpa only [j,PointData.vectorEmbedding,toddLift,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul,map_inv] using hh

private noncomputable def neighborKernel : Subrepresentation cocodeRepresentation where
  toSubmodule := {
    carrier := {v | ∀ y : Point a.P, Adj a.L (Cosets.vertex a.P.M 1) y →
      a.P.vectorEmbedding (Multiplicative.ofAdd v) • y = y}
    zero_mem' := by intro y _; change a.P.vectorEmbedding 1 • y = y; rw [map_one,one_smul]
    add_mem' := by
      intro v w hv hw y hy
      change a.P.vectorEmbedding (Multiplicative.ofAdd v * Multiplicative.ofAdd w) • y = y
      rw [map_mul,mul_smul,hw y hy,hv y hy]
    smul_mem' := by
      intro c v hv
      rcases (by decide : ∀ c : ZMod 2, c=0 ∨ c=1) c with rfl|rfl
      · intro y _; simp only [zero_smul]; change a.P.vectorEmbedding 1 • y = y; rw [map_one,one_smul]
      · simpa only [one_smul] using hv }
  apply_mem_toSubmodule := by
    intro g v hv y hy
    have hi : Adj a.L (Cosets.vertex a.P.M 1) ((a.toddLift g)⁻¹ • y) := by
      have hh := adj_smul (a.toddLift g⁻¹) hy
      rw [a.toddLift_point,map_inv] at hh
      exact hh
    rw [a.vector_action,mul_smul,mul_smul,hv _ hi,smul_inv_smul]

private theorem neighborKernel_eq_bot : a.neighborKernel = ⊥ := by
  rcases cocode_isIrreducible.eq_bot_or_eq_top a.neighborKernel with hb | ht
  · exact hb
  have hfix (n : a.L.G₂) (hn : (n : G) ∈ a.P.E) : a.linePointAction n = 1 := by
    obtain ⟨v,hv⟩ := hn
    have hvK : v.toAdd ∈ a.neighborKernel := by rw [ht]; trivial
    apply Equiv.ext
    intro y
    apply Subtype.ext
    rw [a.linePointAction_apply]
    change (n : G) • y.val = y.val
    by_cases hy : y.val = Cosets.vertex a.P.M 1
    · rw [hy,Cosets.smul_vertex,mul_one]
      exact (Cosets.vertex_eq_base _ _).mpr (a.P.E_le ⟨v,hv⟩)
    · have hadj : Adj a.L (Cosets.vertex a.P.M 1) y.val :=
        ⟨(fun he => hy he.symm),Cosets.vertex a.L.G₂ 1,⟨1,rfl,rfl⟩,y.property⟩
      change ∀ y : Point a.P, Adj a.L (Cosets.vertex a.P.M 1) y →
        a.P.vectorEmbedding (Multiplicative.ofAdd v.toAdd) • y = y at hvK
      have hh := hvK _ hadj
      change a.P.vectorEmbedding v • y.val = y.val at hh
      rwa [hv] at hh
  have he : (a.P.E.subgroupOf a.L.G₂).map a.linePointAction = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨n,hn,rfl⟩
    exact hfix n hn
  have hc := a.radical_line_action_card
  rw [he,Subgroup.card_bot] at hc
  norm_num at hc

/-- Faithfulness of E on the neighbors of the original point follows from
irreducibility of its actual Todd action and its nontrivial line action. -/
theorem core_faithful_base (u : a.P.E)
    (hu : ∀ y, Adj a.L (Cosets.vertex a.P.M 1) y → (u : G) • y = y) : (u : G)=1 := by
  obtain ⟨v,hv⟩ := u.property
  have hm : v.toAdd ∈ a.neighborKernel := by
    intro y hy
    change a.P.vectorEmbedding v • y = y
    rw [hv]
    exact hu y hy
  rw [a.neighborKernel_eq_bot] at hm
  have hv0 : v.toAdd = 0 := hm
  have hv1 : v=1 := congrArg Multiplicative.ofAdd hv0
  rw [←hv,hv1,map_one]

/-- The unchanged neighbor-faithfulness field at every ambient point. -/
theorem core_faithful_neighbors (x : Point a.P) (u : coreAt a.P x)
    (hu : ∀ y, Adj a.L x y → (u : G) • y = y) : (u : G)=1 := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hm := (coreAt_vertex a.P g).le u.property
    change g⁻¹*(u : G)*(g⁻¹)⁻¹ ∈ a.P.E at hm
    let e : a.P.E := ⟨g⁻¹*(u : G)*g,by simpa only [inv_inv] using hm⟩
    have he : (e : G)=1 := a.core_faithful_base e (by
      intro y hy
      have hh : Adj a.L (Cosets.vertex a.P.M g) (g • y) := by
        simpa only [Cosets.smul_vertex,mul_one] using adj_smul g hy
      change (g⁻¹*(u : G)*g) • y = y
      rw [mul_smul,mul_smul,hu _ hh,inv_smul_smul])
    have hh := congrArg (fun v : G => g*v*g⁻¹) he
    change g*(g⁻¹*(u : G)*g)*g⁻¹ = g*1*g⁻¹ at hh
    simpa only [mul_assoc,mul_inv_cancel,inv_mul_cancel_left,mul_one,mul_inv_cancel_left] using hh

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
