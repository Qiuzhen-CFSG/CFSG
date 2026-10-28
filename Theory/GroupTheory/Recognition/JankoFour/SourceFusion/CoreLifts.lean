module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.FixedCore
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.ToddInvolutions
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Normalizer
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.CoreRepresentatives
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.Displacements

/-!
# The four Todd involution lifts fuse into the original plane core

Both native involution classes meet the sextet two-core. Their canonical
Todd lifts lie in Q by the minimal-normal/index argument. Every such lift
fixes at least 64 elements of E intersect Q, whereas its displacement image
has order at most 32. A vector outside that image gives the second fixed
coset. Transport of the native fixed-coset calculation supplies actual
conjugators in M for all four original representatives.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.4), printed p.602.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu MathieuCode
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open LocalGeometry LocalGeometry.LocalSubgroups SourceIncidence
open Representation.BinaryOffender
/-- Transport the nonzero fixed-coset calculation using the actual native
quotient conjugator and the original Todd splitting. -/
lemma todd_nonzero_coset_transport (b : Bool) (s g : M24)
    (hg : MulAut.conj g (if b then M24InvolutionCentralizers.involution2A
      else M24InvolutionCentralizers.involution2B) = s)
    (v : Cocode) (hv : cocodeRepresentation s v = v)
    (hn : ¬ ∃ w : Cocode, v = cocodeRepresentation s w - w) :
    IsConj (toddLift b true) (⟨Multiplicative.ofAdd v,s⟩ : ToddGroup) := by
  let r := if b then M24InvolutionCentralizers.involution2A else M24InvolutionCentralizers.involution2B
  have hi (w : Cocode) : cocodeRepresentation s (cocodeRepresentation g w) =
      cocodeRepresentation g (cocodeRepresentation r w) := by
    rw [←hg]
    change cocodeRepresentation (g*r*g⁻¹) (cocodeRepresentation g w) = _
    simp only [map_mul,Module.End.mul_apply,cocodeRepresentation.inv_self_apply]
  have hinj : Function.Injective (cocodeRepresentation g) := by
    intro u w he
    have he' := congrArg (cocodeRepresentation g⁻¹) he
    simpa only [cocodeRepresentation.inv_self_apply] using he'
  let w := cocodeRepresentation g⁻¹ v
  have hw : cocodeRepresentation r w = w := by
    apply hinj
    rw [←hi]
    change cocodeRepresentation s (cocodeRepresentation g (cocodeRepresentation g⁻¹ v)) =
      cocodeRepresentation g (cocodeRepresentation g⁻¹ v)
    rw [cocodeRepresentation.self_inv_apply,hv]
  have hwn : ¬ ∃ u : Cocode, w = cocodeRepresentation r u - u := by
    rintro ⟨u,hu⟩
    apply hn
    refine ⟨cocodeRepresentation g u,?_⟩
    have he := congrArg (cocodeRepresentation g) hu
    rw [map_sub,←hi] at he
    simpa only [w,cocodeRepresentation.self_inv_apply] using he
  have hc := toddLift_nonzero_coset b w hw hwn
  apply hc.trans
  apply isConj_iff.mpr
  refine ⟨SemidirectProduct.inr g,?_⟩
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left,SemidirectProduct.mul_right,
      SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.inv_left,inv_one,map_one,one_mul,mul_one]
    change Multiplicative.ofAdd (cocodeRepresentation g (cocodeRepresentation g⁻¹ v)) = _
    rw [cocodeRepresentation.self_inv_apply]
  · exact hg


variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

noncomputable def toddSection (a : LocalData h) : M24 →* G :=
  a.P.M.subtype.comp (a.P.toddEquiv.toMonoidHom.comp SemidirectProduct.inr)

lemma toddSection_mem (a : LocalData h) (s : M24) : toddSection a s ∈ a.P.M :=
  (a.P.toddEquiv (SemidirectProduct.inr s)).property

lemma toddSection_projection (a : LocalData h) (s : M24) :
    a.P.projection ⟨toddSection a s,toddSection_mem a s⟩ = s := by
  change (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inr s))).right = s
  rw [MulEquiv.symm_apply_apply]
  rfl

lemma toddSection_core (a : LocalData h) (s : M24)
    (hs : s ∈ (Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer a.sextet).pCoreIn 2) :
    toddSection a s ∈ ambientCore z := by
  obtain ⟨s,hs,rfl⟩ := hs
  exact ⟨planeComplement a s,planeComplement_core_le a ⟨s,hs,rfl⟩,rfl⟩

lemma pointLift_false_section (a : LocalData h) (b : Bool) :
    pointLift a b false = toddSection a (if b then M24InvolutionCentralizers.involution2A
      else M24InvolutionCentralizers.involution2B) := by
  rw [pointLift_coe,toddLift_false]
  rfl

/-- Both pure quotient representatives fuse into the actual original plane
core by conjugators in the original point group. -/
lemma pure_pointLift_into_core (a : LocalData h) (b : Bool) :
    ∃ m ∈ a.P.M, MulAut.conj m (pointLift a b false) ∈ ambientCore z := by
  obtain ⟨s,hs,hc⟩ := J4Fusion.sextet_core_class a.sextet b
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  refine ⟨toddSection a g,toddSection_mem a g,?_⟩
  rw [pointLift_false_section]
  change toddSection a g * toddSection a _ * (toddSection a g)⁻¹ ∈ _
  rw [←map_inv,←map_mul,←map_mul,hg]
  exact toddSection_core a s hs

/-- The fixed subgroup used by the source argument contains a vector outside
all displacements, in the same original Todd coordinates. -/
lemma core_fixed_nondisplacement (a : LocalData h) (s : M24)
    (hs : s ∈ (Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer a.sextet).pCoreIn 2)
    (ho : orderOf s = 2) :
    ∃ v : Cocode, a.P.vectorEmbedding (Multiplicative.ofAdd v) ∈ ambientCore z ∧
      cocodeRepresentation s v = v ∧
      ¬ ∃ w : Cocode, v = cocodeRepresentation s w - w := by
  let U := a.P.E ⊓ ambientCore z ⊓ centralizer (toddSection a s)
  have hU : U ≤ a.P.E := inf_le_left.trans inf_le_left
  have hcard : 64 ≤ Nat.card (toddSubspace a.P U) := by
    rw [toddSubspace_card a.P U hU]
    exact planeCore_fixed_card a _ (toddSection_core a s hs)
  obtain ⟨v,hv,hn⟩ := J4Fusion.exists_not_displacement s ho (toddSubspace a.P U) hcard
  change a.P.vectorEmbedding (Multiplicative.ofAdd v) ∈ U at hv
  refine ⟨v,hv.1.2,?_,hn⟩
  have hh := vector_conj a.P ⟨toddSection a s,toddSection_mem a s⟩ v
  rw [toddSection_projection] at hh
  have hc := mem_centralizer_singleton_iff.mp hv.2
  change toddSection a s * a.P.vectorEmbedding (Multiplicative.ofAdd v) *
    (toddSection a s)⁻¹ = _ at hh
  rw [hc.symm,mul_inv_cancel_right] at hh
  exact (congrArg Multiplicative.toAdd (a.P.vectorEmbedding_injective hh)).symm

/-- All four outside-radical Todd representatives fuse into the original Q,
with actual point-group conjugators. -/
lemma pointLift_into_core (a : LocalData h) (b e : Bool) :
    ∃ m ∈ a.P.M, MulAut.conj m (pointLift a b e) ∈ ambientCore z := by
  cases e
  · exact pure_pointLift_into_core a b
  · obtain ⟨s,hs,hc⟩ := J4Fusion.sextet_core_class a.sextet b
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    have ho : orderOf s = 2 := by
      rw [←hg]
      change orderOf (MulAut.conj g _) = 2
      rw [(MulAut.conj g).orderOf_eq]
      cases b
      · exact M24InvolutionCentralizers.involution2B_order
      · exact M24InvolutionCentralizers.involution2A_order
    obtain ⟨v,hvQ,hv,hn⟩ := core_fixed_nondisplacement a s hs ho
    have ht := todd_nonzero_coset_transport b s g hg v hv hn
    obtain ⟨m,hm⟩ := isConj_iff.mp (a.P.toddEquiv.toMonoidHom.map_isConj ht)
    refine ⟨m,m.property,?_⟩
    have he := congrArg Subtype.val hm
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,MulEquiv.coe_toMonoidHom] at he
    rw [pointLift_coe]
    change (m : G) * (a.P.toddEquiv (toddLift b true) : G) * (m : G)⁻¹ ∈ _
    rw [he]
    rw [SemidirectProduct.mk_eq_inl_mul_inr,map_mul,Subgroup.coe_mul]
    exact (ambientCore z).mul_mem hvQ (toddSection_core a s hs)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
