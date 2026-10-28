module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.HexadCommutant
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapModuleReduction
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneFlags

/-!
# All automorphisms of the original point-plane overlap

The full native action marking carries one conjugate of the certified even
hexad preimage into the original overlap. Its matrix commutant consists of
the three cubic scalars. The overlap has an actual outer actor, which inverts
the scalar, so the centralizer of its full action on Q/Z(Q) is trivial.
Transport through the same original core coordinates closes the residual
kernel left by the quotient calculation. Consequently every automorphism
of I is inner followed by the constructed Todd and plane twists.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
All scalar attachments and original quotient embeddings are retained.
Local-map alignment and the full edge equation are subsequent obligations.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension M22TripleCover.Ambient
open scoped Matrix Pointwise

private theorem native_cover_projection (g : M22TripleCover) :
    quotientConjugation (coverInclusion g) =
      MulAut.conj (⟨corePermutationAction g,corePermutationAction_range_eq_M22.le ⟨g,rfl⟩⟩ : M22) := by
  change MulAut.centralQuotientAction M22TripleCover.centralQuotientEquiv (MulAut.conj g) = _
  rw [MulAut.centralQuotientAction_conj]
  rfl

private theorem exists_matrix_implementing {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (N : V ≃ₗ[ZMod 2] M22TripleCover.BinarySpace) (F : V ≃ₗ[ZMod 2] V) :
    ∃ m : Matrix12ˣ, ∀ v, (m : Matrix12)*ᵥ N v=N (F v) := by
  let m : Matrix12ˣ := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (N.symm.trans (F.trans N)))
  refine ⟨m,fun v => ?_⟩
  change (Matrix.GeneralLinearGroup.toLin m).val (N v)=_
  rw [MulEquiv.apply_symm_apply]
  change N (F (N.symm (N v)))=N (F v)
  rw [LinearEquiv.symm_apply_apply]

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)
variable [IsExtraspecial 2 (core z)]

/-- The chosen original hexad contains a single conjugate of the certified
native even hexad preimage, in the same full core-module coordinates. -/
theorem overlap_native_hexad_marking :
    ∃ n : actionGroup, ∀ g : M22TripleCover,
      m22Hexad123.image (corePermutationAction g)=m22Hexad123 →
      (coreAmbientEquiv h a.e a.X).symm (n*coverInclusion g*n⁻¹) ∈ overlapCoreImage a := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  obtain ⟨b,hb⟩ := MulAut.automorphismTower_inner_of_isSimpleGroup m22_center_eq_bot
    (coreAmbientAutEquiv h a.e a.X)
  obtain ⟨u,_,hu⟩ := m22_pair_hexad_flag_conjugacy
    a.L.pair_card a.P.hexad_mem a.L.pair_le_hexad
  obtain ⟨n,hn⟩ := quotientConjugation_surjective (b*MulAut.conj u)
  refine ⟨n,fun g hg => ?_⟩
  let p : M22 := ⟨corePermutationAction g,corePermutationAction_range_eq_M22.le ⟨g,rfl⟩⟩
  let x := (coreAmbientEquiv h a.e a.X).symm (n*coverInclusion g*n⁻¹)
  have hx : coreAmbientHom h a.e a.X x=n*coverInclusion g*n⁻¹ :=
    (coreAmbientEquiv h a.e a.X).apply_symm_apply _
  have hp : a.e.projection x=MulAut.conj (u*p*u⁻¹) := by
    apply (MulAut.conj b).injective
    change b*a.e.projection x*b⁻¹=b*MulAut.conj (u*p*u⁻¹)*b⁻¹
    calc
      _ = coreAmbientAutEquiv h a.e a.X (a.e.projection x) :=
        MulEquiv.congr_fun hb _
      _ = quotientConjugation (coreAmbientHom h a.e a.X x) :=
        coreAmbientAutEquiv_projection h a.e a.X x
      _ = _ := by
        rw [hx,map_mul,map_mul,map_inv,hn,native_cover_projection]
        simp only [map_mul,map_inv]
        dsimp only [p]
        group
  change a.e.projection x ∈ designStabilizer a.P.hexad
  rw [hp]
  refine ⟨M22ValueBound.Concrete.inclusion (u*p*u⁻¹),?_,
    M22ValueBound.Concrete.designAutEquiv_inclusion _⟩
  change (u*p*u⁻¹) • a.P.hexad=a.P.hexad
  rw [←hu,mul_smul,mul_smul,inv_smul_smul]
  have hpg : p • m22Hexad123=m22Hexad123 := hg
  rw [hpg]

private theorem overlap_native_commutant (m : Matrix12ˣ)
    (hc : ∀ x : overlapCoreImage a, Commute m (coreAmbientHom h a.e a.X x.val).val) : m=1 := by
  obtain ⟨n,hn⟩ := overlap_native_hexad_marking a
  let u := n.val⁻¹*m*n.val
  have hu (g : M22TripleCover)
      (hg : m22Hexad123.image (corePermutationAction g)=m22Hexad123) : Commute u g.val := by
    have he := hc ⟨(coreAmbientEquiv h a.e a.X).symm (n*coverInclusion g*n⁻¹),hn g hg⟩
    change Commute m ((coreAmbientEquiv h a.e a.X)
      ((coreAmbientEquiv h a.e a.X).symm (n*coverInclusion g*n⁻¹))).val at he
    rw [MulEquiv.apply_symm_apply] at he
    have hh := he.map (MulAut.conj n.val⁻¹).toMonoidHom
    change Commute u (n.val⁻¹*(n.val*g.val*n.val⁻¹)*n.val) at hh
    have hhg : n.val⁻¹*(n.val*g.val*n.val⁻¹)*n.val=g.val := by group
    exact Eq.mp (congrArg (Commute u) hhg) hh
  have hne : overlapCoreEven a ≠ ⊤ := by
    intro he
    have hi := overlapCoreEven_index a
    rw [he,index_top] at hi
    contradiction
  obtain ⟨t,ht⟩ : ∃ t : overlapCoreImage a, t ∉ overlapCoreEven a := by
    by_contra hh
    exact hne (eq_top_iff.mpr fun t _ => by simpa using not_exists.mp hh t)
  let t₀ := coreAmbientHom h a.e a.X t.val
  have ht₀ : t₀ ∉ coverSubgroup := by
    intro hh
    apply ht
    exact (markedTripleAmbientHom_mem_cover_iff (coreBinaryRepresentation h)
      (innerPreimage a.e) (innerPreimageTripleEquiv h a.e) (coreNativeInnerEquiv h a.e a.X)
      (coreBinaryRepresentation_injective h) t.val).mp hh
  let t' : actionGroup := n⁻¹*t₀*n
  have ht' : t' ∉ coverSubgroup := by
    intro hh
    apply ht₀
    have hh' := Subgroup.Normal.conj_mem (inferInstance : coverSubgroup.Normal) t' hh n
    change n*(n⁻¹*t₀*n)*n⁻¹ ∈ coverSubgroup at hh'
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh'
  have hut : Commute u t'.val := by
    exact (hc t).map (MulAut.conj n.val⁻¹).toMonoidHom
  have hu1 := HexadCommutant.even_hexad_outer_commuting_units u hu t' ht' hut
  have hm1 : m=1 := by
    apply (MulAut.conj n.val⁻¹).injective
    exact hu1.trans (map_one (MulAut.conj n.val⁻¹)).symm
  exact hm1

/-- The centralizer of the full original overlap action on Q/Z(Q) is trivial.
The even preimage supplies only the three scalars; an actual outer overlap
actor eliminates the two nonidentity possibilities. -/
theorem overlap_section_commutant
    (f : MulAut (core z ⧸ center (core z)))
    (hf : ∀ x : PlaneOverlap a, Commute f (overlapSectionAction a x)) : f=1 := by
  let N := coreNativeEquiv h a.e a.X
  let F : CoreSpace (z := z) ≃ₗ[ZMod 2] CoreSpace (z := z) :=
    { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
  obtain ⟨m,hm⟩ := exists_matrix_implementing N F
  have hfc (x : overlapCoreImage a) : Commute f (coreQuotientAction h x.val) := by
    obtain ⟨y,rfl⟩ := overlapCoreProjection_surjective a x
    exact hf y
  have hc (x : overlapCoreImage a) : Commute m (coreAmbientHom h a.e a.X x.val).val := by
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨w,rfl⟩ := N.surjective v
    simp only [Units.val_mul,←Matrix.mulVec_mulVec]
    change (m : Matrix12)*ᵥ binaryAction (coreAmbientHom h a.e a.X x.val) (N w) =
      binaryAction (coreAmbientHom h a.e a.X x.val) ((m : Matrix12)*ᵥ N w)
    rw [←coreAmbientHom_intertwines,hm,hm,←coreAmbientHom_intertwines]
    apply congrArg N
    exact congrArg Additive.ofMul (MulEquiv.congr_fun (hfc x).eq w.toMul)
  have hm1 := overlap_native_commutant a m hc
  apply MulEquiv.ext
  intro v
  apply Additive.ofMul.injective
  apply N.injective
  have he := hm (Additive.ofMul v)
  rw [hm1,Units.val_one,Matrix.one_mulVec] at he
  exact he.symm

omit [IsExtraspecial 2 (core z)] in
/-- The full automorphism description of the literal point-plane overlap.
Both outer factors are the constructed restrictions of actual local twists. -/
theorem overlap_automorphism_factorization (f : MulAut (PlaneOverlap a)) :
    ∃ x : PlaneOverlap a,
      f=MulAut.conj x ∨
      f=MulAut.conj x*overlapPlaneTwist a ∨
      f=MulAut.conj x*planeOverlapToddTwist a (cubicFixedWord a) ∨
      f=MulAut.conj x*planeOverlapToddTwist a (cubicFixedWord a)*overlapPlaneTwist a := by
  let := h.extraspecial
  obtain ⟨x,b,_,_,hc,hk,he⟩ := overlap_automorphism_module_reduction a f
  have hb := hk (overlap_section_commutant a (overlapSectionAut a b) hc)
  refine ⟨x,?_⟩
  rcases hb with rfl | rfl <;> rcases he with he | he
  · exact Or.inl (by simpa only [mul_one] using he)
  · exact Or.inr (Or.inr (Or.inl (by simpa only [mul_one] using he)))
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inr he))

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
