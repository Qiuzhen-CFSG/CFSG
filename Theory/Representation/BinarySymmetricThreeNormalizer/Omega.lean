module
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega

/-!
# Natural Ω coordinates for a normal symmetric-three four-space

A fully moved S3 action is the tensor of its natural binary plane with the
inverter-fixed multiplicity space. In dimension four the multiplicity space is
another binary plane. Cubic rotation and inversion act on the first plane;
the centralizer acts diagonally on the multiplicity plane. Explicit determinant
coordinates identify these operations with isometries preserving a ruling of
the standard plus-four form, hence with elements of the actual Siegel-generated
Ω. A normal S3 splits off its centralizer, so order36 makes this embedding onto.

The support-image consumer preserves the original invariant action maps. A
fixed supplement proves faithfulness of the marked S3 after restricting to its
support, and proves full movement there without a ratio-preservation premise.

Source: Aschbacher--Smith 15.1.2, printed p.1085, natural action in case (6).
-/

public noncomputable section
open Subgroup InvertedCubicTensor
namespace Representation.BinarySymmetricThreeNormalizer
open OrthogonalFourBinary

private def splitCoordinates : Space ≃ₗ[ZMod 2] Space where
  toFun z := ((z.1.1 + z.2.2 + z.2.1, z.1.2 + z.2.1),
    (z.1.1 + z.2.2, z.1.2 + z.2.2 + z.2.1))
  invFun z := ((z.1.2 + z.2.1 + z.2.2, z.1.1 + z.1.2 + z.2.1),
    (z.1.1 + z.2.1, z.1.2 + z.2.2))
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' x y := by ext <;> simp [add_left_comm, add_comm]
  map_smul' a x := by ext <;> simp [mul_add]

private def cubicPair : Space ≃ₗ[ZMod 2] Space where
  toFun z := (z.2,z.1+z.2)
  invFun z := (z.1+z.2,z.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' x y := by ext <;> simp [add_left_comm, add_comm]
  map_smul' a x := by ext <;> simp
private def inverterPair : Space ≃ₗ[ZMod 2] Space where
  toFun z := (z.1+z.2,z.2)
  invFun z := (z.1+z.2,z.2)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' x y := by ext <;> simp [add_left_comm, add_comm]
  map_smul' a x := by ext <;> simp
private def leftPlane (p : S₃) : Plane ≃ₗ[ZMod 2] Plane :=
  ((LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).symm.trans (BinaryFourPlus.planeLinear p)).trans
    (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
private def planeEval (p : S₃) (x : Plane) : Plane :=
  let v : Fin 3 → Plane := ![(1,0),(0,1),(1,1)]
  if x.1 = 0 then if x.2 = 0 then 0 else v (p 1)
  else if x.2 = 0 then v (p 0) else v (p 2)
private theorem leftPlane_eval (p : S₃) (x : Plane) : leftPlane p x = planeEval p x := by
  have hc : ∀ x : Plane, x = 0 ∨ x = (1,0) ∨ x = (0,1) ∨ x = (1,1) := by decide +kernel
  have hn : ∀ i : Fin 3, (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
      (BinaryFourPlus.nonzeroVector i) = (![(1,0),(0,1),(1,1)] : Fin 3 → Plane) i := by decide +kernel
  rcases hc x with rfl | rfl | rfl | rfl
  · rw [map_zero]; rfl
  · change (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
      (BinaryFourPlus.planeLinear p (BinaryFourPlus.nonzeroVector 0)) = _
    rw [BinaryFourPlus.planeLinear_nonzeroVector]
    simpa [planeEval] using hn (p 0)
  · change (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
      (BinaryFourPlus.planeLinear p (BinaryFourPlus.nonzeroVector 1)) = _
    rw [BinaryFourPlus.planeLinear_nonzeroVector]
    simpa [planeEval] using hn (p 1)
  · change (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
      (BinaryFourPlus.planeLinear p (BinaryFourPlus.nonzeroVector 2)) = _
    rw [BinaryFourPlus.planeLinear_nonzeroVector]
    simpa [planeEval] using hn (p 2)
private def leftPair (p : S₃) : Space ≃ₗ[ZMod 2] Space :=
  (leftPlane p).prodCongr (leftPlane p)
private def coordinateAut (a : Space ≃ₗ[ZMod 2] Space) : Space ≃ₗ[ZMod 2] Space :=
  (splitCoordinates.symm.trans a).trans splitCoordinates
private theorem model_preserves :
    (∀ x, form (coordinateAut cubicPair x) = form x) ∧
    (∀ x, form (coordinateAut inverterPair x) = form x) ∧
    (∀ p x, form (coordinateAut (leftPair p) x) = form x) := by
  simp only [coordinateAut, LinearEquiv.trans_apply, leftPair, LinearEquiv.prodCongr_apply, leftPlane_eval]
  decide +kernel
private def cubicIsometry : TerminalLines.IsometryGroup :=
  ⟨coordinateAut cubicPair, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form _).mpr model_preserves.1⟩
private def inverterIsometry : TerminalLines.IsometryGroup :=
  ⟨coordinateAut inverterPair, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form _).mpr model_preserves.2.1⟩
private def leftIsometry (p : S₃) : TerminalLines.IsometryGroup :=
  ⟨coordinateAut (leftPair p), (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form _).mpr (model_preserves.2.2 p)⟩
private theorem model_omega :
    cubicIsometry ∈ omega ∧ inverterIsometry ∈ omega ∧ ∀ p, leftIsometry p ∈ omega := by
  rw [SylowGeometry.omega_eq_ruling]
  change (∀ a b, SylowGeometry.rulingPair (coordinateAut cubicPair a)
    (coordinateAut cubicPair b) ↔ SylowGeometry.rulingPair a b) ∧
    (∀ a b, SylowGeometry.rulingPair (coordinateAut inverterPair a)
    (coordinateAut inverterPair b) ↔ SylowGeometry.rulingPair a b) ∧
    (∀ p a b, SylowGeometry.rulingPair (coordinateAut (leftPair p) a)
    (coordinateAut (leftPair p) b) ↔ SylowGeometry.rulingPair a b)
  simp only [coordinateAut, LinearEquiv.trans_apply, leftPair, LinearEquiv.prodCongr_apply, leftPlane_eval]
  decide +kernel

private theorem binary_double {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (v : W) :
    v + v = 0 := by
  simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
    (add_smul (1 : ZMod 2) 1 v).symm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
private theorem square_formula (σ : Representation (ZMod 2) S₃ V)
    (h : ∀ v, σ cubic v = v → v = 0) (v : V) :
    σ cubic (σ cubic v) = v + σ cubic v := by
  have h3 : σ cubic (σ cubic (σ cubic v)) = v := by
    change (σ cubic * σ cubic * σ cubic) v = v
    rw [←map_mul,←map_mul,cubic_cube,map_one,Module.End.one_apply]
  have hn : v + σ cubic v + σ cubic (σ cubic v) = 0 := by
    apply h
    simp only [map_add,h3]
    abel
  have he := congrArg (fun x => x + σ cubic (σ cubic v)) hn
  simpa only [add_assoc,binary_double,add_zero,zero_add] using he.symm

private theorem pair_cubic (σ : Representation (ZMod 2) S₃ V)
    (h : ∀ v, σ cubic v = v → v = 0) (a b : multiplicitySpace σ) :
    σ cubic (pairEquiv σ h (a,b)) = pairEquiv σ h (b,a+b) := by
  rw [pairEquiv_apply,pairEquiv_apply,map_add,square_formula σ h]
  simp only [Submodule.coe_add,map_add]
  abel

private theorem pair_inverter (σ : Representation (ZMod 2) S₃ V)
    (h : ∀ v, σ cubic v = v → v = 0) (a b : multiplicitySpace σ) :
    σ inverter (pairEquiv σ h (a,b)) = pairEquiv σ h (a+b,b) := by
  have hb : σ inverter (σ cubic (b : V)) = σ cubic (σ cubic (b : V)) := by
    have he := inverts_cubic
    have hv := congrArg (fun g => σ g (b : V)) he
    simpa only [map_mul,Module.End.mul_apply,
      (mem_multiplicitySpace σ _).mp b.property] using hv
  rw [pairEquiv_apply,pairEquiv_apply,map_add,
    (mem_multiplicitySpace σ _).mp a.property,hb,square_formula σ h]
  simp only [Submodule.coe_add]
  abel

private theorem symmetricThree_words (g : S₃) :
    g = 1 ∨ g = cubic ∨ g = cubic*cubic ∨ g = inverter ∨
      g = cubic*inverter ∨ g = cubic*cubic*inverter := by
  revert g
  decide +kernel

variable {G : Type*} [Group G] [FiniteDimensional (ZMod 2) V]
/-- A faithful four-space with a normal, fully moved S3 and total group order36
is the actual natural action of genuine Ω4+(2). -/
theorem exists_omega_coordinates (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) [H.Normal] (j : H ≃* S₃)
    (hm : BinaryOffender.subspaceCommutator (ρ.comp H.subtype) ⊤ ⊤ = ⊤)
    (hcard : Nat.card G = 36) :
    ∃ (c : V ≃ₗ[ZMod 2] Space) (e : G ≃* omega),
      ∀ g v, c (ρ g v) = (e g).val.val (c v) := by
  let σ := ρ.comp (H.subtype.comp j.symm.toMonoidHom)
  let κ := ρ.comp (centralizer (H : Set G)).subtype
  have hc (g : centralizer (H : Set G)) (k : S₃) (v : V) :
      κ g (σ k v) = σ k (κ g v) := by
    change ρ (g:G) (ρ (j.symm k : G) v) = ρ (j.symm k : G) (ρ (g:G) v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun a => ρ a v) ((g.property _ (j.symm k).property).symm)
  have hfull : BinaryOffender.subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    change BinaryOffender.subspaceCommutator ((ρ.comp H.subtype).comp j.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [BinaryOffender.subspaceCommutator_comp_map,
      Subgroup.map_top_of_surjective _ j.symm.surjective]
    exact hm
  have hfree := fixedFree_of_full σ hfull
  have hn : Module.finrank (ZMod 2) (multiplicitySpace σ) = 2 := by
    have he := multiplicity_finrank σ hfree
    change 2 * Module.finrank (ZMod 2) (multiplicitySpace σ) = Module.finrank (ZMod 2) V at he
    omega
  let b₀ : multiplicitySpace σ ≃ₗ[ZMod 2] BinaryFourPlus.Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) _ hn).equivFun
  let b : multiplicitySpace σ ≃ₗ[ZMod 2] Plane :=
    b₀.trans (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
  let E := pairEquiv σ hfree
  let c : V ≃ₗ[ZMod 2] Space := (E.symm.trans (b.prodCongr b)).trans splitCoordinates
  let A : G →* (Space ≃ₗ[ZMod 2] Space) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).toMonoidHom.comp ρ.asGroupHom)
  have hA (g : G) (v : V) : A g (c v) = c (ρ g v) := by
    change c (ρ g (c.symm (c v))) = _
    rw [c.symm_apply_apply]
  have hcp (a b' : multiplicitySpace σ) : c (E (a,b')) = splitCoordinates (b a,b b') := by
    simp only [c,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
  have hR : A (j.symm cubic : G) = coordinateAut cubicPair := by
    apply LinearEquiv.ext
    intro z
    obtain ⟨v,rfl⟩ := c.surjective z
    obtain ⟨⟨a,b'⟩,rfl⟩ := E.surjective v
    rw [hA]
    change c (σ cubic (E (a,b'))) = _
    rw [pair_cubic σ hfree,hcp,hcp]
    simp only [coordinateAut,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
      cubicPair,map_add]
    rfl
  have hT : A (j.symm inverter : G) = coordinateAut inverterPair := by
    apply LinearEquiv.ext
    intro z
    obtain ⟨v,rfl⟩ := c.surjective z
    obtain ⟨⟨a,b'⟩,rfl⟩ := E.surjective v
    rw [hA]
    change c (σ inverter (E (a,b'))) = _
    rw [pair_inverter σ hfree,hcp,hcp]
    simp only [coordinateAut,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
      inverterPair,map_add]
    rfl
  let K : Subgroup (Space ≃ₗ[ZMod 2] Space) := omega.map TerminalLines.IsometryGroup.subtype
  have hRK : A (j.symm cubic : G) ∈ K := by
    rw [hR]
    exact ⟨cubicIsometry,model_omega.1,rfl⟩
  have hTK : A (j.symm inverter : G) ∈ K := by
    rw [hT]
    exact ⟨inverterIsometry,model_omega.2.1,rfl⟩
  have hHK : H ≤ K.comap A := by
    intro g hg
    let k := j ⟨g,hg⟩
    have he : (j.symm k : G) = g := congrArg Subtype.val (j.symm_apply_apply ⟨g,hg⟩)
    change A g ∈ K
    rw [←he]
    rcases symmetricThree_words k with hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    · simp only [map_one,coe_one]; exact K.one_mem
    · exact hRK
    · simpa only [map_mul,coe_mul] using K.mul_mem hRK hRK
    · exact hTK
    · simpa only [map_mul,coe_mul] using K.mul_mem hRK hTK
    · simpa only [map_mul,coe_mul] using K.mul_mem (K.mul_mem hRK hRK) hTK
  have hCK : centralizer (H : Set G) ≤ K.comap A := by
    intro g hg
    let k : centralizer (H : Set G) := ⟨g,hg⟩
    let μ := multiplicity σ κ hc
    let α : BinaryFourPlus.Plane ≃ₗ[ZMod 2] BinaryFourPlus.Plane :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryFourPlus.Plane
        (LinearMap.GeneralLinearGroup.congrLinearEquiv b₀ (μ.asGroupHom k))
    let p := BinaryFourPlus.planeAutEquiv α
    have hp (i : multiplicitySpace σ) : leftPlane p (b i) = b (μ k i) := by
      simp only [leftPlane,b,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
      change (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
        (BinaryFourPlus.planeLinear (BinaryFourPlus.planeAutPerm α) (b₀ i)) = _
      rw [BinaryFourPlus.planeLinear_planeAutPerm]
      change (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
        (b₀ (μ k (b₀.symm (b₀ i)))) = _
      rw [b₀.symm_apply_apply]
    have he : A g = coordinateAut (leftPair p) := by
      apply LinearEquiv.ext
      intro z
      obtain ⟨v,rfl⟩ := c.surjective z
      obtain ⟨⟨a,b'⟩,rfl⟩ := E.surjective v
      rw [hA]
      change c (κ k (E (a,b'))) = _
      rw [←pairEquiv_equivariant σ κ hc hfree,hcp,hcp]
      simp only [coordinateAut,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
      change splitCoordinates (b (μ k a),b (μ k b')) =
        splitCoordinates (leftPlane p (b a),leftPlane p (b b'))
      rw [hp,hp]
    change A g ∈ K
    rw [he]
    exact ⟨leftIsometry p,model_omega.2.2 p,rfl⟩
  have hall (g : G) : A g ∈ K := by
    have ht : (⊤ : Subgroup G) ≤ K.comap A := by
      rw [←Theory.GroupTheory.NormalSymmetricThree.sup_centralizer_eq_top H j]
      exact sup_le hHK hCK
    exact ht (mem_top g)
  have hall' (g : G) : ∃ a : omega, a.val.val = A g := by
    obtain ⟨a,ha,he⟩ := hall g
    exact ⟨⟨a,ha⟩,he⟩
  let f : G →* omega := {
    toFun := fun g => (hall' g).choose
    map_one' := by
      apply Subtype.ext
      apply Subtype.ext
      exact (hall' 1).choose_spec.trans A.map_one
    map_mul' g k := by
      apply Subtype.ext
      apply Subtype.ext
      change (hall' (g*k)).choose.val.val = (hall' g).choose.val.val * (hall' k).choose.val.val
      rw [(hall' g).choose_spec,(hall' k).choose_spec]
      exact (hall' (g*k)).choose_spec.trans (A.map_mul g k) }
  have hfA : Function.Injective A := by
    intro g k he
    apply hf
    ext v
    apply c.injective
    rw [←hA,←hA,he]
  have hff : Function.Injective f := by
    intro g k he
    apply hfA
    exact (hall' g).choose_spec.symm.trans
      ((congrArg (fun a : omega => a.val.val) he).trans (hall' k).choose_spec)
  have hb : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hff,hcard.trans SylowGeometry.omega_card.symm⟩
  refine ⟨c,MulEquiv.ofBijective f hb,?_⟩
  intro g v
  rw [←hA]
  exact congrArg (fun a : Space ≃ₗ[ZMod 2] Space => a (c v))
    (hall' g).choose_spec.symm

/-- The natural Ω coordinates on the literal action image of the marked
S3 support. Only this support, rather than the whole module, is four-dimensional. -/
theorem support_exists_omega_coordinates
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (j : H ≃* S₃)
    (W : Submodule (ZMod 2) V)
    (hW : (⊤ : Subgroup G) ≤ BinaryOffender.subspaceStabilizer ρ W)
    (hmoved : BinaryOffender.subspaceCommutator ρ ⊤ H = W)
    (hsup : W ⊔ BinaryOffender.fixedSpace ρ H = ⊤)
    (h4 : Module.finrank (ZMod 2) W = 4)
    (hcard : Nat.card (BinaryOffender.subspaceActionImage ρ W) = 36) :
    ∃ (c : W ≃ₗ[ZMod 2] Space)
      (e : BinaryOffender.subspaceActionImage ρ W ≃* omega),
      ∀ g v, c (BinaryOffender.subspaceImageRepresentation ρ W g v) =
        (e g).val.val (c v) := by
  let q := BinaryOffender.invariantActionHom ρ W hW
  let H' := H.map q
  let τ := BinaryOffender.subspaceImageRepresentation ρ W
  have hq : Function.Surjective q := BinaryOffender.invariantActionHom_surjective ρ W hW
  let : H'.Normal := Subgroup.Normal.map inferInstance q hq
  let qH := q.comp H.subtype
  have hqH : Function.Injective qH := by
    intro a b hab
    apply Subtype.ext
    apply hf
    ext v
    obtain ⟨w,hw,y,hy,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ BinaryOffender.fixedSpace ρ H from hsup ▸ Submodule.mem_top)
    have he := congrArg (fun g => (τ g ⟨w,hw⟩ : V)) hab
    change ρ (a:G) w = ρ (b:G) w at he
    change ∀ h : H, ρ (h:G) y = y at hy
    simp only [map_add,hy a,hy b,he]
  have hr : qH.range = H' := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  let k : H ≃* H' := (MonoidHom.ofInjective hqH).trans (MulEquiv.subgroupCongr hr)
  have hself : BinaryOffender.subspaceCommutator ρ W H = W := by
    apply le_antisymm
      (BinaryOffender.subspaceCommutator_le_of_invariant ρ (le_top.trans hW))
    apply hmoved.symm.le.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    obtain ⟨w,hw,y,hy,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ BinaryOffender.fixedSpace ρ H from hsup ▸ Submodule.mem_top)
    have he : ρ a y = y := hy ⟨a,ha⟩
    simp only [map_add,he,add_sub_add_right_eq_sub]
    exact Submodule.subset_span ⟨a,ha,w,hw,rfl⟩
  have hfull : BinaryOffender.subspaceCommutator (τ.comp H'.subtype) ⊤ ⊤ = ⊤ := by
    rw [BinaryOffender.subspaceCommutator_comp_map,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    have he := BinaryOffender.restricted_commutator_eq_top ρ W H (le_top.trans hW) hself
    rw [←BinaryOffender.invariantActionHom_map ρ W hW H] at he
    exact he
  exact exists_omega_coordinates τ
    (BinaryOffender.subspaceImageRepresentation_injective ρ W) h4 H'
    (k.symm.trans j) hfull hcard

end Representation.BinarySymmetricThreeNormalizer
