module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointComparison

/-!
# The full-word automorphisms of the split Todd group

The displacement w-gw of a full permutation-module word is even and defines
a cocycle in the eleven-dimensional cocode. Its automorphism of the split
Todd group factors through Full/Golay, fixes the embedded cocode pointwise,
and induces identity on M₂₄. Even classes give inner automorphisms. An odd
singleton gives an actual order-two automorphism, witnessed by a nonzero
pair-vector displacement under a native generator.

Transport through the original Todd marking preserves the same quotient,
marker and literal plane overlap. This constructs the beta family in
AS91 (8.2), pp.605–606. The full automorphism group of the overlap is not
asserted by these results.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open scoped BigOperators

/-- The literal twelve-dimensional extension of the even cocode. -/
abbrev FullCocode := Full ⧸ golay

noncomputable def fullCocodeRepresentation : Representation (ZMod 2) M24 FullCocode :=
  golaySubrepresentation.quotientRepresentation

theorem fullCocode_finrank : Module.finrank (ZMod 2) FullCocode = 12 := by
  have hd := golay.finrank_quotient_add_finrank
  rw [finrank_golay,BinaryPermutation.finrank_full] at hd
  change Module.finrank (ZMod 2) FullCocode + 12 = 24 at hd
  omega

/-- The even cocode is embedded by the original inclusion of the even core. -/
noncomputable def cocodeIntoFull : Cocode →ₗ[ZMod 2] FullCocode :=
  codeInCore.mapQ golay Core.subtype le_rfl

theorem cocodeIntoFull_mk (v : Core) :
    cocodeIntoFull (codeInCore.mkQ v) = golay.mkQ v.val := by rfl

theorem cocodeIntoFull_injective : Function.Injective cocodeIntoFull := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_bot_iff.mp
  intro x hx
  change x = 0
  obtain ⟨v,rfl⟩ := codeInCore.mkQ_surjective x
  change cocodeIntoFull (codeInCore.mkQ v) = 0 at hx
  rw [cocodeIntoFull_mk] at hx
  have hv : v.val ∈ golay := (Submodule.Quotient.mk_eq_zero golay).mp hx
  exact (Submodule.Quotient.mk_eq_zero codeInCore).mpr hv

theorem cocodeIntoFull_equivariant (g : M24) (v : Cocode) :
    cocodeIntoFull (cocodeRepresentation g v) = fullCocodeRepresentation g (cocodeIntoFull v) := by
  obtain ⟨w,rfl⟩ := codeInCore.mkQ_surjective v
  rfl

/-- Displacement of a word of the full permutation module, viewed in the even core. -/
private noncomputable def fullWordDisplacement (w : Full) (g : M24) : Core :=
  ⟨w - fullRepresentation g w, by
    change BinaryPermutation.augmentation (Fin 24) (w - fullRepresentation g w) = 0
    rw [map_sub]
    change BinaryPermutation.augmentation (Fin 24) w -
      BinaryPermutation.augmentation (Fin 24) (BinaryPermutation.representation (Fin 24) g.val w) = 0
    rw [BinaryPermutation.augmentation_permute,sub_self]⟩

/-- The connecting cocycle of Full/Golay over its even cocode submodule. -/
noncomputable def toddCocycle (w : Full) (g : M24) : Cocode :=
  codeInCore.mkQ (fullWordDisplacement w g)

/-- The cocycle is the class of the actual even displacement, without
exposing the private representative construction. -/
theorem toddCocycle_representative (w : Full) (g : M24) :
    ∃ v : Core, v.val = w - fullRepresentation g w ∧
      toddCocycle w g = codeInCore.mkQ v :=
  ⟨fullWordDisplacement w g, rfl, rfl⟩

/-- The cocycle is precisely the displacement in the twelve-dimensional extension. -/
theorem toddCocycle_intoFull (w : Full) (g : M24) :
    cocodeIntoFull (toddCocycle w g) =
      golay.mkQ w - fullCocodeRepresentation g (golay.mkQ w) := by
  change golay.mkQ (w-fullRepresentation g w) = golay.mkQ w-golay.mkQ (fullRepresentation g w)
  exact map_sub golay.mkQ w (fullRepresentation g w)

theorem toddCocycle_of_fixed_word (w : Full) (g : M24)
    (hg : fullRepresentation g w = w) : toddCocycle w g = 0 := by
  change codeInCore.mkQ (fullWordDisplacement w g) = 0
  rw [show fullWordDisplacement w g = 0 by
    apply Subtype.ext
    change w-fullRepresentation g w=0
    rw [hg,sub_self],map_zero]

theorem toddCocycle_one (w : Full) : toddCocycle w 1 = 0 := by
  change codeInCore.mkQ _ = _
  rw [show fullWordDisplacement w 1 = 0 by
    apply Subtype.ext
    change w - fullRepresentation 1 w = 0
    rw [map_one]
    exact sub_self w,map_zero]

theorem toddCocycle_mul (w : Full) (g k : M24) :
    toddCocycle w (g*k) = toddCocycle w g + cocodeRepresentation g (toddCocycle w k) := by
  change codeInCore.mkQ (fullWordDisplacement w (g*k)) =
    codeInCore.mkQ (fullWordDisplacement w g) +
      codeInCore.mkQ (coreRepresentation g (fullWordDisplacement w k))
  rw [← map_add]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  change w - fullRepresentation (g*k) w =
    (w - fullRepresentation g w) + fullRepresentation g (w-fullRepresentation k w)
  rw [map_mul,Module.End.mul_apply,map_sub]
  abel

/-- Changing a full word by a Golay codeword leaves the connecting cocycle unchanged. -/
theorem toddCocycle_add_golay (w v : Full) (hv : v ∈ golay) (g : M24) :
    toddCocycle (w+v) g = toddCocycle w g := by
  have he : fullWordDisplacement (w+v) g = fullWordDisplacement w g + fullWordDisplacement v g := by
    apply Subtype.ext
    change w+v-fullRepresentation g (w+v) =
      (w-fullRepresentation g w)+(v-fullRepresentation g v)
    rw [map_add]
    abel
  change codeInCore.mkQ _ = _
  rw [he,map_add]
  have hv0 : codeInCore.mkQ (fullWordDisplacement v g) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (golay.sub_mem hv (golay_invariant g hv))
  rw [hv0,add_zero]
  rfl

/-- For an even word the cocycle is the usual coboundary of its cocode class. -/
theorem toddCocycle_even (w : Core) (g : M24) :
    toddCocycle w.val g = codeInCore.mkQ w - cocodeRepresentation g (codeInCore.mkQ w) := by
  change codeInCore.mkQ (fullWordDisplacement w.val g) =
    codeInCore.mkQ w-codeInCore.mkQ (coreRepresentation g w)
  rw [← map_sub]
  rfl

private noncomputable def toddShear (w : Full) : ToddGroup →* ToddGroup where
  toFun x := ⟨x.left * Multiplicative.ofAdd (toddCocycle w x.right),x.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change (1 : ToddVector) * Multiplicative.ofAdd (toddCocycle w 1) = 1
      rw [toddCocycle_one]
      rfl
    · rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change (x.left * toddAction x.right y.left) * Multiplicative.ofAdd (toddCocycle w (x.right*y.right)) =
        (x.left * Multiplicative.ofAdd (toddCocycle w x.right)) *
          toddAction x.right (y.left * Multiplicative.ofAdd (toddCocycle w y.right))
      rw [map_mul]
      change Multiplicative.ofAdd (x.left.toAdd + cocodeRepresentation x.right y.left.toAdd +
        toddCocycle w (x.right*y.right)) =
          Multiplicative.ofAdd (x.left.toAdd + toddCocycle w x.right +
            (cocodeRepresentation x.right y.left.toAdd +
              cocodeRepresentation x.right (toddCocycle w y.right)))
      rw [toddCocycle_mul]
      congr 1
      abel
    · rfl

private theorem toddShear_involutive (w : Full) : Function.Involutive (toddShear w) := by
  intro x
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd ((x.left.toAdd + toddCocycle w x.right) + toddCocycle w x.right) = x.left
    have hc : toddCocycle w x.right + toddCocycle w x.right = 0 := by
      rw [← two_nsmul,← Nat.cast_smul_eq_nsmul (ZMod 2)]
      simp
    rw [add_assoc,hc,add_zero]
    rfl
  · rfl

/-- The automorphism of the actual split Todd group induced by a full-word class. -/
noncomputable def toddTwist (w : Full) : MulAut ToddGroup :=
  { toddShear w with
    invFun := toddShear w
    left_inv := toddShear_involutive w
    right_inv := toddShear_involutive w }

theorem toddTwist_apply (w : Full) (x : ToddGroup) :
    toddTwist w x = ⟨x.left * Multiplicative.ofAdd (toddCocycle w x.right),x.right⟩ := by rfl

theorem toddTwist_projection (w : Full) (x : ToddGroup) :
    (toddTwist w x).right = x.right := by rfl

theorem toddTwist_vector (w : Full) (v : ToddVector) :
    toddTwist w (SemidirectProduct.inl v) = SemidirectProduct.inl v := by
  rw [toddTwist_apply]
  apply SemidirectProduct.ext
  · change v * Multiplicative.ofAdd (toddCocycle w 1) = v
    rw [toddCocycle_one]
    exact mul_one v
  · rfl

theorem toddTwist_sq (w : Full) : toddTwist w ^ 2 = 1 := by
  apply MulEquiv.ext
  exact toddShear_involutive w

/-- The cocycle and automorphism depend on Full/Golay, as in the source. -/
theorem toddTwist_add_golay (w v : Full) (hv : v ∈ golay) : toddTwist (w+v) = toddTwist w := by
  apply MulEquiv.ext
  intro x
  rw [toddTwist_apply,toddTwist_apply,toddCocycle_add_golay w v hv]

/-- Even classes produce inner automorphisms by elements of the embedded cocode. -/
theorem toddTwist_even (w : Core) :
    toddTwist w.val = MulAut.conj
      (SemidirectProduct.inl (Multiplicative.ofAdd (codeInCore.mkQ w)) : ToddGroup) := by
  apply MulEquiv.ext
  intro x
  rw [toddTwist_apply]
  apply SemidirectProduct.ext
  · simp only [MulAut.conj_apply,SemidirectProduct.mul_left,SemidirectProduct.mul_right,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.inv_left,
      inv_one,map_one,MulAut.one_apply,one_mul]
    change Multiplicative.ofAdd (x.left.toAdd + toddCocycle w.val x.right) =
      Multiplicative.ofAdd ((codeInCore.mkQ w + x.left.toAdd) +
        cocodeRepresentation x.right (-codeInCore.mkQ w))
    rw [toddCocycle_even,map_neg]
    congr 1
    abel
  · change x.right = 1*x.right*1⁻¹
    simp

/-- A specified odd class in the full permutation-module quotient. -/
@[expose] def toddOddWord : Full := wordOfSet {1}

theorem toddOddWord_not_even : toddOddWord ∉ Core := by
  change ¬ (∑ i : Fin 24, if i ∈ ({1} : Finset (Fin 24)) then (1 : ZMod 2) else 0) = 0
  simp

theorem toddOddWord_not_golay : toddOddWord ∉ golay :=
  fun hw => toddOddWord_not_even (golay_le_core hw)

private theorem toddOddCocycle_generator :
    toddCocycle toddOddWord (⟨m24GeneratorA,m24GeneratorA_mem⟩ : M24) =
      pairVector ⟨{1,4},by decide⟩ := by
  change codeInCore.mkQ (fullWordDisplacement toddOddWord _) =
    codeInCore.mkQ ⟨wordOfSet {1,4},_⟩
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  change wordOfSet {1} - BinaryPermutation.representation (Fin 24) m24GeneratorA (wordOfSet {1}) =
    wordOfSet {1,4}
  ext i
  fin_cases i <;> decide +kernel

/-- The source odd-class automorphism is nonidentity on the actual Todd group. -/
theorem toddOddTwist_ne_one : toddTwist toddOddWord ≠ 1 := by
  intro he
  let g : M24 := ⟨m24GeneratorA,m24GeneratorA_mem⟩
  have hh := congrArg (fun a : MulAut ToddGroup => (a (SemidirectProduct.inr g)).left) he
  rw [toddTwist_apply] at hh
  change (1 : ToddVector)*Multiplicative.ofAdd (toddCocycle toddOddWord g) = 1 at hh
  rw [one_mul] at hh
  have hz : toddCocycle toddOddWord g = 0 := congrArg Multiplicative.toAdd hh
  rw [toddOddCocycle_generator] at hz
  exact pairVector_ne_zero _ hz

theorem toddOddTwist_order : orderOf (toddTwist toddOddWord) = 2 :=
  orderOf_eq_prime (toddTwist_sq toddOddWord) toddOddTwist_ne_one

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

/-- Transfer the same full-word automorphism through the original Todd marking. -/
noncomputable def pointTwist (w : Full) : MulAut a.P.M := MulAut.congr a.P.toddEquiv (toddTwist w)

theorem pointTwist_eq_congr (w : Full) :
    pointTwist a w = MulAut.congr a.P.toddEquiv (toddTwist w) := by rfl

theorem pointTwist_projection (w : Full) (m : a.P.M) :
    a.P.projection (pointTwist a w m) = a.P.projection m := by
  change (a.P.toddEquiv.symm (a.P.toddEquiv
    (toddTwist w (a.P.toddEquiv.symm m)))).right = (a.P.toddEquiv.symm m).right
  rw [a.P.toddEquiv.symm_apply_apply,toddTwist_projection]

theorem pointTwist_vector (w : Full) (v : ToddVector) :
    pointTwist a w (a.P.toddEquiv (SemidirectProduct.inl v)) =
      a.P.toddEquiv (SemidirectProduct.inl v) := by
  change a.P.toddEquiv (toddTwist w (a.P.toddEquiv.symm
    (a.P.toddEquiv (SemidirectProduct.inl v)))) = _
  rw [a.P.toddEquiv.symm_apply_apply,toddTwist_vector]

theorem pointTwist_marker (w : Full) :
    (pointTwist a w ⟨z,marker_mem_point a⟩ : G) = z := by
  have hz : (⟨z,marker_mem_point a⟩ : a.P.M) =
      a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd (sextetVector a.sextet))) :=
    Subtype.ext a.marker_vector.symm
  rw [hz,pointTwist_vector]
  exact a.marker_vector

theorem pointTwist_overlap (w : Full) :
    ((centralizer z).subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
      (centralizer z).subgroupOf a.P.M :=
  pointEquiv_overlap a a (pointTwist a w) (pointTwist_marker a w)

theorem pointTwist_sq (w : Full) : pointTwist a w ^ 2 = 1 := by
  change MulAut.congr a.P.toddEquiv (toddTwist w) ^ 2 = 1
  rw [← map_pow,toddTwist_sq,map_one]

theorem pointOddTwist_order : orderOf (pointTwist a toddOddWord) = 2 :=
  ((MulAut.congr a.P.toddEquiv).orderOf_eq _).trans toddOddTwist_order

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
