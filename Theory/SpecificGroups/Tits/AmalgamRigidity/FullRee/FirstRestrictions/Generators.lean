module

public import Theory.SpecificGroups.ReeTwo.SylowPackedArithmetic
public import Theory.SpecificGroups.ReeTwo.Recognition

/-!
# Three explicit first-endpoint automorphisms

The ten core images, root-one image, and Weyl image satisfy the presentation
of the actual Ree two centralizer. The last root survives, so the existing
recognition theorem makes each resulting endomorphism an automorphism.
Evaluation on normal forms restricts these maps along the literal Sylow
embedding, with a pointwise commuting square.

The three image lists come from `FullRee/source/results.json`. Their Weyl
images are respectively w, w, and x₁₂w. All relations below are checked by
Lean's kernel; the discovery computation is not a proof premise.
Source: Shinoda (1975), pp.81–83; Parrott (1972), p.683. This is a finite
input to the full-Ree restriction argument for Aschbacher–Smith F.1.11–12.
-/

@[expose] public section
open ReeTwo
namespace Tits.AmalgamRigidity.FullRee.FirstRestrictions
abbrev E := Core ⋊[Core.complementAction] FiveFour.Group
noncomputable def equiv : E ≃* Centralizer :=
  SemidirectProduct.congr (MulEquiv.refl _) Core.complementEquiv (fun _ => rfl)

def fromS : SylowModel →* E :=
  SemidirectProduct.map (MonoidHom.id Core) SemidirectProduct.inr (fun _ => rfl)

theorem equiv_fromS (g : SylowModel) : equiv (fromS g) = SylowModel.embedding g := rfl

theorem normal_form (g : SylowModel) :
    Core.normalWord SylowModel.root (Core.coords g.left) *
      SylowModel.rootOne⁻¹ ^ g.right.toAdd.val = g := by
  have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form g.left)
  have hr : SylowModel.rootOne⁻¹ ^ g.right.toAdd.val = SemidirectProduct.inr g.right := by
    simp only [SylowModel.rootOne, ← map_inv, inv_inv, ← map_pow, FiveFour.generator_pow_val]
  rw [hr]
  have hh : Core.normalWord SylowModel.root (Core.coords g.left) = SemidirectProduct.inl g.left := by
    simpa [Core.normalWord, Core.coords, SylowModel.root] using hn
  rw [hh, SemidirectProduct.inl_left_mul_inr_right]

def wordMap (x : CoreRoot → SylowModel) (s : SylowModel) (g : SylowModel) : SylowModel :=
  Core.normalWord x (Core.coords g.left) * s⁻¹ ^ g.right.toAdd.val

section
variable (a : MulAut Centralizer) (x : CoreRoot → SylowModel) (s : SylowModel)
variable (hx : ∀ i, a (Centralizer.root i) = SylowModel.embedding (x i))
variable (hs : a Centralizer.rootOne = SylowModel.embedding s)
include hx hs

theorem wordMap_compatible (g : SylowModel) :
    a (SylowModel.embedding g) = SylowModel.embedding (wordMap x s g) := by
  conv_lhs => rw [← normal_form g]
  simp only [wordMap, map_mul, map_pow, map_inv, Core.normalWord,
    SylowModel.embedding_root, SylowModel.embedding_rootOne, hx, hs]

noncomputable def restrictionHom : SylowModel →* SylowModel where
  toFun := wordMap x s
  map_one' := by
    apply SylowModel.embedding_injective
    rw [← wordMap_compatible a x s hx hs]
    simp only [map_one]
  map_mul' g h := by
    apply SylowModel.embedding_injective
    rw [← wordMap_compatible a x s hx hs, map_mul, map_mul, map_mul,
      wordMap_compatible a x s hx hs, wordMap_compatible a x s hx hs]

noncomputable def restriction : MulAut SylowModel :=
  MulEquiv.ofBijective (restrictionHom a x s hx hs) (by
    apply (show Function.Injective (restrictionHom a x s hx hs) from ?_).bijective_of_finite
    intro g h he
    apply SylowModel.embedding_injective
    apply a.injective
    rw [wordMap_compatible a x s hx hs, wordMap_compatible a x s hx hs]
    exact congrArg SylowModel.embedding he)

theorem restriction_compatible (g : SylowModel) :
    a (SylowModel.embedding g) = SylowModel.embedding (restriction a x s hx hs g) :=
  wordMap_compatible a x s hx hs g

theorem restriction_root (i : CoreRoot) :
    restriction a x s hx hs (SylowModel.root i) = x i := by
  apply SylowModel.embedding_injective
  rw [← restriction_compatible, SylowModel.embedding_root, hx]

theorem restriction_rootOne :
    restriction a x s hx hs SylowModel.rootOne = s := by
  apply SylowModel.embedding_injective
  rw [← restriction_compatible, SylowModel.embedding_rootOne, hs]
end


/-- The three discovered core-image lists, in the existing collected numbering. -/
def coreCodes : Fin 3 → CoreRoot → Nat :=
  ![![1,2,4,8,16,32,64,128,256,512],
    ![1,2,516,8,16,32,64,128,256,512],
    ![65,610,4,904,144,32,64,128,256,512]]

def coreImage (k : Fin 3) (i : CoreRoot) : Core :=
  (SylowModel.Collected.decode (coreCodes k i)).left

def rootImage (k : Fin 3) (i : CoreRoot) : SylowModel :=
  SemidirectProduct.inl (coreImage k i)

def rootOneImage (k : Fin 3) : SylowModel :=
  SylowModel.Collected.decode (![3584,3456,3076] k)

def weylImage (k : Fin 3) : E :=
  ⟨if k = 2 then Core.root 9 else 1, FiveFour.r⟩

set_option maxRecDepth 8192 in
theorem coreImage_relations (k : Fin 3) : CoreRelations (coreImage k) where
  square := (by decide +kernel : ∀ (k : Fin 3) (i : CoreRoot),
      coreImage k i * coreImage k i = rootWord (coreImage k) (coreSquare i)) k
  commutator := (by decide +kernel : ∀ (k : Fin 3) (i j : CoreRoot), i < j →
      rightComm (coreImage k i) (coreImage k j) =
        rootWord (coreImage k) (coreCommutator i j)) k

set_option maxRecDepth 8192 in
theorem rootOneImage_relations (k : Fin 3) :
    RootOneRelations (fromS (rootOneImage k))
      (fun i => (SemidirectProduct.inl (coreImage k i) : E)) :=
  (by decide +kernel : ∀ (k : Fin 3) (i : CoreRoot),
    rightComm (fromS (rootOneImage k)) (SemidirectProduct.inl (coreImage k i)) =
      rootWord (fun j => (SemidirectProduct.inl (coreImage k j) : E)) (actionCorrection i)) k

set_option maxRecDepth 8192 in
theorem weylImage_relations (k : Fin 3) (i : CoreRoot) :
    weylImage k * SemidirectProduct.inl (coreImage k i) * (weylImage k)⁻¹ =
      SemidirectProduct.inl (coreImage k (weylRoot i)) := by
  let z : Core := if k = 2 then Core.root 9 else 1
  have hw : weylImage k = SemidirectProduct.inl z *
      SemidirectProduct.inr FiveFour.r :=
    (SemidirectProduct.inl_left_mul_inr_right (weylImage k)).symm
  have hr : (SemidirectProduct.inr FiveFour.r : E) *
      SemidirectProduct.inl (coreImage k i) * (SemidirectProduct.inr FiveFour.r)⁻¹ =
      SemidirectProduct.inl (Core.r (coreImage k i)) := by
    simpa only [Core.complementAction_r, map_inv] using
      (SemidirectProduct.inl_aut (φ := Core.complementAction) FiveFour.r (coreImage k i)).symm
  calc
    _ = SemidirectProduct.inl z * ((SemidirectProduct.inr FiveFour.r : E) *
        SemidirectProduct.inl (coreImage k i) * (SemidirectProduct.inr FiveFour.r)⁻¹) *
        (SemidirectProduct.inl z)⁻¹ := by rw [hw]; group
    _ = SemidirectProduct.inl (z * Core.r (coreImage k i) * z⁻¹) := by
      rw [hr, map_mul, map_mul, map_inv]
    _ = _ := congrArg SemidirectProduct.inl
      ((by decide +kernel : ∀ (k : Fin 3) (i : CoreRoot),
        (if k = 2 then Core.root 9 else 1) * Core.r (coreImage k i) *
          (if k = 2 then Core.root 9 else 1)⁻¹ = coreImage k (weylRoot i)) k i)

set_option maxRecDepth 8192 in
theorem five_relation (k : Fin 3) :
    ((fromS (rootOneImage k))⁻¹ ^ 2 * weylImage k) ^ 5 = 1 :=
  (by decide +kernel : ∀ k : Fin 3,
    ((fromS (rootOneImage k))⁻¹ ^ 2 * weylImage k) ^ 5 = 1) k

set_option maxRecDepth 8192 in
theorem four_relation (k : Fin 3) : ((fromS (rootOneImage k))⁻¹) ^ 4 = 1 :=
  (by decide +kernel : ∀ k : Fin 3, ((fromS (rootOneImage k))⁻¹) ^ 4 = 1) k

set_option maxRecDepth 8192 in
theorem action_relation (k : Fin 3) :
    (fromS (rootOneImage k))⁻¹ * ((fromS (rootOneImage k))⁻¹ ^ 2 * weylImage k) *
      ((fromS (rootOneImage k))⁻¹)⁻¹ =
        ((fromS (rootOneImage k))⁻¹ ^ 2 * weylImage k) ^ 2 :=
  (by decide +kernel : ∀ k : Fin 3,
    (fromS (rootOneImage k))⁻¹ * ((fromS (rootOneImage k))⁻¹ ^ 2 * weylImage k) *
      ((fromS (rootOneImage k))⁻¹)⁻¹ =
        ((fromS (rootOneImage k))⁻¹ ^ 2 * weylImage k) ^ 2) k

noncomputable def endpointHom (k : Fin 3) : Centralizer →* Centralizer :=
  equiv.toMonoidHom.comp (Centralizer.lift
    ((coreImage_relations k).map SemidirectProduct.inl)
    (rootOneImage_relations k) (weylImage_relations k)
    (five_relation k) (four_relation k) (action_relation k))

@[simp] theorem endpointHom_root (k : Fin 3) (i : CoreRoot) :
    endpointHom k (Centralizer.root i) = SylowModel.embedding (rootImage k i) := by
  simp only [endpointHom, MonoidHom.comp_apply, Centralizer.lift_root]
  rfl

@[simp] theorem endpointHom_rootOne (k : Fin 3) :
    endpointHom k Centralizer.rootOne = SylowModel.embedding (rootOneImage k) := by
  simp only [endpointHom, MonoidHom.comp_apply, Centralizer.lift_rootOne]
  rfl

/-- Actual automorphisms of the endpoint, obtained from its presentation. -/
noncomputable def endpointAutomorphism (k : Fin 3) : MulAut Centralizer :=
  MulEquiv.ofBijective (endpointHom k) (by
    apply (Centralizer.hom_injective_of_last_root (endpointHom k) ?_).bijective_of_finite
    rw [endpointHom_root]
    have hz : rootImage k 9 = SylowModel.root 9 :=
      (by decide +kernel : ∀ k : Fin 3, rootImage k 9 = SylowModel.root 9) k
    rw [hz, SylowModel.embedding_root]
    exact Centralizer.root_ne_one 9)

/-- Their restrictions are automorphisms of the genuine 4096-element overlap. -/
noncomputable def generator (k : Fin 3) : MulAut SylowModel :=
  restriction (endpointAutomorphism k) (rootImage k) (rootOneImage k)
    (endpointHom_root k) (endpointHom_rootOne k)

theorem generator_root (k : Fin 3) (i : CoreRoot) :
    generator k (SylowModel.root i) = rootImage k i :=
  restriction_root ..

theorem generator_rootOne (k : Fin 3) :
    generator k SylowModel.rootOne = rootOneImage k := restriction_rootOne ..

/-- The literal endpoint inclusion square, pointwise on every Sylow element. -/
theorem generator_compatible (k : Fin 3) (g : SylowModel) :
    endpointAutomorphism k (SylowModel.embedding g) =
      SylowModel.embedding (generator k g) := restriction_compatible ..

end Tits.AmalgamRigidity.FullRee.FirstRestrictions
