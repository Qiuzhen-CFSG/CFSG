module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.StemData

/-!
# The marked root preimage in a Suzuki central covering

Transfer places the covering kernel in the derived subgroup of the full root
preimage. The first root coordinate therefore identifies its abelianization
with the additive Suzuki field. Its third commutator lies in the central
covering kernel. Conjugation descends through that kernel, giving the actual
split torus action on the lifted root group, with its scalar coordinate law.

These are inputs to the ordinary Suzuki multiplier calculation, not a
splitting or a multiplier bound. Sources: Huppert--Blackburn III, XI.3.1;
Aschbacher--Smith I.1.1--I.1.3 and the transfer reduction in SchurCoverReduction.
-/

@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.SchurCover.Family
open Subgroup Theory.GroupTheory
open scoped commutatorElement

variable {E : Type*} [Group E] {m : ℕ}

/-- Full preimage of the standard root subgroup under the specified cover. -/
def rootPreimage (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) : Subgroup E :=
  (SuzukiRootSubgroup m).comap f.toMonoidHom

/-- The restriction of the actual covering map to its root preimage. -/
def rootProjection (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    rootPreimage f →* SuzukiRootSubgroup m :=
  (f.toMonoidHom.comp (rootPreimage f).subtype).codRestrict _ (fun x => x.property)

theorem rootProjection_surjective (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    Function.Surjective (rootProjection f) := by
  intro x
  obtain ⟨y,hy⟩ := f.surjective x
  refine ⟨⟨y,?_⟩,Subtype.ext hy⟩
  change f.toMonoidHom y ∈ SuzukiRootSubgroup m
  rw [hy]
  exact x.property

theorem rootProjection_ker (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    (rootProjection f).ker = f.toMonoidHom.ker.subgroupOf (rootPreimage f) := by
  ext x
  change (⟨f.toMonoidHom x, _⟩ : SuzukiRootSubgroup m) = 1 ↔ f.toMonoidHom x = 1
  exact Subtype.ext_iff

theorem rootProjection_ker_le_center
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    (rootProjection f).ker ≤ center (rootPreimage f) := by
  rw [rootProjection_ker]
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hx) y)

theorem rootProjection_ker_isTwoGroup [Finite E] (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    IsPGroup 2 (rootProjection f).ker := by
  rw [rootProjection_ker]
  exact (kernel_isTwoGroup hm f).of_equiv
    (subgroupOfEquivOfLe ((SuzukiRootSubgroup m).ker_le_comap f.toMonoidHom)).symm

/-- The stem condition for the literal restricted projection, by Sylow transfer. -/
theorem rootProjection_ker_le_commutator [Finite E] (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    (rootProjection f).ker ≤ _root_.commutator (rootPreimage f) := by
  rw [rootProjection_ker]
  intro x hx
  have h := kernel_le_rootPreimage_commutator hm f hx
  change (x : E) ∈ ⁅rootPreimage f, rootPreimage f⁆ at h
  rw [← map_subtype_commutator] at h
  obtain ⟨y,hy,he⟩ := h
  exact (Subtype.ext he : y = x) ▸ hy

/-- Transfer identifies the full preimage of the root center with the derived group. -/
theorem rootPreimage_commutator_eq [Finite E] (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    _root_.commutator (rootPreimage f) =
      (center (SuzukiRootSubgroup m)).comap (rootProjection f) := by
  have hi : (_root_.commutator (rootPreimage f)).map (rootProjection f) =
      center (SuzukiRootSubgroup m) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (rootProjection_surjective f)]
    exact root_commutator_eq_center m hm
  have h := comap_map_eq_self (rootProjection_ker_le_commutator hm f)
  rw [hi] at h
  exact h.symm

/-- The marked additive coordinate on the full lifted root group. -/
def liftedCoordinate (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    rootPreimage f →* Multiplicative (Field m) :=
  (rootCoordinate m hm).comp (rootProjection f)

theorem liftedCoordinate_surjective (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    Function.Surjective (liftedCoordinate hm f) :=
  (rootCoordinate_surjective m hm).comp (rootProjection_surjective f)

theorem liftedCoordinate_ker [Finite E] (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    (liftedCoordinate hm f).ker = _root_.commutator (rootPreimage f) := by
  rw [liftedCoordinate, ← MonoidHom.comap_ker, rootCoordinate_ker,
    root_commutator_eq_center m hm, rootPreimage_commutator_eq hm f]

/-- All third commutators lie in the actual central covering kernel. -/
theorem third_commutator_le_kernel [Finite E] (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    ⁅_root_.commutator (rootPreimage f), (⊤ : Subgroup (rootPreimage f))⁆ ≤
      (rootProjection f).ker := by
  apply Subgroup.commutator_le.mpr
  intro x hx y _
  have hx' : rootProjection f x ∈ center (SuzukiRootSubgroup m) := by
    rw [rootPreimage_commutator_eq hm f] at hx
    exact hx
  change rootProjection f ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp hx' (rootProjection f y)).symm

/-- Conjugation on a central covering descends to its base group. -/
def baseConjugation (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    SuzukiMatrixGroup m →* MulAut E :=
  f.toMonoidHom.liftOfSurjective f.surjective ⟨MulAut.conj, by
    intro x hx
    change MulAut.conj x = 1
    ext y
    change x*y*x⁻¹ = y
    rw [← mem_center_iff.mp (f.ker_le_center hx) y, mul_inv_cancel_right]⟩

theorem baseConjugation_image (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (x : E) : baseConjugation f (f.toMonoidHom x) = MulAut.conj x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem baseConjugation_projection
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (g : SuzukiMatrixGroup m) (x : E) :
    f.toMonoidHom (baseConjugation f g x) = g * f.toMonoidHom x * g⁻¹ := by
  obtain ⟨y,rfl⟩ := f.surjective g
  rw [baseConjugation_image]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem baseConjugation_kernel
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (g : SuzukiMatrixGroup m) (x : E) (hx : x ∈ f.toMonoidHom.ker) :
    baseConjugation f g x = x := by
  obtain ⟨y,rfl⟩ := f.surjective g
  rw [baseConjugation_image]
  change y*x*y⁻¹ = x
  rw [mem_center_iff.mp (f.ker_le_center hx) y, mul_inv_cancel_right]

private theorem torus_preserves_rootPreimage (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (t : (Field m)ˣ) (x : rootPreimage f) :
    baseConjugation f (torusPoint m hm t) x ∈ rootPreimage f := by
  change f.toMonoidHom (baseConjugation f (torusPoint m hm t) x) ∈ SuzukiRootSubgroup m
  rw [baseConjugation_projection]
  exact (mem_normalizer_iff.mp
    (suzukiSplitTorus_le_normalizer_root m (torusPoint_mem m hm t)) _).mp x.property

/-- The full units group acts on the lifted root group, by actual lifted conjugation. -/
def torusAction (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    (Field m)ˣ →* MulAut (rootPreimage f) where
  toFun t := {
    toFun x := ⟨baseConjugation f (torusPoint m hm t) x,
      by exact torus_preserves_rootPreimage hm f t x⟩
    invFun x := ⟨baseConjugation f (torusPoint m hm t⁻¹) x,
      by exact torus_preserves_rootPreimage hm f t⁻¹ x⟩
    left_inv x := by
      apply Subtype.ext
      change ((baseConjugation f (torusPoint m hm t⁻¹)) *
        (baseConjugation f (torusPoint m hm t))) x = x
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
      rfl
    right_inv x := by
      apply Subtype.ext
      change ((baseConjugation f (torusPoint m hm t)) *
        (baseConjugation f (torusPoint m hm t⁻¹))) x = x
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      rfl
    map_mul' x y := Subtype.ext (map_mul _ _ _) }
  map_one' := by ext x; change baseConjugation f (torusPoint m hm 1) x = x; simp
  map_mul' t s := by
    ext x
    change baseConjugation f (torusPoint m hm (t*s)) x =
      baseConjugation f (torusPoint m hm t) (baseConjugation f (torusPoint m hm s) x)
    rw [map_mul, map_mul]
    rfl

theorem torusAction_fixes_kernel (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (t : (Field m)ˣ) (x : rootPreimage f) (hx : x ∈ (rootProjection f).ker) :
    torusAction hm f t x = x := by
  apply Subtype.ext
  exact baseConjugation_kernel f _ _ (show f.toMonoidHom (x : E) = 1 from
    congrArg Subtype.val hx)

/-- The induced action on the marked abelianization is multiplication by t. -/
theorem liftedCoordinate_torusAction (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (t : (Field m)ˣ) (x : rootPreimage f) :
    liftedCoordinate hm f (torusAction hm f t x) =
      Multiplicative.ofAdd ((t : Field m) * (liftedCoordinate hm f x).toAdd) := by
  obtain ⟨a,b,h⟩ := rootPoint_surjective m (rootProjection f x)
  have hp : rootProjection f (torusAction hm f t x) =
      rootPoint m (t*a) (t*suzukiTits m t*b) := by
    apply Subtype.ext
    change f.toMonoidHom (baseConjugation f (torusPoint m hm t) x) = _
    rw [baseConjugation_projection, show f.toMonoidHom (x : E) = (rootPoint m a b).val from
      congrArg Subtype.val h]
    exact torusPoint_conj m hm t a b
  change rootCoordinate m hm (rootProjection f (torusAction hm f t x)) =
    Multiplicative.ofAdd ((t : Field m) * (rootCoordinate m hm (rootProjection f x)).toAdd)
  rw [hp, h, rootCoordinate_rootPoint, rootCoordinate_rootPoint]
  rfl

/-- Triviality on the restricted projection is exactly enough for global vanishing. -/
theorem kernel_eq_bot_of_rootProjection_ker (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (h : (rootProjection f).ker = ⊥) : f.toMonoidHom.ker = ⊥ := by
  apply bot_unique
  intro x hx
  have hxR : x ∈ rootPreimage f := (SuzukiRootSubgroup m).ker_le_comap f.toMonoidHom hx
  have hxK : (⟨x,hxR⟩ : rootPreimage f) ∈ (rootProjection f).ker := Subtype.ext hx
  rw [h] at hxK
  exact congrArg Subtype.val (mem_bot.mp hxK)

/-- All scalar stem data on the literal root preimage, without any splitting premise. -/
def rootData [Finite E] (hm : 0 < m)
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    ScalarInvariantMaps.StemData (Field m) (rootPreimage f) where
  coordinate := liftedCoordinate hm f
  coordinate_surjective := liftedCoordinate_surjective hm f
  coordinate_ker := liftedCoordinate_ker hm f
  action := torusAction hm f
  coordinate_action := liftedCoordinate_torusAction hm f
  kernel := (rootProjection f).ker
  kernel_le_center := rootProjection_ker_le_center f
  kernel_le_commutator := rootProjection_ker_le_commutator hm f
  kernel_isTwoGroup := rootProjection_ker_isTwoGroup hm f
  third_le_kernel := third_commutator_le_kernel hm f
  action_kernel := torusAction_fixes_kernel hm f

/-- Apply the local construction to the constructed canonical universal covering. -/
def canonicalRootData (m : ℕ) [hm : Fact (0 < m)] :
    ScalarInvariantMaps.StemData (Field m)
      (rootPreimage (PerfectCentralCovering.universalCover (SuzukiMatrixGroup m))) :=
  rootData hm.out (PerfectCentralCovering.universalCover (SuzukiMatrixGroup m))

/-- The kernel in the marked canonical local data detects the full Schur kernel. -/
theorem canonicalKernel_eq_bot_of_local (m : ℕ) [Fact (0 < m)]
    (h : (canonicalRootData m).kernel = ⊥) : Kernel m = ⊥ :=
  kernel_eq_bot_of_rootProjection_ker
    (PerfectCentralCovering.universalCover (SuzukiMatrixGroup m)) h

end BenderSuzuki.MatrixGroups.SchurCover.Family
end
