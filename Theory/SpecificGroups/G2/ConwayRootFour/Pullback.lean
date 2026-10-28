module

public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift

/-!
# Restricting the genuine Leech double cover

For a homomorphism into the actual central Leech quotient, the fiber product
has a surjective projection to its domain and a kernel isomorphic to the
actual central signs. If the homomorphism is injective, the other projection
embeds this pullback in the Leech isometry group. The marked square calculation
then proves that a section cannot exist above a marked involution.

This is the pullback step in the G₂(4) argument of Aschbacher–Smith I.2.2(5),
printed p.411. The embedding into the Conway quotient is an explicit input;
this module does not assert its existence or identify a root-four class.
-/

@[expose] public section

namespace Atlas.G2.ConwayRootFour
open Atlas.Lattices Atlas.Conway

variable {G : Type*} [Group G]

/-- The literal fiber product with the central Leech projection. -/
def pullback (f : G →* LeechCentralQuotient) : Subgroup (LeechIsometryGroup × G) :=
  (leechCentralProjection.comp (MonoidHom.fst _ _)).eqLocus
    (f.comp (MonoidHom.snd _ _))

/-- The projection to the group being covered. -/
def projection (f : G →* LeechCentralQuotient) : pullback f →* G :=
  (MonoidHom.snd _ _).comp (pullback f).subtype

/-- The map to the original Leech cover. -/
def toLeech (f : G →* LeechCentralQuotient) : pullback f →* LeechIsometryGroup :=
  (MonoidHom.fst _ _).comp (pullback f).subtype

theorem projection_compatible (f : G →* LeechCentralQuotient) (x : pullback f) :
    leechCentralProjection (toLeech f x) = f (projection f x) := x.property

theorem projection_surjective (f : G →* LeechCentralQuotient) :
    Function.Surjective (projection f) := by
  intro g
  obtain ⟨x, hx⟩ := leechCentralProjection_surjective (f g)
  exact ⟨⟨(x, g), hx⟩, rfl⟩

theorem toLeech_injective {f : G →* LeechCentralQuotient} (hf : Function.Injective f) :
    Function.Injective (toLeech f) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext h
  apply hf
  exact (projection_compatible f x).symm.trans
    ((congrArg leechCentralProjection h).trans (projection_compatible f y))

/-- The image is exactly the inverse image of the embedded subgroup. -/
theorem toLeech_range (f : G →* LeechCentralQuotient) :
    (toLeech f).range = f.range.comap leechCentralProjection := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨projection f y, (projection_compatible f y).symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨(x, g), hg.symm⟩, rfl⟩

/-- The quotient map is the literal pullback projection to the prescribed base. -/
noncomputable def quotientKernelEquiv (f : G →* LeechCentralQuotient) :
    pullback f ⧸ (projection f).ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective (projection f) (projection_surjective f)

theorem quotientKernelEquiv_mk (f : G →* LeechCentralQuotient) (x : pullback f) :
    quotientKernelEquiv f (QuotientGroup.mk' (projection f).ker x) = projection f x := rfl

/-- This is an isomorphism of the actual kernel, not a cardinality label. -/
def kernelEquivSigns (f : G →* LeechCentralQuotient) :
    (projection f).ker ≃* leechCentralSigns where
  toFun x := ⟨toLeech f x.val, by
    rw [← leechCentralProjection_kernel, MonoidHom.mem_ker,
      projection_compatible, show projection f x.val = 1 from x.property, map_one]⟩
  invFun z := ⟨⟨(z.val, 1), by
    change leechCentralProjection z.val = f 1
    rw [map_one]
    apply MonoidHom.mem_ker.mp
    rw [leechCentralProjection_kernel]
    exact z.property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  right_inv z := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

theorem kernel_card (f : G →* LeechCentralQuotient) : Nat.card (projection f).ker = 2 := by
  rw [Nat.card_congr (kernelEquivSigns f).toEquiv, leechCentralSigns_card]

theorem kernel_le_center (f : G →* LeechCentralQuotient) :
    (projection f).ker ≤ Subgroup.center (pullback f) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · have hz : toLeech f x ∈ Subgroup.center LeechIsometryGroup := by
      rw [← leechCentralSigns_eq_center]
      exact (kernelEquivSigns f ⟨x, hx⟩).property
    exact Subgroup.mem_center_iff.mp hz (toLeech f y)
  · change projection f y * projection f x = projection f x * projection f y
    rw [show projection f x = 1 from hx, mul_one, one_mul]

/-- The nonidentity sign as an element of the restricted cover. -/
noncomputable def centralSign (f : G →* LeechCentralQuotient) : pullback f :=
  ⟨(negationIsometry, 1), projection_negation.trans (map_one f).symm⟩

theorem centralSign_ne_one (f : G →* LeechCentralQuotient) : centralSign f ≠ 1 := by
  intro h
  exact negationIsometry_ne_one (congrArg (toLeech f) h)

theorem centralSign_mem_center (f : G →* LeechCentralQuotient) :
    centralSign f ∈ Subgroup.center (pullback f) := kernel_le_center f rfl

theorem lift_sq_of_marked (f : G →* LeechCentralQuotient) {g : G}
    (hg : g ^ 2 = 1) (hm : f g = markedInvolution)
    {x : pullback f} (hx : projection f x = g) : x ^ 2 = centralSign f := by
  apply Subtype.ext
  apply Prod.ext
  · exact lift_sq_of_projection_eq_marked ((projection_compatible f x).trans (hx ▸ hm))
  · change (projection f x) ^ 2 = 1
    rw [hx, hg]

theorem lift_order_of_marked {f : G →* LeechCentralQuotient}
    (hf : Function.Injective f) {g : G} (hm : f g = markedInvolution)
    {x : pullback f} (hx : projection f x = g) : orderOf x = 4 := by
  rw [← orderOf_injective (toLeech f) (toLeech_injective hf) x]
  exact lift_order_of_projection_eq_marked
    ((projection_compatible f x).trans (hx ▸ hm))

/-- A homomorphic section would send a base involution to an involution,
contradicting the concrete square of its Leech lift. -/
theorem no_section_of_marked (f : G →* LeechCentralQuotient) {g : G}
    (hg : g ^ 2 = 1) (hm : f g = markedInvolution) :
    ¬∃ s : G →* pullback f, (projection f).comp s = MonoidHom.id G := by
  rintro ⟨s, hs⟩
  have hx : projection f (s g) = g := congrArg (fun k : G →* G => k g) hs
  have hsq := lift_sq_of_marked f hg hm hx
  rw [← map_pow, hg, map_one] at hsq
  exact centralSign_ne_one f hsq.symm

end Atlas.G2.ConwayRootFour
