module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient

/-!
# Constructing a G₂(4) cover from marked Conway geometry

Pull back the actual Leech projection Co₀ → Co₁ along an embedding of the
split-octonion G₂(4) model. Its kernel is exactly the two central signs.
A marked isometry whose square is the nonidentity sign gives an order-four
element in the pullback. The square obstruction proves perfectness, hence
quasisimplicity, and the literal second projection identifies its central
quotient with the original G₂(4). Its nontrivial kernel also detects the
nontriviality of the canonical universal kernel.

The embedding and marked isometry remain explicit geometric inputs. This
module proves the cover construction from those inputs, not their existence.
The independent Conway geometry must supply them before the unconditional
I.1.3(1) multiplier row can be assembled. No multiplier bound is used here.

Source: Aschbacher–Smith, I.1.3(1) and the G₂(4) paragraph of I.2.2(5),
printed pp.407 and 411 (PDF pp.418 and 422), using Aschbacher, *Sporadic
Groups*, Lemmas 46.9 and 49.5. The imported Leech and octonion constructions
retain their ATLAS attribution; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is ported here.
-/

public section

namespace Atlas.G2.FourNontrivialCover
open Subgroup PerfectCentralCovering
open Atlas.Conway Atlas.Lattices Atlas.G2.FiniteCover
noncomputable section

/-- The literal pullback of the Leech central projection along `j`. -/
@[expose] def pullback (j : FourBase →* LeechCentralQuotient) :
    Subgroup (LeechIsometryGroup × FourBase) :=
  (leechCentralProjection.comp (MonoidHom.fst _ _)).eqLocus
    (j.comp (MonoidHom.snd _ _))

/-- The second projection to the actual octonion G₂(4) carrier. -/
@[expose] def projection (j : FourBase →* LeechCentralQuotient) : pullback j →* FourBase :=
  (MonoidHom.snd _ _).comp (pullback j).subtype

/-- The first projection realizes the pullback inside Co₀ when `j` is injective. -/
@[expose] def toLeech (j : FourBase →* LeechCentralQuotient) :
    pullback j →* LeechIsometryGroup :=
  (MonoidHom.fst _ _).comp (pullback j).subtype

/-- The actual quotient square commutes, with no change of base model. -/
theorem quotient_square (j : FourBase →* LeechCentralQuotient) :
    leechCentralProjection.comp (toLeech j) = j.comp (projection j) := by
  ext x
  exact x.property

theorem toLeech_injective (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) : Function.Injective (toLeech j) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext h
  apply hj
  exact x.property.symm.trans ((congrArg leechCentralProjection h).trans y.property)

theorem projection_surjective (j : FourBase →* LeechCentralQuotient) :
    Function.Surjective (projection j) := by
  intro b
  obtain ⟨a, ha⟩ := leechCentralProjection_surjective (j b)
  exact ⟨⟨(a, b), ha⟩, rfl⟩

theorem negation_projection : leechCentralProjection negationIsometry = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [leechCentralProjection_kernel, leechCentralSigns_mem]
  exact Or.inr rfl

/-- The central sign retained from the Leech isometry group. -/
@[expose] def centralSign (j : FourBase →* LeechCentralQuotient) : pullback j :=
  ⟨(negationIsometry, 1), by
    change leechCentralProjection negationIsometry = j 1
    rw [negation_projection, map_one]⟩

theorem centralSign_ne_one (j : FourBase →* LeechCentralQuotient) : centralSign j ≠ 1 := by
  intro h
  exact negationIsometry_ne_one (congrArg (fun x : pullback j => x.val.1) h)

theorem centralSign_sq (j : FourBase →* LeechCentralQuotient) : centralSign j ^ 2 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · change negationIsometry ^ 2 = 1
    simpa only [pow_two] using negationIsometry_sq
  · exact one_mul 1

theorem centralSign_mem_center (j : FourBase →* LeechCentralQuotient) :
    centralSign j ∈ center (pullback j) := by
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact mem_center_iff.mp negation_mem_center x.val.1
  · exact mul_one x.val.2 |>.trans (one_mul x.val.2).symm

theorem projection_ker (j : FourBase →* LeechCentralQuotient) (x : pullback j) :
    x ∈ (projection j).ker ↔ x = 1 ∨ x = centralSign j := by
  constructor
  · intro hx
    have hb : x.val.2 = 1 := hx
    have ha : x.val.1 ∈ leechCentralSigns := by
      rw [← leechCentralProjection_kernel]
      change leechCentralProjection x.val.1 = 1
      calc
        leechCentralProjection x.val.1 = j x.val.2 := x.property
        _ = 1 := by rw [hb, map_one]
    rcases (leechCentralSigns_mem _).mp ha with ha | ha
    · exact Or.inl (Subtype.ext (Prod.ext ha hb))
    · exact Or.inr (Subtype.ext (Prod.ext ha hb))
  · rintro (rfl | rfl)
    · exact (projection j).ker.one_mem
    · rfl

theorem projection_ker_le_center (j : FourBase →* LeechCentralQuotient) :
    (projection j).ker ≤ center (pullback j) := by
  intro x hx
  rcases (projection_ker j x).mp hx with rfl | rfl
  · exact (center (pullback j)).one_mem
  · exact centralSign_mem_center j


/-- The center of the pullback contains the genuine nonidentity Leech sign. -/
theorem center_ne_bot (j : FourBase →* LeechCentralQuotient) :
    center (pullback j) ≠ ⊥ := by
  intro h
  have hz := centralSign_mem_center j
  rw [h, mem_bot] at hz
  exact centralSign_ne_one j hz

/-- The marked isometry defines an element of the literal pullback. -/
@[expose] def markedLift (j : FourBase →* LeechCentralQuotient)
    (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) : pullback j := ⟨(a, b), ha⟩

theorem markedLift_sq (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry) :
    markedLift j b a ha ^ 2 = centralSign j := by
  apply Subtype.ext
  apply Prod.ext
  · exact hsq
  · change b ^ 2 = 1
    apply hj
    rw [map_pow, ← ha, ← map_pow, hsq, negation_projection, map_one]

theorem markedLift_order (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry) :
    orderOf (markedLift j b a ha) = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one, markedLift_sq j hj b a ha hsq] using centralSign_ne_one j
  · change markedLift j b a ha ^ (2 * 2) = 1
    rw [pow_mul, markedLift_sq j hj b a ha hsq, centralSign_sq]

/-- The nonsplit pullback is a perfect central cover, proved from its square.
No perfectness or quasisimplicity of the pullback is assumed. -/
@[expose] def coverOfMarkedSquare (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry) :
    Cover (pullback j) FourBase where
  toMonoidHom := projection j
  surjective := projection_surjective j
  ker_le_center := projection_ker_le_center j
  isPerfect := isPerfect_of_central_binary_kernel_of_square (projection j)
    (projection_surjective j) (projection_ker_le_center j)
    (centralSign j) (centralSign_sq j) (fun k hk => (projection_ker j k).mp hk)
    (markedLift j b a ha) (markedLift_sq j hj b a ha hsq)

theorem isQuasisimple_of_marked_square (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry) :
    Theory.GroupTheory.IsQuasisimple (pullback j) :=
  (coverOfMarkedSquare j hj b a ha hsq).isQuasisimple

/-- The constructed quasisimple group's central quotient is the actual
split-octonion model over GF(4), via the pullback projection. -/
@[expose] def quotientCenterEquivOfMarkedSquare (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry) :
    pullback j ⧸ center (pullback j) ≃* FourBase := by
  let c := coverOfMarkedSquare j hj b a ha hsq
  letI : Theory.GroupTheory.IsQuasisimple (pullback j) := c.isQuasisimple
  have hk : (projection j).ker = center (pullback j) :=
    c.toCovering.ker_eq_center_of_isSimple
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (projection j) (projection_surjective j))

theorem quotientCenterEquivOfMarkedSquare_apply (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry)
    (x : pullback j) :
    quotientCenterEquivOfMarkedSquare j hj b a ha hsq
      (QuotientGroup.mk' (center (pullback j)) x) = projection j x := by
  rfl

/-- The literal canonical universal kernel is nontrivial once the independent
Conway embedding and its marked square are constructed. -/
theorem fourKernel_ne_bot_of_marked_square (j : FourBase →* LeechCentralQuotient)
    (hj : Function.Injective j) (b : FourBase) (a : LeechIsometryGroup)
    (ha : leechCentralProjection a = j b) (hsq : a ^ 2 = negationIsometry) :
    Kernel FourField ≠ ⊥ := by
  apply (coverOfMarkedSquare j hj b a ha hsq).universalKernel_ne_bot_of_ker_ne_bot
  intro h
  change (projection j).ker = ⊥ at h
  have hz : centralSign j ∈ (projection j).ker := (projection_ker j _).mpr (Or.inr rfl)
  rw [h, mem_bot] at hz
  exact centralSign_ne_one j hz

end
end Atlas.G2.FourNontrivialCover
