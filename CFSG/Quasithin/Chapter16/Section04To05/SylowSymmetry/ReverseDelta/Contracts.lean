module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.ModelAction
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.Mathieu.M12.Basic

/-!
# Precise residual-comparison contracts for reverse Δ₀

`Contrary` contains the configuration obtained before the centralizer tables
are inspected. Its innerness, actual outer action, and relative residual
normality are derived here. `M12Comparison` records the missing comparison
through actual central quotient maps; `M12LocalData` records the subsequent
covering and action facts. These are unproved prerequisite contracts, not
assertions of the numbered source lemma. The remaining proof owners must
construct them before the source theorem can be assembled.

The quotient image convention agrees with the action quotient H/C_G(L) on
subgroups of L. It does not replace O² by O₂, or quotient a residual by its
own center without justification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 16.4.11(2), printed p.1193; 16.1.4–5 and I.2.2(5b).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Image in the actual central quotient of the indicated component. The
subgroupOf is paired with explicit containment whenever its carrier is used. -/
def centralImage (L X : Subgroup G) : Subgroup (L ⧸ center L) :=
  (X.subgroupOf L).map (QuotientGroup.mk' (center L))

/-- With trivial covering kernel the actual subgroup is isomorphic to its image. -/
noncomputable def centralImageEquiv {L X : Subgroup G} (hXL : X ≤ L)
    (hZ : center L = ⊥) : X ≃* centralImage L X :=
  (subgroupOfEquivOfLe hXL).symm.trans
    ((X.subgroupOf L).equivMapOfInjective (QuotientGroup.mk' (center L))
      ((MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hZ])))

/-- The contrary configuration derived before inspecting 16.1.4–5. None of
its fields is reverse Δ₀ membership or the desired M₁₂ identification. -/
structure Contrary (T : Sylow 2 G) (z : G) (L : Subgroup G) (g : G)
    (R : Subgroup G) (r : G) : Prop where
  setup : IntersectionSetup T z L g R
  evenType : HasEvenTypeCentralizers G
  sylow : SylowIn R ((centralizer (L : Set G)).conjBy g)
  deltaZero : (centralizer (L : Set G)).conjBy g ∈ Intersections.deltaZero L
  faithful : R ⊓ centralizer (L : Set G) = ⊥
  not_normalized : ¬ L ≤ normalizer (L.conjBy g : Set G)
  small : Nat.card (commutingSylow T L) = 2
  mem : r ∈ R
  involution : orderOf r = 2
  z_normalizes : z ∈ normalizer (L.conjBy g : Set G)
  outer : z ∉ centralizer (L.conjBy g : Set G) ⊔ L.conjBy g
  placement : residual (L.conjBy g) z ≤ L

variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

theorem Contrary.inner (d : Contrary T z L g R r) :
    r ∈ centralizer (L : Set G) ⊔ L :=
  (omegaOneAmbient_le_iff _ _).mp (omega_le_of_deltaZero d.setup d.deltaZero)
    r d.mem (d.involution ▸ pow_orderOf_eq_one r)

theorem Contrary.residual_normal (d : Contrary T z L g R r) :
    residual (L.conjBy g) z ≤ residual L r ∧
      ((residual (L.conjBy g) z).subgroupOf (residual L r)).Normal ∧
      L ⊓ centralizer ({r} : Set G) ≤ normalizer (residual (L.conjBy g) z : Set G) := by
  apply residual_relative_normal (z_mem_commutingSylow d.setup).2 _
    (involution_centralizer_control d.setup d.mem d.involution) d.placement
  rw [centralizer_conjugate]
  exact d.sylow.le d.mem

/-- The outer condition concerns the actual normalizer action on L′. -/
theorem Contrary.outer_action (d : Contrary T z L g R r) :
    ¬ ∃ l : L.conjBy g,
      (L.conjBy g).normalizerMonoidHom ⟨z, d.z_normalizes⟩ = MulAut.conj l := by
  rintro ⟨l, hl⟩
  let zN : normalizer (L.conjBy g : Set G) := ⟨z, d.z_normalizes⟩
  let lN : normalizer (L.conjBy g : Set G) :=
    ⟨l, (L.conjBy g).le_normalizer l.property⟩
  have he : (L.conjBy g).normalizerMonoidHom lN = MulAut.conj l := by
    ext x
    rfl
  have hk : zN * lN⁻¹ ∈ (L.conjBy g).normalizerMonoidHom.ker := by
    change (L.conjBy g).normalizerMonoidHom (zN * lN⁻¹) = 1
    rw [map_mul, map_inv, he, show (L.conjBy g).normalizerMonoidHom zN =
      MulAut.conj l from hl, mul_inv_cancel]
  rw [normalizerMonoidHom_ker] at hk
  apply d.outer
  have hm := mul_mem_sup (show z * (l : G)⁻¹ ∈ centralizer (L.conjBy g : Set G) from hk)
    l.property
  simpa only [inv_mul_cancel_right] using hm

/-- Faithfulness from 16.4.2(1) makes the inner action nontrivial. -/
theorem Contrary.not_centralizing (d : Contrary T z L g R r) :
    r ∉ centralizer (L : Set G) := by
  intro hrK
  have hr1 : r = 1 := by
    have hh : r ∈ R ⊓ centralizer (L : Set G) := ⟨d.mem, hrK⟩
    rwa [d.faithful, mem_bot] at hh
  have hh := d.involution
  simp [hr1] at hh

/-- The inner condition produces an actual inner automorphism, with the
conjugating element in L and the ambient conjugation equation preserved. -/
theorem Contrary.inner_action (d : Contrary T z L g R r) :
    ∃ l : L, L.normalizerMonoidHom
      ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩ = MulAut.conj l := by
  have hi := d.inner
  change r ∈ ((centralizer (L : Set G) ⊔ L : Subgroup G) : Set G) at hi
  rw [coe_mul_of_left_le_normalizer_right _ _ (centralizer_le_normalizer _)] at hi
  obtain ⟨c, hc, l, hl, he⟩ := hi
  refine ⟨⟨l, hl⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change r * (x : G) * r⁻¹ = l * (x : G) * l⁻¹
  rw [← he, mul_inv_rev]
  calc
    c * l * (x : G) * (l⁻¹ * c⁻¹) = c * (l * (x : G) * l⁻¹) * c⁻¹ := by group
    _ = l * (x : G) * l⁻¹ := by
      rw [← mem_centralizer_iff.mp hc _ (L.mul_mem (L.mul_mem hl x.property) (L.inv_mem hl)),
        mul_inv_cancel_right]

/-- The inner action used in 16.1.4–5 has order exactly two. -/
theorem Contrary.inner_action_order (d : Contrary T z L g R r) :
    orderOf (L.normalizerMonoidHom
      ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩) = 2 := by
  let a : normalizer (L : Set G) :=
    ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩
  have ha : a ^ 2 = 1 := Subtype.ext (d.involution ▸ pow_orderOf_eq_one r)
  apply orderOf_eq_prime (by
    change (L.normalizerMonoidHom a) ^ 2 = 1
    rw [← map_pow, ha, map_one])
  intro he
  have hk : a ∈ L.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact d.not_centralizing hk

/-- The outer action used in the reversed 16.4.8 and the tables also has
order exactly two. -/
theorem Contrary.outer_action_order (d : Contrary T z L g R r) :
    orderOf ((L.conjBy g).normalizerMonoidHom ⟨z, d.z_normalizes⟩) = 2 := by
  let a : normalizer (L.conjBy g : Set G) := ⟨z, d.z_normalizes⟩
  have ha : a ^ 2 = 1 := Subtype.ext (d.setup.involution ▸ pow_orderOf_eq_one z)
  apply orderOf_eq_prime (by
    change ((L.conjBy g).normalizerMonoidHom a) ^ 2 = 1
    rw [← map_pow, ha, map_one])
  intro he
  apply d.outer_action
  exact ⟨1, he.trans (map_one MulAut.conj).symm⟩

/-- The exact model identifications still required from comparing the inner and
outer rows of 16.1.4–5. Each star is an image in an actual central quotient. -/
structure M12Comparison (L M : Subgroup G) (r z : G) : Prop where
  component : Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M12)
  innerResidual : Nonempty (centralImage L (residual L r) ≃* A5)
  outerResidual : Nonempty (centralImage M (residual M z) ≃* A5)

/-- The M₁₂ row inputs used after the comparison. The cover clause quantifies
over actual commuting factorizations; the outer restriction is an equation
for the action on the actual two-residual, not an abstract isomorphism tag. -/
structure M12LocalData (L M : Subgroup G) (r z : G) : Prop where
  cover_lift : center L ≠ ⊥ → ∃ c ∈ centralizer (L : Set G),
    ∃ l ∈ L, r = c * l ∧ orderOf l = 4
  inner_centralizer : center L = ⊥ →
    Nonempty ((L ⊓ centralizer ({r} : Set G) : Subgroup G) ≃* InnerCentralizerModel)
  outer_restriction : center L = ⊥ → ∀ x ∈ normalizer (M : Set G) ⊓ centralizer ({z} : Set G),
    ∃ a ∈ residual M z, ∀ b ∈ residual M z, x * b * x⁻¹ = a * b * a⁻¹

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
