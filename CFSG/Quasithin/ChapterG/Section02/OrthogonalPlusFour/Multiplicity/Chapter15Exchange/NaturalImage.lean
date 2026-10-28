module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes

/-!
# Order of the actual natural Sylow image in Chapter 15

Compatibility identifies both the wreath actor kernel and the literal
conjugation kernel with the same relative centralizer. Their image orders
therefore agree. Surjective images of the specified local Sylow subgroup
are Sylow in the concrete orthogonal actor, whose Sylow subgroups have
order eight. The source span equality then transports this calculation
to precisely the G.2.6 natural action used in the multiplicity argument.

Both a local Sylow witness and an ambient Sylow with containment are
supported. No assertion is made that a general G.2.6 natural T-image has
order eight; the earlier compatible Chapter 15 action is essential here.

Source: Aschbacher–Smith, 15.3.2 and the decomposition following 15.3.4,
printed pp.1121–1122; the substitution in 15.3.54, printed p.1146.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
open CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G]

/-- Restriction of literal ambient conjugation to a normalizing subgroup. -/
def naturalAction {V A : Subgroup G} (h : A ≤ normalizer (V : Set G)) : A →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion h)

/-- The kernel is the actual centralizer, independently of any model coordinates. -/
theorem naturalAction_ker {V A : Subgroup G} (h : A ≤ normalizer (V : Set G)) :
    (naturalAction h).ker = (centralizer (V : Set G)).subgroupOf A := by
  ext a
  constructor
  · intro ha v hv
    have he := congrArg (fun f : MulAut V => (f ⟨v, hv⟩ : G)) ha
    change (a : G) * v * (a : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (a : G) * (v : G) * (a : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (ha v v.property).symm

/-- Compatibility, rather than an abstract wreath-group isomorphism, identifies image orders. -/
theorem naturalAction_card {M V A : Subgroup G}
    (a : NaturalOrthogonalAction M V) (hAM : A ≤ M) :
    Nat.card (naturalAction (hAM.trans a.normalizes)).range = Nat.card (a.image A) := by
  let f := a.actor.comp (inclusion hAM)
  have hk : f.ker = (naturalAction (hAM.trans a.normalizes)).ker := by
    rw [naturalAction_ker, show f.ker = a.actor.ker.comap (inclusion hAM) from rfl, a.ker_actor]
    rfl
  have hr : f.range = a.image A := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨inclusion hAM t, t.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  rw [← index_ker, ← hk, index_ker, hr]

/-- A local Sylow subgroup has order eight in the actual natural action. -/
theorem naturalAction_card_eight [Finite G] {M V T : Subgroup G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T) :
    Nat.card (naturalAction (hTM.trans a.normalizes)).range = 8 := by
  rw [naturalAction_card a hTM]
  obtain ⟨P, hP⟩ := hSyl
  have ht : T.subgroupOf M = (P : Subgroup M) := by
    rw [← hP, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]
  change Nat.card ((T.subgroupOf M).map a.actor) = 8
  rw [ht]
  exact OrthogonalGeometry.sylow_card (P.mapSurjective a.onto)

/-- The source may instead provide its ambient Sylow together with containment in M. -/
theorem naturalAction_card_eight_ambient [Finite G] {M V : Subgroup G}
    (a : NaturalOrthogonalAction M V) (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    Nat.card (naturalAction (hTM.trans a.normalizes)).range = 8 := by
  rw [naturalAction_card a hTM]
  exact OrthogonalGeometry.sylow_card (a.sylowImage T hTM)

/-- Transport the source span equality to the literal G.2.6 conjugation map. -/
theorem literal_naturalAction_card_eight [Finite G]
    {M Z Zperp V Y T : Subgroup G} {g : G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) :
    Nat.card (naturalAction (Chapter15Collapse.T_normalizes_natural d)).range = 8 := by
  have hV := Chapter15.VL_eq (Zperp := Zperp) (T := T) hspan
  have ha := naturalAction_card_eight a hTM hSyl
  generalize_proofs hD at ⊢
  change Nat.card (naturalAction (A := T) hD).range = 8
  subst V
  exact ha

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
