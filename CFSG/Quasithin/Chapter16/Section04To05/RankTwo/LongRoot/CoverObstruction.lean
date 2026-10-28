module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Action
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.SevenAction

/-!
# The simultaneous-normalizer action in the covered obstruction

The simultaneous normalizer acts on the actual common residual `X`, its
characteristic two-core, and the actual subgroup `V`. The inclusion of `V`
into that two-core is equivariant for these conjugation actions; this is
proved, rather than supplied as a compatibility certificate.

The two intrinsic image bounds on `X/O₂(X)` and the Frattini section now
exclude an image of order 21 on `V`. In the source application `V = Φ(O₂(X))`.
The exact cover calculation supplying this equality and the two image bounds
remains separate.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed p.1202.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
open Subgroup
variable {G : Type*} [Group G]

/-- The same group which acts on `V` also acts by conjugation on the actual `X`. -/
def residualAction (V X : Subgroup G) : actingGroup V X →* MulAut X :=
  X.normalizerMonoidHom.comp (inclusion inf_le_right)

/-- The actual embedded two-core of `X`. -/
def twoCore (X : Subgroup G) : Subgroup G := (pCore 2 X).map X.subtype

/-- The actual embedded Frattini subgroup of that two-core. -/
def coreFrattini (X : Subgroup G) : Subgroup G :=
  (frattini (pCore 2 X)).map (X.subtype.comp (pCore 2 X).subtype)

/-- The intrinsic two-core and its ambient image are canonically equivalent. -/
noncomputable def coreEquiv (X : Subgroup G) : pCore 2 X ≃* twoCore X :=
  (pCore 2 X).equivMapOfInjective X.subtype X.subtype_injective

/-- The inclusion into the actual intrinsic two-core. -/
noncomputable def coreEmbedding {V X : Subgroup G} (hVQ : V ≤ twoCore X) :
    V →* pCore 2 X :=
  (coreEquiv X).symm.toMonoidHom.comp (inclusion hVQ)

theorem coreEmbedding_coe {V X : Subgroup G} (hVQ : V ≤ twoCore X) (v : V) :
    (((coreEmbedding hVQ v : pCore 2 X) : X) : G) = v := by
  have he := congrArg (fun y : twoCore X => (y : G))
    ((coreEquiv X).apply_symm_apply (inclusion hVQ v))
  exact he

theorem coreEmbedding_injective {V X : Subgroup G} (hVQ : V ≤ twoCore X) :
    Function.Injective (coreEmbedding hVQ) :=
  (coreEquiv X).symm.injective.comp (inclusion_injective hVQ)

/-- Both actions are conjugation by the same ambient element. -/
theorem coreEmbedding_equivariant {V X : Subgroup G} (hVQ : V ≤ twoCore X)
    (m : actingGroup V X) (v : V) :
    coreEmbedding hVQ (action V X m v) =
      coreAction (residualAction V X) m (coreEmbedding hVQ v) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coreEmbedding_coe]
  change (m : G) * (v : G) * (m : G)⁻¹ =
    (m : G) * (((coreEmbedding hVQ v : pCore 2 X) : X) : G) * (m : G)⁻¹
  rw [coreEmbedding_coe]

theorem coreFrattini_le_twoCore (X : Subgroup G) : coreFrattini X ≤ twoCore X := by
  rw [coreFrattini, ← map_map]
  exact map_mono (map_subtype_le _)

variable [Finite G]

/-- Eliminate the exceptional O'Nan image using intrinsic bounds for the actual
residual action. No assumption about the order or solvability of `O^{7′}(M)`
is needed, and no isomorphism type is substituted for a subgroup inclusion. -/
theorem no_order_twentyOne_image {V X : Subgroup G} (hVQ : V ≤ twoCore X)
    (hquot : Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range))
    (hmodule : Nat.Coprime 7
      (Nat.card ((topAction (residualAction V X)).ker.map
        (sectionAction (residualAction V X)))))
    (hcard : Nat.card (action V X).range = 21) : False := by
  apply no_seven_image_on_core_subgroup (residualAction V X) (action V X)
    (coreEmbedding hVQ) (coreEmbedding_injective hVQ)
    (coreEmbedding_equivariant hVQ) hquot hmodule
  rw [hcard]
  decide

/-- The form directly consumed by the `G₂(4)` cover calculation. -/
theorem no_order_twentyOne_image_of_frattini {V X : Subgroup G}
    (hΦ : V = coreFrattini X)
    (hquot : Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range))
    (hmodule : Nat.Coprime 7
      (Nat.card ((topAction (residualAction V X)).ker.map
        (sectionAction (residualAction V X)))))
    (hcard : Nat.card (action V X).range = 21) : False :=
  no_order_twentyOne_image (hΦ ▸ coreFrattini_le_twoCore X) hquot hmodule hcard

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
