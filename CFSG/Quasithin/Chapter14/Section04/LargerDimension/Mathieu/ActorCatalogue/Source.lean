module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Assembly

/-!
# The source Mathieu residual actors

The native point-centralizer theorem constructs the Borel used by the complete
native parabolic calculation. Residual lifting through the original H/O₂(H)
map then gives all three ambient actors, their distinctness, the exhaustive
X-family, and the S₃ × S₃ quotient of the first two actors with T. The first
actor is the original O²(O₂,₃(H)); the third is the residual of the actual
Borel preimage. The binary point and every quotient map are retained.

The module calculations deciding membership in Y are separate. No actor
catalogue, point-centralizer order, or overlap isomorphism is assumed here.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The canonical ambient residual lift through the literal two-core quotient. -/
def liftedActor (H : Subgroup G) (e : coreQuotient H ≃* Native.Model)
    (P : Subgroup Native.Model) : Subgroup G :=
  (residualLift (starProjection H e) P).map H.subtype

/-- The actual ambient Borel preimage, before taking its two-residual. -/
def sourceBorel (H : Subgroup G) (e : coreQuotient H ≃* Native.Model)
    (B : Subgroup Native.Model) : Subgroup G :=
  (B.comap (starProjection H e)).map H.subtype

omit [Finite G] in
theorem liftedActor_le (H : Subgroup G) (e : coreQuotient H ≃* Native.Model)
    (P : Subgroup Native.Model) : liftedActor H e P ≤ H := map_subtype_le _

/-- The original projection sends the lifted actor to precisely its residual. -/
theorem liftedActor_image (H : Subgroup G) (e : coreQuotient H ≃* Native.Model)
    (P : Subgroup Native.Model) :
    ((liftedActor H e P).subgroupOf H).map (starProjection H e) = twoResidual P := by
  have he : (liftedActor H e P).subgroupOf H = residualLift (starProjection H e) P :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [he, residualLift_map _ (starProjection_surjective H e)]

private theorem residual_idempotent {A : Type*} [Group A] [Finite A]
    (P : Subgroup A) : twoResidual (twoResidual P) = twoResidual P := by
  have hp := (pResidual_eq_top_iff 2 (twoResidual P)).mpr
    (isPPerfect_embedded_pResidual 2 P)
  change (pResidual 2 (twoResidual P)).map (twoResidual P).subtype = twoResidual P
  rw [hp, ← MonoidHom.range_eq_map, range_subtype]

private theorem residualLift_residual {A B : Type*} [Group A] [Group B]
    [Finite A] (q : A →* B) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (P : Subgroup B) :
    residualLift q (twoResidual P) = residualLift q P := by
  have hn (R : Subgroup B) : q.ker ≤ normalizer (residualLift q R : Set A) := by
    have he : q.ker ≤ R.comap q := by
      intro g hg
      change q g ∈ R
      rw [MonoidHom.mem_ker.mp hg]
      exact R.one_mem
    exact he.trans ((R.comap q).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (R.comap q) (pResidual 2 (R.comap q))))
  have : Finite B := Finite.of_surjective q hq
  apply eq_of_map_eq_map_of_isPPerfect q
    (isPPerfect_embedded_pResidual 2 _) (isPPerfect_embedded_pResidual 2 _) hk
    (hn _) (hn _)
  change (residualLift q (twoResidual P)).map q = (residualLift q P).map q
  rw [residualLift_map q hq, residualLift_map q hq, residual_idempotent]

theorem liftedActor_residual (H : Subgroup G) (e : coreQuotient H ≃* Native.Model)
    (P : Subgroup Native.Model) : liftedActor H e (twoResidual P) = liftedActor H e P := by
  unfold liftedActor
  rw [residualLift_residual _ (starProjection_surjective H e)
    (by rw [starProjection_ker]; exact pCore_isPGroup)]

/-- The cubic residual lift is exactly the first actor in the source. -/
theorem firstActor_eq_liftedActor (H : Subgroup G)
    (e : coreQuotient H ≃* Native.Model) :
    firstActor H = liftedActor H e (twoResidual (pCore 3 Native.Model)) := by
  rw [firstActor_eq_residualLift H e, liftedActor,
    NativeParabolics.firstActor_eq_cubic, NativeParabolics.threeCore_eq_cubic]

theorem borelActor_eq_liftedActor (H : Subgroup G)
    (e : coreQuotient H ≃* Native.Model) (B : Subgroup Native.Model) :
    borelActor (sourceBorel H e B) = liftedActor H e B :=
  borelActor_eq_residualLift H (starProjection H e) B

/-- Distinct residual actors in the native group stay distinct in G. -/
theorem liftedActor_ne (H : Subgroup G) (e : coreQuotient H ≃* Native.Model)
    {P R : Subgroup Native.Model} (hP : twoResidual P = P)
    (hR : twoResidual R = R) (hne : P ≠ R) :
    liftedActor H e P ≠ liftedActor H e R := by
  intro he
  exact residualLift_ne _ (starProjection_surjective H e) hP hR hne
    ((map_injective H.subtype_injective) he)

/-- The family bijection on a native three-element catalogue. -/
theorem liftedActor_catalogue (H : Subgroup G) (S : Sylow 2 H)
    (e : coreQuotient H ≃* Native.Model) (P₁ P₂ P₃ : Subgroup Native.Model)
    (hfamily : XFamily ⊤ ((S : Subgroup H).map (starProjection H e)) = {P₁, P₂, P₃}) :
    XFamily H ((S : Subgroup H).map H.subtype) =
      {liftedActor H e P₁, liftedActor H e P₂, liftedActor H e P₃} := by
  calc
    _ = liftedActor H e '' XFamily ⊤ ((S : Subgroup H).map (starProjection H e)) :=
      source_XFamily_transport H S e
    _ = _ := by rw [hfamily, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

/-- The quotient of the literal first-two-actor overlap is transported through
the original projection, with neither actor nor Sylow replaced. -/
theorem liftedActor_overlap (H : Subgroup G) (S : Sylow 2 H)
    (e : coreQuotient H ≃* Native.Model) (P₁ P₂ : Subgroup Native.Model)
    (h₁ : twoResidual P₁ = P₁) (h₂ : twoResidual P₂ = P₂)
    (hquot : Nonempty (coreQuotient
      (P₁ ⊔ P₂ ⊔ (S : Subgroup H).map (starProjection H e)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty (coreQuotient
      (liftedActor H e P₁ ⊔ liftedActor H e P₂ ⊔ (S : Subgroup H).map H.subtype) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let T := (S : Subgroup H).map H.subtype
  have hTH : T ≤ H := map_subtype_le _
  have h1H := liftedActor_le H e P₁
  have h2H := liftedActor_le H e P₂
  have hT : T.subgroupOf H = (S : Subgroup H) :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have hm : ((liftedActor H e P₁ ⊔ liftedActor H e P₂ ⊔ T).subgroupOf H).map
      (starProjection H e) = P₁ ⊔ P₂ ⊔ (S : Subgroup H).map (starProjection H e) := by
    rw [subgroupOf_sup (sup_le h1H h2H) hTH, subgroupOf_sup h1H h2H,
      Subgroup.map_sup, Subgroup.map_sup, liftedActor_image, liftedActor_image, h₁, h₂, hT]
  obtain ⟨eqv⟩ := hquot
  let f := sourceCoreImageEquiv H (liftedActor H e P₁ ⊔ liftedActor H e P₂ ⊔ T)
    (sup_le (sup_le h1H h2H) hTH) e
  rw [hm] at f
  exact ⟨f.trans eqv⟩

/-- The native point-core calculation now discharges the formerly explicit
order premise in the original Wg* identification. -/
theorem source_WStar_eq_twoCore_of_sylow_fixed
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup G) (ρ : Representation (ZMod 2) (coreQuotient H) V)
    (e : coreQuotient H ≃* Native.Model) (a : V ≃ₗ[ZMod 2] Native.Space)
    (ha : ∀ g v, a (ρ g v) = Native.action (e g) (a v)) (v : V)
    (S : Sylow 2 Native.Model) (hv : a v ≠ 0)
    (hfixed : ∀ s : S, Native.action s.val (a v) = a v)
    (WStar : Subgroup (coreQuotient H))
    (hWC : WStar ≤ Native.vectorStabilizer ρ v)
    (hn : Native.vectorStabilizer ρ v ≤ normalizer (WStar : Set (coreQuotient H)))
    (hW : IsPGroup 2 WStar) (hcard : Nat.card WStar = 32) :
    WStar = twoCore (Native.vectorStabilizer ρ v) :=
  source_WStar_eq_twoCore H ρ e a ha v WStar hWC hn hW hcard
    (Native.pointCentralizer_core_card S (a v) hv hfixed)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
