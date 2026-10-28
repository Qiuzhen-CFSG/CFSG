module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Reduction
public import Theory.GroupTheory.PResidual.CentralSylowFrattini
public import Theory.GroupTheory.SylowNormalRestriction


/-!
# Quotient lifting for the marked calculation in 15.3.59

The actor projection and the restriction to K = O²(H) are literal quotient
maps. The residual Sylow group is constructed by restricting a supplied
Sylow subgroup of H. After Q_H = U C_T(U) and [K,C_T(U)] = 1, the actor
kernel in K is central modulo U. Its Sylow Frattini image therefore does
not contribute generators. This proves the lifting step without assuming
C_T(U) ≤ K or classifying the central cover K/U.

The final cardinal calculation uses |U| = 2⁷ and the order-eight actor
image. The marked image-generation and residual-containment inputs remain
separate obligations; these conditional lemmas do not assert 15.3.59.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1149–1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
variable {G : Type*} [Group G]

/-- The literal projection H → H/O₂(H). -/
def actorProjection (Z : Subgroup G) : centralizerH Z →* ActorQuotient Z :=
  QuotientGroup.mk' _

/-- The image of an ambient subgroup, restricted to H, in the actor quotient. -/
def actorImage (Z A : Subgroup G) : Subgroup (ActorQuotient Z) :=
  (A.subgroupOf (centralizerH Z)).map (actorProjection Z)

/-- The residual is embedded in its defining centralizer. -/
theorem residual_le_H (Z : Subgroup G) : residualK Z ≤ centralizerH Z := map_subtype_le _

/-- The actual restriction K → H/O₂(H). -/
noncomputable def residualActor (Z : Subgroup G) : residualK Z →* ActorQuotient Z :=
  (actorProjection Z).comp (inclusion (residual_le_H Z))

/-- The quotient kernel is the embedded two-core, with no ambient normality. -/
theorem actorProjection_eq_one_iff (Z : Subgroup G) (h : centralizerH Z) :
    actorProjection Z h = 1 ↔ (h : G) ∈ coreQ Z := by
  change (h : ActorQuotient Z) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hh
    exact mem_map_of_mem (centralizerH Z).subtype hh
  · rintro ⟨k, hk, he⟩
    have he' : k = h := Subtype.ext he
    exact he' ▸ hk

/-- In K the actor kernel is K ∩ Q_H, not the whole Q_H. -/
theorem residualActor_ker (Z : Subgroup G) :
    (residualActor Z).ker = (coreQ Z).subgroupOf (residualK Z) := by
  ext k
  exact actorProjection_eq_one_iff Z (inclusion (residual_le_H Z) k)

/-- The internal residual projection agrees with the ambient actor image. -/
theorem residualActor_map (Z A : Subgroup G) (hAK : A ≤ residualK Z) :
    (A.subgroupOf (residualK Z)).map (residualActor Z) = actorImage Z A := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨inclusion (residual_le_H Z) a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, hAK ha⟩, ha, rfl⟩

variable [Finite G]

/-- Normality of the residual is relative to H. -/
theorem residual_normal_in_H (Z : Subgroup G) :
    ((residualK Z).subgroupOf (centralizerH Z)).Normal := by
  have he : (residualK Z).subgroupOf (centralizerH Z) = pResidual 2 (centralizerH Z) := by
    apply map_injective (centralizerH Z).subtype_injective
    rw [map_subgroupOf_eq_of_le (residual_le_H Z), ← twoResidualAmbient_eq_pResidual]
  rw [he]
  infer_instance

/-- The literal T ∩ K is the ambient image of a Sylow subgroup of K. -/
theorem residualSylow_exists (T Z : Subgroup G)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T) :
    ∃ R : Sylow 2 (residualK Z),
      (R : Subgroup (residualK Z)).map (residualK Z).subtype = residualSylow T Z := by
  let N := (residualK Z).subgroupOf (centralizerH Z)
  let : N.Normal := residual_normal_in_H Z
  obtain ⟨R, hR⟩ := S.exists_sylow_map_eq_inf_of_normal N
  let e := subgroupOfEquivOfLe (residual_le_H Z)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((R : Subgroup N).map e.toMonoidHom).map (residualK Z).subtype = _
  have hcomp : (residualK Z).subtype.comp e.toMonoidHom =
      (centralizerH Z).subtype.comp N.subtype := by ext; rfl
  rw [map_map, hcomp, ← map_map, hR, map_inf _ _ _ (centralizerH Z).subtype_injective,
    hS, map_subgroupOf_eq_of_le (residual_le_H Z)]
  rfl

omit [Finite G] in
/-- H-invariance of U induces normality of U ∩ K inside K. -/
instance closure_normal_in_residual (Z ZS : Subgroup G) :
    ((closureU Z ZS).subgroupOf (residualK Z)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((residual_le_H Z).trans (H_normalizes_closureU Z ZS))

omit [Finite G] in
open scoped Pointwise in
/-- The actor kernel in K has central image in K/U.
The proof factors an element of K ∩ Q_H as u c and proves c ∈ K; it never
assumes all of Q_C lies in K. -/
theorem residualActor_kernel_central_mod_closure (T Z ZS : Subgroup G)
    (hUK : closureU Z ZS ≤ residualK Z)
    (hQ : coreQ Z = closureU Z ZS ⊔ centralizerC T Z ZS)
    (hc : residualK Z ≤ centralizer (centralizerC T Z ZS : Set G)) :
    (residualActor Z).ker ≤
      (center ((residualK Z) ⧸ (closureU Z ZS).subgroupOf (residualK Z))).comap
        (QuotientGroup.mk' _) := by
  let K := residualK Z
  let U := closureU Z ZS
  let N := U.subgroupOf K
  let q := QuotientGroup.mk' N
  intro x hx
  have hxQ : (x : G) ∈ coreQ Z := by
    rwa [residualActor_ker] at hx
  have hxprod : (x : G) ∈ (U : Set G) * (centralizerC T Z ZS : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U (centralizerC T Z ZS)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))]
    exact hQ ▸ hxQ
  obtain ⟨u, hu, c, hcC, he⟩ := hxprod
  have hcK : c ∈ K := by
    have hh := K.mul_mem (K.inv_mem (hUK hu)) x.property
    rwa [← he, inv_mul_cancel_left] at hh
  let cK : K := ⟨c, hcK⟩
  have hxq : q x = q cK := by
    have heK : x = (⟨u, hUK hu⟩ : K) * cK := Subtype.ext he.symm
    rw [heK, map_mul]
    have huq : q ⟨u, hUK hu⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hu
    rw [huq, one_mul]
  change q x ∈ center (K ⧸ N)
  rw [hxq]
  apply mem_center_iff.mpr
  intro k
  induction k using QuotientGroup.induction_on with
  | H k =>
    change q k * q cK = q cK * q k
    rw [← map_mul, ← map_mul]
    apply congrArg q
    apply Subtype.ext
    exact (hc k.property c hcC).symm


/-- Frattini lifting of two marked subgroups generating the residual Sylow image.
The source application takes X = partnerX Z ZS y and Xt = Xᵗ. Their placement
and image-generation are still required inputs to this conditional step. -/
theorem residualSylow_generation_of_actor_generation (T Z ZS X Xt : Subgroup G)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (hUK : closureU Z ZS ≤ residualK Z) (hUT : closureU Z ZS ≤ T)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hQ : coreQ Z = closureU Z ZS ⊔ centralizerC T Z ZS)
    (hc : residualK Z ≤ centralizer (centralizerC T Z ZS : Set G))
    (hX : X ≤ residualSylow T Z) (hXt : Xt ≤ residualSylow T Z)
    (himage : actorImage Z (residualSylow T Z) ≤ actorImage Z (X ⊔ Xt)) :
    residualSylow T Z = (X ⊔ Xt) ⊔ closureU Z ZS := by
  let K := residualK Z
  let N := (closureU Z ZS).subgroupOf K
  let A := (X ⊔ Xt).subgroupOf K
  obtain ⟨R, hR⟩ := residualSylow_exists T Z S hS
  have hAK : X ⊔ Xt ≤ K := (sup_le hX hXt).trans inf_le_right
  have hAR : A ≤ (R : Subgroup K) := by
    intro a ha
    obtain ⟨r, hr, he⟩ := hR.symm ▸ (sup_le hX hXt ha)
    have he' : r = a := Subtype.ext he
    exact he' ▸ hr
  have hN : N ≤ (residualActor Z).ker := by
    rw [residualActor_ker]
    exact fun _ hx => hUQ hx
  have hRmap : (R : Subgroup K).map (residualActor Z) =
      actorImage Z (residualSylow T Z) := by
    have hRi : (R : Subgroup K) = (residualSylow T Z).subgroupOf K := by
      apply map_injective K.subtype_injective
      rw [hR, map_subgroupOf_eq_of_le (show residualSylow T Z ≤ K from inf_le_right)]
    rw [hRi]
    exact residualActor_map Z _ inf_le_right
  have hcover : (R : Subgroup K).map (residualActor Z) ≤ A.map (residualActor Z) := by
    rw [hRmap, residualActor_map Z _ hAK]
    exact himage
  have hh := sylow_le_sup_of_image_cover_of_central_kernel_mod
    (residualK_isPPerfect Z) R (residualActor Z) N hN
    (residualActor_kernel_central_mod_closure T Z ZS hUK hQ hc) A hAR hcover
  have hmap := map_mono (f := K.subtype) hh
  rw [hR, Subgroup.map_sup, map_subgroupOf_eq_of_le hAK,
    map_subgroupOf_eq_of_le hUK] at hmap
  exact le_antisymm hmap (sup_le (sup_le hX hXt) (le_inf hUT hUK))

/-- The order-128 subgroup U in the kernel and an actor image of order at least
eight give the required order-1024 lower bound on the actual T ∩ K. -/
theorem residualSylow_card_lower (T Z ZS : Subgroup G)
    (hUT : closureU Z ZS ≤ T) (hUK : closureU Z ZS ≤ residualK Z)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hU : Nat.card (closureU Z ZS) = 2 ^ 7)
    (himage : 2 ^ 3 ≤ Nat.card (actorImage Z (residualSylow T Z))) :
    2 ^ 10 ≤ Nat.card (residualSylow T Z) := by
  let R := residualSylow T Z
  let f := (residualActor Z).comp (inclusion (show R ≤ residualK Z from inf_le_right))
  have hker : (closureU Z ZS).subgroupOf R ≤ f.ker := by
    intro u hu
    apply (actorProjection_eq_one_iff Z _).mpr
    exact hUQ hu
  have hkcard : 2 ^ 7 ≤ Nat.card f.ker := by
    have hh := card_le_of_le hker
    have he : Nat.card ((closureU Z ZS).subgroupOf R) = Nat.card (closureU Z ZS) :=
      Nat.card_congr (subgroupOfEquivOfLe (show closureU Z ZS ≤ R from le_inf hUT hUK)).toEquiv
    rw [he, hU] at hh
    exact hh
  have hrange : f.range = actorImage Z R := by
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      exact ⟨⟨r, residual_le_H Z r.property.2⟩, r.property, rfl⟩
    · rintro _ ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have hc := f.ker.card_mul_index
  rw [index_ker, hrange] at hc
  calc
    2 ^ 10 = 2 ^ 7 * 2 ^ 3 := by norm_num
    _ ≤ Nat.card f.ker * Nat.card (actorImage Z R) := Nat.mul_le_mul hkcard himage
    _ = Nat.card R := hc

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
