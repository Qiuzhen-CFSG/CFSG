module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry
public import Theory.Mathieu.M22.Properties.HexadMaximal
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer


/-!
# Hexad pullbacks and their canonical local components

Pull a genuine M₂₂ hexad stabilizer back through K/O₂,Z(K). Restricting the
cover gives a surjection with kernel exactly O₂,Z(K) restricted to the
pullback. Composing with the native six-point action has the full inverse
image of the pointwise hexad kernel as its kernel, and quotient A₆.
That kernel is solvable, so the pullback's solvable residual is a genuine
C-component. Native maximality gives ordinary maximality of the pullback
in K. It and its residual are proper subgroups of K.

If T normalizes this hexad pullback, the residual belongs to L(KT,T).
Its C-component condition follows from relative normality of the pullback;
Sylow membership restricts from H; and the nontrivial two-core is inherited
from O₂(H), which lies in T. No local-family membership is assumed.

These constructions require only the displayed actual central-quotient
isomorphism. The triple-cover restriction, existence of a T-invariant hexad,
and source overlap placement are separate obligations. In particular, the
kernel of the six-point action is not asserted to be the two-core. The
separate SixParabolics leaf proves ordinary maximality and marking after
supplying actual A₆ or S₆ quotient coordinates and their kernel containment.

Source: Aschbacher--Smith, 13.8.21(2), combined manuscript of 1 March 2004,
printed p.956 (PDF p.973), using the native hexad geometry of E.4.3.
-/

@[expose] public section

open scoped Pointwise
open Subgroup Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics

variable {G : Type*} [Group G]

/-- The literal map K → K/O₂,Z(K) → M₂₂. -/
noncomputable def mathieuProjection (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) : K →* M22 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 K)))

/-- The supplied central-quotient identification gives a surjective map. -/
theorem mathieuProjection_surjective (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) :
    Function.Surjective (mathieuProjection K e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The kernel is O₂,Z(K), not merely O₂(K). -/
theorem mathieuProjection_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) :
    (mathieuProjection K e).ker = centralPreimage (pCore 2 K) := by
  dsimp [mathieuProjection]
  rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

/-- The full inverse image of an actual hexad stabilizer, as a subgroup of K. -/
noncomputable def hexadPreimage (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) : Subgroup K :=
  (MulAction.stabilizer M22 B).comap (mathieuProjection K e)

/-- The restriction of the central-quotient map to the hexad pullback. -/
noncomputable def hexadRestriction (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    hexadPreimage K e B →* MulAction.stabilizer M22 B :=
  ((mathieuProjection K e).comp (hexadPreimage K e B).subtype).codRestrict _
    (fun x => x.property)

/-- Every element of the actual hexad stabilizer lifts to the pullback. -/
theorem hexadRestriction_surjective (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    Function.Surjective (hexadRestriction K e B) := by
  intro y
  obtain ⟨x, hx⟩ := mathieuProjection_surjective K e y.val
  exact ⟨⟨x, by change mathieuProjection K e x ∈ MulAction.stabilizer M22 B; rw [hx]; exact y.property⟩,
    Subtype.ext hx⟩

/-- The restricted covering kernel is the original central preimage, restricted to the pullback. -/
theorem hexadRestriction_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    (hexadRestriction K e B).ker =
      (centralPreimage (pCore 2 K)).subgroupOf (hexadPreimage K e B) := by
  ext x
  change hexadRestriction K e B x = 1 ↔ _
  rw [Subtype.ext_iff]
  change mathieuProjection K e x.val = 1 ↔ _
  rw [← MonoidHom.mem_ker, mathieuProjection_ker]
  rfl

/-- The exact quotient of the pullback by the restricted covering kernel. -/
noncomputable def hexadRestrictionQuotient (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    (hexadPreimage K e B ⧸
      (centralPreimage (pCore 2 K)).subgroupOf (hexadPreimage K e B)) ≃*
        MulAction.stabilizer M22 B :=
  (QuotientGroup.quotientMulEquivOfEq (hexadRestriction_ker K e B).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (hexadRestriction_surjective K e B))

/-- The actual six-point action after lifting the native hexad stabilizer. -/
noncomputable def hexadSixProjection (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    hexadPreimage K e B →* alternatingGroup (Fin 6) :=
  (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
    ((QuotientGroup.mk' (m22SetAction B).ker).comp (hexadRestriction K e B))

/-- The lifted six-point action has the full alternating image. -/
theorem hexadSixProjection_surjective (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (hexadSixProjection K e hB) :=
  (m22HexadQuotientAlternatingEquiv hB).surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (hexadRestriction_surjective K e B))

/-- On representatives this is precisely the native labelled hexad action. -/
theorem hexadSixProjection_apply (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (x : hexadPreimage K e B) :
    (hexadSixProjection K e hB x : Equiv.Perm (Fin 6)) =
      m22HexadAction hB (hexadRestriction K e B x) := rfl

/-- The full kernel includes the preimage of the native elementary group of order sixteen. -/
theorem hexadSixProjection_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadSixProjection K e hB).ker =
      (m22SetAction B).ker.comap (hexadRestriction K e B) := by
  dsimp [hexadSixProjection]
  rw [MonoidHom.ker_mulEquiv_comp, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- Kernel membership means fixing every point of this actual hexad. -/
theorem mem_hexadSixProjection_ker (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (x : hexadPreimage K e B) :
    x ∈ (hexadSixProjection K e hB).ker ↔
      ∀ a ∈ B, mathieuProjection K e x.val • a = a := by
  rw [hexadSixProjection_ker]
  exact mem_m22SetAction_ker B (hexadRestriction K e B x)

/-- The first isomorphism theorem for the lifted six-point action. -/
noncomputable def hexadSixQuotient (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadPreimage K e B ⧸ (hexadSixProjection K e hB).ker) ≃*
      alternatingGroup (Fin 6) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (hexadSixProjection_surjective K e hB)

/-- Ordinary maximality of the native hexad stabilizer lifts through the surjection. -/
theorem hexadPreimage_isCoatom (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsCoatom (hexadPreimage K e B) :=
  isCoatom_comap_of_surjective (mathieuProjection_surjective K e)
    (m22_hexad_stabilizer_isCoatom B hB)

variable [Finite G]

private theorem centralPreimage_solvable (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable (centralPreimage (pCore 2 X)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
    infer_instance
  let : Group.IsSolvable (center (X ⧸ pCore 2 X)) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext ((mem_center_iff.mp b.property) a.val))
  exact isSolvable_comap_of_solvable_ker q (center (X ⧸ pCore 2 X))

/-- The six-point kernel is solvable: its two successive images are central and elementary abelian. -/
theorem hexadSixProjection_ker_solvable (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Group.IsSolvable (hexadSixProjection K e hB).ker := by
  let := centralPreimage_solvable K
  let : Group.IsSolvable (hexadRestriction K e B).ker := by
    rw [hexadRestriction_ker]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show centralPreimage (pCore 2 K) ≤
        hexadPreimage K e B from by
          rw [← mathieuProjection_ker K e]
          exact ker_le_comap _ _)).toMonoidHom)
      (subgroupOfEquivOfLe _).injective
  let : Group.IsNilpotent (m22SetAction B).ker :=
    (IsPGroup.of_card (p := 2) (n := 4) (m22HexadKernel_card hB)).isNilpotent
  rw [hexadSixProjection_ker]
  exact isSolvable_comap_of_solvable_ker _ _

private theorem residual_cComponent_of_simple_quotient
    {X S : Type*} [Group X] [Finite X] [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (f : X →* S) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    (solvableResidual X).IsCComponent := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsSimpleGroup (X ⧸ f.ker) := e.isSimpleGroup
  let : Group.IsPerfect (X ⧸ f.ker) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (⊤ : Subgroup (X ⧸ f.ker)) := (topEquiv).isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (X ⧸ f.ker)) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := X ⧸ f.ker)).symm.toMonoidHom)
      (topEquiv (G := X ⧸ f.ker)).symm.surjective
  have ht : (⊤ : Subgroup (X ⧸ f.ker)).IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect (normal_top.isSubnormal)
  have h := ht.solvableResidual_preimage f.ker
  rw [comap_top] at h
  rw [map_solvableResidual_eq _ (topEquiv (G := X)).surjective] at h
  exact h

/-- The solvable residual of the pullback is its canonical C-component. -/
theorem hexadResidual_isCComponent (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (solvableResidual (hexadPreimage K e B)).IsCComponent := by
  let := hexadSixProjection_ker_solvable K e hB
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact residual_cComponent_of_simple_quotient _ (hexadSixProjection_surjective K e hB)

/-- The canonical C-component still surjects onto the alternating six-point image. -/
theorem hexadResidual_image (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (solvableResidual (hexadPreimage K e B)).map (hexadSixProjection K e hB) = ⊤ := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rw [map_solvableResidual_eq _ (hexadSixProjection_surjective K e hB),
    solvableResidual_eq_top]

/-- The same hexad pullback, embedded in the ambient group G. -/
noncomputable def hexadLift (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) : Subgroup G :=
  (hexadPreimage K e B).map K.subtype

omit [Finite G] in
/-- The actual hexad pullback lies in K. -/
theorem hexadLift_le (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    hexadLift K e B ≤ K := map_subtype_le _

omit [Finite G] in
/-- The actual hexad pullback is proper in K. -/
theorem hexadLift_lt (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) : hexadLift K e B < K := by
  refine lt_of_le_of_ne (hexadLift_le K e B) ?_
  intro he
  have hm := congrArg (comap K.subtype) he
  change ((hexadPreimage K e B).map K.subtype).comap K.subtype = K.comap K.subtype at hm
  rw [comap_map_eq_self_of_injective K.subtype_injective] at hm
  have htop : K.comap K.subtype = ⊤ := by
    ext x
    exact iff_of_true x.property trivial
  exact (hexadPreimage_isCoatom K e hB).1 (hm.trans htop)

/-- The canonical hexad C-component, embedded in G. -/
noncomputable def hexadResidualIn (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) : Subgroup G :=
  (solvableResidual (hexadLift K e B)).map (hexadLift K e B).subtype

omit [Finite G] in
/-- The constructed component lies in the original component K. -/
theorem hexadResidualIn_le (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) (B : Finset (Fin 22)) :
    hexadResidualIn K e B ≤ K := (map_subtype_le _).trans (hexadLift_le K e B)

omit [Finite G] in
/-- In the Mathieu branch the constructed component is strictly smaller than K. -/
theorem hexadResidualIn_lt (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) : hexadResidualIn K e B < K :=
  lt_of_le_of_lt (map_subtype_le _) (hexadLift_lt K e hB)

omit [Finite G] in
private theorem residualIn_mem_L {H E T : Subgroup G}
    (hH : H.pCoreIn 2 ≠ ⊥) (hEH : E ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hn : T ≤ normalizer (E : Set G)) (hc : (solvableResidual E).IsCComponent) :
    (solvableResidual E).map E.subtype ∈ Chapter1.L G T := by
  let U := E ⊔ T
  let E' := E.subgroupOf U
  have hEU : E ≤ U := le_sup_left
  have hUH : U ≤ H := sup_le hEH (Chapter1.isSylowIn_iff.mp hT).2.1
  let : E'.Normal := normal_subgroupOf_of_le_normalizer (sup_le E.le_normalizer hn)
  let e := subgroupOfEquivOfLe hEU
  have hc' := (hc.map_equiv e.symm).map_subtype (inferInstance : E'.Normal).isSubnormal
  have hm : ((solvableResidual E).map e.symm.toMonoidHom).map E'.subtype =
      ((solvableResidual E).map E.subtype).subgroupOf U := by
    rw [map_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_map.mpr ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, he⟩ := mem_map.mp hx
      exact ⟨y, hy, Subtype.ext he⟩
  rw [hm] at hc'
  have hcore : H.pCoreIn 2 ≤ U.pCoreIn 2 := by
    obtain ⟨P, hP⟩ := hT
    have hcoreT : H.pCoreIn 2 ≤ T := hP ▸ pCoreIn_le_sylow H P
    exact (le_inf (hcoreT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 hUH)
  exact Chapter1.mem_L_of_cComponent
    (fun he => hH (bot_unique (he ▸ hcore)))
    (hT.restrict le_sup_right hUH)
    ((map_subtype_le _).trans hEU) hc'

/-- A T-normalized hexad supplies all three defining local-family conditions. The choice of an invariant hexad remains explicit. -/
theorem hexadResidualIn_mem_LIn (H K T : Subgroup G)
    (hH : H.pCoreIn 2 ≠ ⊥) (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hn : T ≤ normalizer (hexadLift K e B : Set G)) :
    hexadResidualIn K e B ∈ Chapter1.LIn (K ⊔ T) T := by
  have hc := (hexadResidual_isCComponent K e hB).map_equiv
    ((hexadPreimage K e B).equivMapOfInjective K.subtype K.subtype_injective)
  rw [map_solvableResidual_eq _
    ((hexadPreimage K e B).equivMapOfInjective K.subtype K.subtype_injective).surjective] at hc
  exact ⟨(hexadResidualIn_le K e B).trans le_sup_left,
    residualIn_mem_L hH ((hexadLift_le K e B).trans hKH) hT hn hc⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
