module

public import Theory.GroupTheory.CharacteristicTwoNormalIndexTwo
public import Theory.Quasithin.EvenCharacteristic
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Characteristic two for both binary derived parabolics

Every element of the full first parabolic factors into its five-root core
and one of six explicit Levi representatives. The action of these six on
the right quaternion factor is faithful modulo inner automorphisms of the
core. Consequently an element centralizing the core belongs to the core.
The finite check uses the five binary root coordinates; the conjugation
identities themselves are inherited from the root calculation.

The actual commutator of G₂(2) has index two. Intersecting each full parabolic
with it gives a normal subgroup of index dividing two. The intrinsic
self-centralizing two-core condition passes to these intersections, proving
characteristic two for both restricted parabolics. The full second parabolic
calculation is reused from `EvenLocal.LongCore`.

Coverage of Sylow-containing maximal two-locals remains a separate geometric
assertion; these local calculations alone do not establish even characteristic
for the whole derived group.
Source: Aschbacher–Smith, Theorem 0.1.2(1), printed pp.3–4 and 481–482,
and Lemma 14.2.21, printed p.988. Root conventions follow the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

namespace Atlas.G2.BinaryParabolicPair
open Subgroup Atlas.G2.Explicit Atlas.SplitOctonion
open scoped Pointwise
open BinaryCore
set_option maxRecDepth 100000

private theorem model_ext (g h : Model (ZMod 2))
    (he : ∀ i j, g.val (basisVector i) j = h.val (basisVector i) j) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ (fun i => funext (he i))

private def leviElement : DihedralGroup 3 → Model (ZMod 2)
  | .r i => cubicActor ^ i.val
  | .sr i => shortRoot * cubicActor ^ i.val

set_option maxHeartbeats 2000000 in
private def leviHom : DihedralGroup 3 →* Model (ZMod 2) where
  toFun := leviElement
  map_one' := by change cubicActor ^ 0 = 1; exact pow_zero _
  map_mul' a b := by
    apply model_ext
    exact (by decide +kernel : ∀ (a b : DihedralGroup 3) i j,
      (leviElement (a*b)).val (basisVector i) j =
      (leviElement a * leviElement b).val (basisVector i) j) a b

private theorem levi_mem (d : DihedralGroup 3) : leviHom d ∈ firstParabolic := by
  cases d with
  | r i => exact firstParabolic.pow_mem cubicActor_mem i.val
  | sr i =>
    exact firstParabolic.mul_mem (unipotent_le_firstParabolic shortRoot_mem_unipotent)
      (firstParabolic.pow_mem cubicActor_mem i.val)

private theorem first_factor (g : firstParabolic) :
    ∃ (q : Coordinates) (d : DihedralGroup 3), g.val = embedding q * leviHom d := by
  have heq : firstParabolic = core ⊔ leviHom.range := by
    apply le_antisymm
    · apply sup_le
      · rw [unipotent_eq_core_sup]
        apply sup_le le_sup_left
        apply (Subgroup.closure_le _).mpr
        rintro x (rfl : x = shortRoot)
        apply mem_sup_right
        exact ⟨.sr 0, by change shortRoot * cubicActor ^ 0 = shortRoot; simp⟩
      · apply (Subgroup.closure_le _).mpr
        rintro x (rfl : x = weylS)
        apply mem_sup_right
        refine ⟨.sr 1, ?_⟩
        change shortRoot * cubicActor ^ 1 = weylS
        rw [pow_one, cubicActor, ← mul_assoc, ← pow_two, shortRoot_sq, one_mul]
    · exact sup_le core_le_firstParabolic (by rintro _ ⟨d,rfl⟩; exact levi_mem d)
  have hn : leviHom.range ≤ normalizer (core : Set (Model (ZMod 2))) := by
    rintro _ ⟨d,rfl⟩
    exact firstParabolic_normalizes_core (levi_mem d)
  have hg : g.val ∈ (core : Set (Model (ZMod 2))) * (leviHom.range : Set (Model (ZMod 2))) := by
    rw [← coe_mul_of_right_le_normalizer_left core leviHom.range hn, ← heq]
    exact g.prop
  obtain ⟨_,⟨q,rfl⟩,_,⟨d,rfl⟩,he⟩ := hg
  exact ⟨q,d,he.symm⟩

private def leviAction : DihedralGroup 3 → Coordinates → Coordinates
  | .r i => cubicConjugate^[i.val]
  | .sr i => shortConjugate ∘ cubicConjugate^[i.val]

private theorem levi_conjugate (d : DihedralGroup 3) (x : Coordinates) :
    leviHom d * embedding x * (leviHom d)⁻¹ = embedding (leviAction d x) := by
  have hp (n : ℕ) (x : Coordinates) :
      cubicActor ^ n * embedding x * (cubicActor ^ n)⁻¹ =
        embedding ((cubicConjugate^[n]) x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      calc
        _ = cubicActor * (cubicActor ^ n * embedding x * (cubicActor ^ n)⁻¹) *
            cubicActor⁻¹ := by group
        _ = embedding (cubicConjugate ((cubicConjugate^[n]) x)) := by
          rw [ih, cubic_conjugate]
        _ = _ := by rw [Function.iterate_succ_apply']
  cases d with
  | r i => exact hp i.val x
  | sr i =>
    change (shortRoot * cubicActor ^ i.val) * embedding x *
      (shortRoot * cubicActor ^ i.val)⁻¹ = _
    calc
      _ = shortRoot * (cubicActor ^ i.val * embedding x * (cubicActor ^ i.val)⁻¹) *
          shortRoot⁻¹ := by group
      _ = embedding (shortConjugate ((cubicConjugate^[i.val]) x)) := by
        rw [hp,short_conjugate]

set_option maxHeartbeats 2000000 in
private theorem levi_action_not_inner (q : Coordinates) (d : DihedralGroup 3)
    (hI : q * leviAction d rightI * q⁻¹ = rightI)
    (hJ : q * leviAction d rightJ * q⁻¹ = rightJ) : d = 1 := by
  exact (by decide +kernel : ∀ (q : Coordinates) (d : DihedralGroup 3),
    q * leviAction d rightI * q⁻¹ = rightI →
    q * leviAction d rightJ * q⁻¹ = rightJ → d = 1) q d hI hJ

private theorem first_core_selfCentralizing :
    centralizer (core.subgroupOf firstParabolic : Set firstParabolic) ≤
      core.subgroupOf firstParabolic := by
  intro g hg
  obtain ⟨q,d,he⟩ := first_factor g
  have hc (x : Coordinates) : q * leviAction d x * q⁻¹ = x := by
    apply embedding_injective
    rw [map_mul, map_mul, map_inv, ← levi_conjugate]
    have hx := congrArg Subtype.val (mem_centralizer_iff.mp hg
      ⟨embedding x,core_le_firstParabolic ⟨x,rfl⟩⟩ (show embedding x ∈ core from ⟨x,rfl⟩))
    change embedding x * g.val = g.val * embedding x at hx
    rw [he] at hx
    calc
      _ = (embedding q * leviHom d) * embedding x * (embedding q * leviHom d)⁻¹ := by group
      _ = embedding x := by rw [← hx]; group
  have hd := levi_action_not_inner q d (hc rightI) (hc rightJ)
  change g.val ∈ core
  rw [he,hd,map_one,mul_one]
  exact ⟨q,rfl⟩

/-- The full first binary parabolic has a self-centralizing intrinsic two-core. -/
public theorem firstParabolic_centralizer_pCore :
    centralizer (pCore 2 firstParabolic : Set firstParabolic) ≤ pCore 2 firstParabolic := by
  have he : pCore 2 firstParabolic = core.subgroupOf firstParabolic := by
    apply Subgroup.map_injective firstParabolic.subtype_injective
    change firstParabolic.pCoreIn 2 = _
    rw [firstParabolic_pCore, Subgroup.map_subgroupOf_eq_of_le core_le_firstParabolic]
  rw [he]
  exact first_core_selfCentralizing

private noncomputable def derivedFirstEquivRestriction :
    derivedFirst ≃* (DerivedModel.subgroupOf firstParabolic) where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The first parabolic restricted to the actual commutator has characteristic two. -/
public theorem derivedFirst_centralizer_pCore :
    centralizer (pCore 2 derivedFirst : Set derivedFirst) ≤ pCore 2 derivedFirst := by
  have hd : DerivedModel.index ∣ 2 := by
    change (commutator (Model (ZMod 2))).index ∣ 2
    rw [commutator_eq_longRootClosure, BinaryException.index_H]
  have hc := Subgroup.centralizer_pCore_le_of_normal_index_dvd_two
    firstParabolic_centralizer_pCore (DerivedModel.subgroupOf firstParabolic)
    ((DerivedModel.relIndex_dvd_index_of_normal firstParabolic).trans hd)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 derivedFirstEquivRestriction).mpr hc


private noncomputable def derivedSecondEquivRestriction :
    derivedSecond ≃* (DerivedModel.subgroupOf BinaryCore.secondParabolic) where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The second parabolic restricted to the actual derived group has characteristic two. -/
public theorem derivedSecond_centralizer_pCore :
    centralizer (pCore 2 derivedSecond : Set derivedSecond) ≤ pCore 2 derivedSecond := by
  have hd : DerivedModel.index ∣ 2 := by
    change (commutator (Model (ZMod 2))).index ∣ 2
    rw [commutator_eq_longRootClosure, BinaryException.index_H]
  have hcentral := Subgroup.centralizer_pCore_le_of_normal_index_dvd_two
    (show centralizer (pCore 2 BinaryCore.secondParabolic : Set BinaryCore.secondParabolic) ≤
      pCore 2 BinaryCore.secondParabolic from
      EvenLocal.parabolic₂_centralizer_pCore (F := ZMod 2))
    (DerivedModel.subgroupOf BinaryCore.secondParabolic)
    ((DerivedModel.relIndex_dvd_index_of_normal BinaryCore.secondParabolic).trans hd)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 derivedSecondEquivRestriction).mpr hcentral

end Atlas.G2.BinaryParabolicPair
