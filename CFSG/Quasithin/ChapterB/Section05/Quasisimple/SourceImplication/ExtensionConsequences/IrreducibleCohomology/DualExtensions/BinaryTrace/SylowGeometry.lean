module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.BinaryTrace.Coordinates
public import Theory.ElementaryAbelian.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Trace-one stabilizers in the full binary octonion group

Normalize a trace-one octonion by subtracting multiples of the identity and the
first basis vector; both are fixed by the positive-root subgroup. Its elementary
abelian stabilizer embeds either into the four-element parameter plane or into
one of the four-element sets certified in `Coordinates`. Sylow conjugacy extends
the bound to the full G₂(2) actor, with the octonion conjugated by the same actual
linear automorphism. No assertion identifying this actor with its derived
subgroup is used.

This proves the geometric obstruction needed for Aschbacher–Smith, B.5.1(5)
and I.1.7(b), printed pp.102–103 and 408–409; compare B.4.6(3),(13), pp.88–90.
The split-octonion coordinates and Sylow parametrization are from the licensed
ATLAS imports; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions.BinaryTrace

private theorem fixes_basis_zero (t : Params) : (unipotentProduct t).val (basisVector 0) = basisVector 0 := by
  ext i
  fin_cases i <;> simp [unipotentProduct, rootA,rootB,rootC,rootD,rootE,rootF,
    rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
    rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
    rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply, basisVector]

private theorem normal_decomposition (x : Carrier (ZMod 2)) (ht : trace x = 1) :
    x = normal ![x 1,x 2,x 5,x 6,x 7] + x 0 • basisVector 0 + x 4 • unit := by
  have ht' : x 3 = 1 + x 4 := by
    have h := congrArg (fun a => a + x 4) ht
    simpa [trace, add_assoc, CharTwo.add_self_eq_zero] using h
  ext i
  fin_cases i <;> simp [normal, basisVector, unit, ht', Matrix.vecHead, Matrix.vecTail]

private theorem fixes_of_scalar (x : Carrier (ZMod 2)) (ht : trace x = 1) (t : Params)
    (hx : ∃ c : ZMod 2, c • unit = (unipotentProduct t).val x - x) :
    fixes ![x 1,x 2,x 5,x 6,x 7] t := by
  obtain ⟨c,hc⟩ := hx
  have hnorm := normal_decomposition x ht
  have hh : c • unit = (unipotentProduct t).val (normal ![x 1,x 2,x 5,x 6,x 7]) -
      normal ![x 1,x 2,x 5,x 6,x 7] := by
    conv_rhs at hc => rw [hnorm]
    simpa only [map_add, map_smul, fixes_basis_zero, automorphism_unit,
      add_sub_add_right_eq_sub] using hc
  have hi (i : Fin 8) (hunit : (unit : Carrier (ZMod 2)) i = 0) :
      (unipotentProduct t).val (normal ![x 1,x 2,x 5,x 6,x 7]) i =
        normal ![x 1,x 2,x 5,x 6,x 7] i := by
    apply sub_eq_zero.mp
    have h := congrFun hh i
    simpa only [Pi.smul_apply, Pi.sub_apply, hunit, smul_zero] using h.symm
  exact ⟨hi 0 rfl, hi 1 rfl, hi 2 rfl, hi 5 rfl, hi 6 rfl⟩

private theorem sylow_card_le_four (A : Subgroup (Model (ZMod 2))) [IsElementaryAbelian 2 A]
    (hAU : A ≤ unipotent) (x : Carrier (ZMod 2)) (ht : trace x = 1)
    (hx : ∀ a ∈ A, ∃ c : ZMod 2, c • unit = a.val x - x) : Nat.card A ≤ 4 := by
  classical
  let code : A → Params := fun a => unipotentParameters a.val
  have decode (a : A) : unipotentProduct (code a) = a.val := by
    have ha := hAU a.property
    rw [unipotent_eq_range] at ha
    obtain ⟨t,ht⟩ := ha
    change unipotentProduct (unipotentParameters a.val) = a.val
    rw [← ht, unipotentParameters_product]
  have hinj : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    rw [← decode a, ← decode b, hab]
  have hsq (a : A) : shortProduct (code a) (code a) = 0 := by
    apply unipotentProduct_injective
    rw [shortProduct_eq, ← unipotentProduct_mul, decode, unipotentProduct_zero, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian a.val a.property
  have hcomm (a b : A) : shortProduct (code a) (code b) = shortProduct (code b) (code a) := by
    apply unipotentProduct_injective
    rw [shortProduct_eq, shortProduct_eq, ← unipotentProduct_mul,
      ← unipotentProduct_mul, decode, decode]
    exact congrArg Subtype.val (mul_comm a b)
  have hfix (a : A) : fixes ![x 1,x 2,x 5,x 6,x 7] (code a) := by
    apply fixes_of_scalar x ht
    rw [decode]
    exact hx a.val a.property
  by_cases hplane : ∀ a : A, plane (code a)
  · let f : A → ↥planeCodes := fun a => ⟨code a, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hplane a⟩⟩
    have hcard := Nat.card_le_card_of_injective f (fun a b h => hinj (congrArg Subtype.val h))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, planeCodes_card] using hcard
  · obtain ⟨a,ha⟩ := not_forall.mp hplane
    let f : A → ↥(candidates ![x 1,x 2,x 5,x 6,x 7] (code a)) :=
      fun b => ⟨code b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsq b, hfix b, hcomm a b⟩⟩
    have hcard := Nat.card_le_card_of_injective f (fun b c h => hinj (congrArg Subtype.val h))
    have hb := bound ![x 1,x 2,x 5,x 6,x 7] (code a) ha (hsq a) (hfix a)
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
    exact hcard.trans hb

/-- An elementary abelian subgroup fixing a trace-one octonion modulo scalars
has order at most four, in the full binary octonion automorphism group. -/
theorem card_le_four (A : Subgroup (Model (ZMod 2))) [IsElementaryAbelian 2 A]
    (x : Carrier (ZMod 2)) (ht : trace x = 1)
    (hx : ∀ a ∈ A, ∃ c : ZMod 2, c • unit = a.val x - x) : Nat.card A ≤ 4 := by
  classical
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model (ZMod 2)) S BinaryParabolicPair.commonSylow
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBU : B ≤ unipotent := by
    rw [← BinaryParabolicPair.commonSylow_eq, ← hg, Sylow.coe_subgroup_smul,
      Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hAS
  have hfix : ∀ b ∈ B, ∃ c : ZMod 2, c • unit = b.val (g.val x) - g.val x := by
    rintro b ⟨a,ha,rfl⟩
    obtain ⟨c,hc⟩ := hx a ha
    refine ⟨c, ?_⟩
    have hh := congrArg g.val hc
    rw [map_sub, automorphism_scalar] at hh
    change c • unit = g.val (a.val (g.val.symm (g.val x))) - g.val x
    rw [g.val.symm_apply_apply]
    exact hh
  have hb := sylow_card_le_four B hBU (g.val x) (by simpa using ht) hfix
  rw [show Nat.card B = Nat.card A from Subgroup.card_map_of_injective (MulAut.conj g).injective] at hb
  exact hb

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions.BinaryTrace
