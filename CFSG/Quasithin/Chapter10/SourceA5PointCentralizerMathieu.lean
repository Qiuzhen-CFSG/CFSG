module

public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple
public import Theory.Mathieu.M23.Properties.A5Fixer

/-!
# The M₂₃ component in the A₅ point-centralizer argument

The image of the actual local component in a containing group's central
quotient still has an A₅ quotient: its central kernel lies in its two-core.
Thus its order is divisible by five. An elementary subgroup centralizing
that local component acts trivially on every perfect containing component
whose central quotient is the concrete M₂₃. The normalizer action and central
quotient map below are literal maps of the source subgroups.

This discharges the M₂₃ row of the quasisimple containing-component inspection
in Aschbacher–Smith 10.2.9, pp.750–751, using A.3.14, pp.48–49. The conclusion
applies to the original conjugate moved subgroup, without replacing it by an
arbitrary module or asserting an embedding from an isomorphism-class label.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G] {L I U : Subgroup G}

omit [Finite G] in
private theorem a5_center_le_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) : center L ≤ pCore 2 L := by
  intro z hz
  apply (QuotientGroup.eq_one_iff z).mp
  apply e.injective
  rw [e.map_one]
  have hc : e (QuotientGroup.mk' (pCore 2 L) z) ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) a
    rw [←hl]
    simpa only [Function.comp_apply,map_mul] using
      congrArg (fun x : L => e (QuotientGroup.mk' (pCore 2 L) x))
        (mem_center_iff.mp hz l)
  rwa [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc

/-- The literal image of the local component has an A₅ quotient after dividing
out the center of its containing component. -/
theorem source_a5_containing_center_image_card_dvd
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I) :
    60 ∣ Nat.card ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) := by
  let A := L.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change q (inclusion hLI l) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp hh
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  have hp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hk.trans (a5_center_le_core e))
  let d : ((A.map q) ⧸ pCore 2 (A.map q)) ≃* alternatingGroup (Fin 5) :=
    (f.pCoreQuotientEquiv hf hp).symm.trans e
  have hd := (pCore 2 (A.map q)).index_dvd_card
  change Nat.card ((A.map q) ⧸ pCore 2 (A.map q)) ∣ Nat.card (A.map q) at hd
  have hcard : Nat.card ((A.map q) ⧸ pCore 2 (A.map q)) = 60 := by
    rw [Nat.card_congr d.toEquiv, nat_card_alternatingGroup]
    norm_num
  rw [hcard] at hd
  exact hd

/-- An elementary subgroup fixing the actual A₅ local component centralizes a
perfect containing component of central-quotient type M₂₃. -/
theorem source_a5_m23_component_centralized
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLI : L ≤ I) [Group.IsPerfect I]
    (eI : I ⧸ center I ≃* Sporadic.Mathieu.M23)
    [IsElementaryAbelian 2 U]
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  have h5 : 5 ∣ Nat.card ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) :=
    (by decide : 5 ∣ 60).trans (source_a5_containing_center_image_card_dvd eL hLI)
  intro u hu
  let n : normalizer (I : Set G) := ⟨u,hUN hu⟩
  let a : MulAut I := I.normalizerMonoidHom n
  have hn : n ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu)
  have ha : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom n) ^ 2 = 1
    rw [← map_pow, hn, map_one]
  have hf : ∀ l ∈ L.subgroupOf I, a l = l := by
    intro l hl
    apply Subtype.ext
    change u * l.val * u⁻¹ = l.val
    exact mul_inv_eq_iff_eq_mul.mpr ((hUL hu l.val hl).symm)
  have he := Sporadic.Mathieu.m23_perfect_cover_involutory_fixer_eq_one
    eI (L.subgroupOf I) h5 a ha hf
  intro i hi
  have hh := congrArg (fun f : MulAut I => (f ⟨i,hi⟩ : G)) he
  change u * i * u⁻¹ = i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The source point-centralizer hypotheses supply precisely the normalizer
condition of the M₂₃ calculation, for the original elementary subgroup U. -/
theorem source_a5_m23_point_component_centralized
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLI : L ≤ I) [Group.IsPerfect I]
    (eI : I ⧸ center I ≃* Sporadic.Mathieu.M23)
    [IsElementaryAbelian 2 U] (v : G)
    (hUv : U ≤ centralizer ({v} : Set G))
    (hIN : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hUL : U ≤ centralizer (L : Set G)) : U ≤ centralizer (I : Set G) :=
  source_a5_m23_component_centralized eL hLI eI (hUv.trans hIN) hUL

end CFSG.Quasithin.Chapter10
