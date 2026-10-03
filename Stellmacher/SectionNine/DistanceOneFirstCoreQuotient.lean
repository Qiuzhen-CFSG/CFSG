module

public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Theory.GroupTheory.WreathTwoSylowModel


/-!
# The first core quotient and Sylow order after core equality

At critical distance one, assume the faithful initial-center conclusion and
that the initial core equals that center. Characteristic two makes the
centralizer of the center inside its vertex stabilizer exactly the core.
Consequently the actual faithful quotient is also the quotient by the core.

The faithful center has order sixteen. Map the actual edge Sylow through this
quotient: its image is a Sylow two-subgroup of the concrete SL2(2) wreath C2,
hence a dihedral group of order eight. Its kernel is the entire initial core.
The subgroup index formula gives order128 for the distinguished edge Sylow.

This proves the first quotient and Sylow-order calculations immediately after
Stellmacher (9.1), relation (11), Journal of Algebra190 (1997), p.48. The core
equality is explicit: this module neither assumes the local conclusion nor
proves the separate chief-factor argument that supplies this equality.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

public theorem distance_one_first_core_quotient_of_core_eq_center
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hcore : QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2 ∧ Nat.card T = 2 ^ 7 := by
  let first := GAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a
  let Z := ZAt ctx.Γ ctx.criticalPath.a
  change Q = Z at hcore
  have hQT : Q ≤ T := (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨hTfirst, P, hP⟩ := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  change T ≤ first at hTfirst
  have hQfirst : Q ≤ first := hQT.trans hTfirst
  have hZfirst : Z ≤ first := hcore ▸ hQfirst
  have hn : ctx.criticalPath.a' ∈ CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hlength)
  let _ : IsElementaryAbelian 2 Z :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hn
  have hchar : IsCharacteristicTwoType first :=
    (SevenSix.edge_characteristic_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hcentral : first ⊓ Subgroup.centralizer (Z : Set G) = Q := by
    apply le_antisymm
    · intro x hx
      have hc : (⟨x,hx.1⟩ : first) ∈ Subgroup.centralizer (pCore 2 first : Set first) := by
        intro q hq
        apply Subtype.ext
        apply Subgroup.mem_centralizer_iff.mp hx.2
        rw [← hcore]
        change (q : G) ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a
        rw [ctx.Γ.twoCoreAt_def]
        exact Subgroup.mem_map_of_mem _ hq
      change x ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a
      rw [ctx.Γ.twoCoreAt_def]
      exact Subgroup.mem_map_of_mem _ (hchar hc)
    · intro x hx
      have hxZ : x ∈ Z := hcore ▸ hx
      exact ⟨hZfirst hxZ, fun z hz => setLike_mul_comm (s := Z) hz hxZ⟩
  obtain ⟨f,hf,hker⟩ := hfaithful.2
  change f.ker = (first ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf first at hker
  rw [hcentral] at hker
  refine ⟨⟨f,hf,hker⟩, ?_⟩
  have hkernelcard : Nat.card f.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQfirst).toEquiv]
    rw [show Q = Z from hcore]
    exact hfaithful.1
  have hkernelP : f.ker ≤ (P : Subgroup first) := by
    intro x hx
    rw [hker] at hx
    have ht := hQT hx
    rw [← hP] at ht
    obtain ⟨y,hy,hyx⟩ := ht
    exact (show y=x from Subtype.ext hyx) ▸ hy
  have himagecard : Nat.card ((P : Subgroup first).map f) = 8 := by
    obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four (P.mapSurjective hf)
    change Nat.card (P.mapSurjective hf) = 8
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcard := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup first) f.ker
    (P : Subgroup first) bot_le hkernelP
  simp only [Subgroup.relIndex_bot_left, Subgroup.relIndex_ker] at hcard
  rw [hkernelcard,himagecard] at hcard
  have hPT : Nat.card P = Nat.card T := by
    exact (Subgroup.card_map_of_injective (K := (P : Subgroup first))
      first.subtype_injective).symm.trans (congrArg (fun J : Subgroup G => Nat.card J) hP)
  rw [← hPT]
  exact hcard.symm
end Stellmacher.SectionNine
