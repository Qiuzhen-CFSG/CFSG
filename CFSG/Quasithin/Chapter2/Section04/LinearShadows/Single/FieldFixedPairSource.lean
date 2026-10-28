module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource
public import Theory.GroupTheory.CentralizerResidualProducts
public import Theory.ElementaryAbelian.Injective

/-!
# The fixed maximum elementary pair in the original single block

Every elementary subgroup of the original Thompson group lies in one of
its two elementary factors. Intersecting with the actual involution
centralizer preserves this dichotomy. An outside element centralizing the
involution exchanges the two fixed factors, so they have the same order
and are precisely the maximum elementary subgroups of the fixed group.

This supplies the literal pair used in the Sylow-centralizer argument,
without assuming fixed-block recognition or that the pair generates.
Source: Aschbacher–Smith, 2.4.23(4), printed p.537.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_fixed_maximum_pair
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (s : G)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxs : x ∈ centralizer ({s} : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Us := sourceModule (d.block.map d.H.subtype) ⊓ centralizer ({s} : Set G)
    Stellmacher.elementaryAbelianMaxSubgroups (R ⊓ centralizer ({s} : Set G)) =
      {Us, Us.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let U := sourceModule L
  let C := centralizer ({s} : Set G)
  let Us := U ⊓ C
  let Rs := R ⊓ C
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  let Vs := Us.map e.toMonoidHom
  have hes : e s=s := by
    change x⁻¹*s*(x⁻¹)⁻¹=s
    exact mul_inv_eq_iff_eq_mul.mpr (Commute.inv_left
      (mem_centralizer_singleton_iff.mp hxs)).eq
  have hC : C.map e.toMonoidHom=C := by
    change (centralizer ({s}:Set G)).map e.toMonoidHom=centralizer ({s}:Set G)
    rw [Theory.GroupTheory.map_centralizer_singleton,hes]
  have hVs : V ⊓ C=Vs := by
    change U.map e.toMonoidHom ⊓ C=(U⊓C).map e.toMonoidHom
    rw [map_inf _ _ _ e.injective,hC]
  have hpair := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hgen : U⊔V=R := (hpair.2.2.2 x hxT hxS).1.symm
  have hUs : Us≤Rs := inf_le_inf_right C (le_sup_left.trans_eq hgen)
  have hVsR : Vs≤Rs := hVs ▸ inf_le_inf_right C (le_sup_right.trans_eq hgen)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  let : IsElementaryAbelian 2 (ChapterC.blockU L) := hK.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 Us := IsElementaryAbelian.of_injective
    (inclusion (show Us≤U from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Vs := IsElementaryAbelian.map e.toMonoidHom
  have hcard : Nat.card Vs=Nat.card Us := card_map_of_injective e.injective
  have htwo (E : Subgroup G) (hER : E≤Rs) (hE : IsElementaryAbelian 2 E) : E≤Us ∨ E≤Vs := by
    rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).2
      E (hER.trans inf_le_left) hE with hEU | hEV
    · exact Or.inl (le_inf hEU (hER.trans inf_le_right))
    · exact Or.inr (hVs ▸ le_inf hEV (hER.trans inf_le_right))
  have hbound (E : Subgroup G) (hER : E≤Rs) (hE : IsElementaryAbelian 2 E) :
      Nat.card E≤Nat.card Us := by
    rcases htwo E hER hE with he | he
    · exact card_le_of_le he
    · exact (card_le_of_le he).trans_eq hcard
  change Stellmacher.elementaryAbelianMaxSubgroups Rs={Us,Vs}
  ext E
  constructor
  · intro hE
    rcases htwo E hE.1 hE.2.1 with he | he
    · exact Set.mem_insert_iff.mpr (Or.inl (eq_of_le_of_card_ge he (hE.2.2 Us hUs inferInstance)))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
        (eq_of_le_of_card_ge he (hE.2.2 Vs hVsR inferInstance))))
  · rintro (rfl|rfl)
    · exact ⟨hUs,inferInstance,hbound⟩
    · exact ⟨hVsR,inferInstance,fun E hER hE => (hbound E hER hE).trans_eq hcard.symm⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
