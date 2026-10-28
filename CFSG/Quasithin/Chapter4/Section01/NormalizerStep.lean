module
public import CFSG.Quasithin.Chapter4.Section01.CoreContainment
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.TwoLocalUniquenessControl
import Mathlib.Tactic
/-!
# The common normalizer-growth step in pushing up

For an intermediate A inside M, its section centralizer is normal in A.
The Sylow normalizer therefore covers A by Frattini. The subgroup X intersect A
normalizes that Sylow because its commutators lie in O2(X) intersect A, a normal
two-subgroup already contained in the Sylow. This makes the new normalizer an
eta member preserving both parts of the source comparison relation.
Source: Aschbacher--Smith,4.1.4(2),(4), printed p.607.
-/

public section
namespace CFSG.Quasithin.Chapter4
open Subgroup
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G]

private theorem frattini_factorization {C M : Subgroup G} (hCM : C ≤ M)
    (hMC : M ≤ normalizer (C : Set G)) (S : Sylow 2 C) :
    (M : Set G) = (C : Set G) *
      ((M ⊓ normalizer ((S : Subgroup C).map C.subtype : Set G)) : Set G) := by
  let C' := C.subgroupOf M
  let : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr hMC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCM).symm
  let S' : Sylow 2 C' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((S' : Subgroup C').map C'.subtype).map M.subtype =
      (S : Subgroup C).map C.subtype := by
    change (((S : Subgroup C).map e.toMonoidHom).map C'.subtype).map M.subtype = _
    rw [map_map, map_map]
    rfl
  have hfr : C' ⊔ normalizer ((S' : Subgroup C').map C'.subtype : Set M) = ⊤ := by
    rw [sup_comm]
    exact S'.normalizer_sup_eq_top
  apply Set.Subset.antisymm
  · intro m hm
    have hm' : (⟨m, hm⟩ : M) ∈ C' ⊔
        normalizer ((S' : Subgroup C').map C'.subtype : Set M) := by rw [hfr]; trivial
    obtain ⟨c, hc, n, hn, he⟩ := mem_sup_of_normal_left.mp hm'
    refine ⟨c, hc, n, ⟨n.property, ?_⟩, congrArg Subtype.val he⟩
    have hh := ((S' : Subgroup C').map C'.subtype).le_normalizer_map M.subtype
      (mem_map_of_mem M.subtype hn)
    rwa [hmap] at hh
  · rintro _ ⟨c, hc, n, hn, rfl⟩
    exact M.mul_mem (hCM hc) hn.1

omit [Finite G] in
/-- Normalized two-subgroups are contained in the literal embedded Sylow. -/
private theorem normal_two_le_sylow {C Q : Subgroup G}
    (hp : IsPGroup 2 Q) (hq : Q ≤ C) (hn : C ≤ normalizer (Q : Set G))
    (S : Sylow 2 C) : Q ≤ (S : Subgroup C).map C.subtype :=
  (le_pCoreIn_of_normalizes hp hq hn).trans (pCoreIn_le_sylow C S)

/-- The normalizer-growth step preserves the source action intersection and
covers the intermediate group through its actual section centralizer. -/
theorem sectionSylow_normalizer_data {M X A : Subgroup G}
    (hAM : A ≤ M) (hMX : M ≤ normalizer (X : Set G))
    (S : Sylow 2 (sectionCentralizerIn A X)) :
    let R1 := (S : Subgroup (sectionCentralizerIn A X)).map
      (sectionCentralizerIn A X).subtype
    X ⊓ A ≤ normalizer (R1 : Set G) ∧
      (A : Set G) = ((A ⊓ normalizer (R1 : Set G)) : Set G) *
        (sectionCentralizerIn A X : Set G) ∧
      R1 ≤ (A ⊓ normalizer (R1 : Set G)).pCoreIn 2 := by
  let C := sectionCentralizerIn A X
  let R1 := (S : Subgroup C).map C.subtype
  have hRC : R1 ≤ C := map_subtype_le _
  have hRA : R1 ≤ A := hRC.trans inf_le_left
  have hAQ : A ≤ normalizer (X.pCoreIn 2 ⊓ A : Set G) :=
    (le_inf ((hAM.trans hMX).trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))) A.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hQC : X.pCoreIn 2 ⊓ A ≤ C := by
    refine le_inf inf_le_right ?_
    exact inf_le_left.trans ((componentCore_le_sectionCentralizer (M := X) le_rfl).trans inf_le_right)
  have hQR : X.pCoreIn 2 ⊓ A ≤ R1 := normal_two_le_sylow
    ((isPGroup_pCoreIn 2 X).to_le inf_le_left) hQC (inf_le_left.trans hAQ) S
  have hc : ⁅R1,X ⊓ A⁆ ≤ X.pCoreIn 2 ⊓ A := by
    refine le_inf ?_ ((commutator_le_sup R1 (X ⊓ A)).trans (sup_le hRA inf_le_right))
    exact (commutator_mono (hRC.trans inf_le_right) inf_le_left).trans
      ((le_sectionCentralizer_iff (sectionCentralizer X) X).mp le_rfl).2
  have hAC := sectionCentralizerIn_normalized (hAM.trans hMX)
  refine ⟨le_normalizer_iff_commutator_le_left.mpr (hc.trans hQR),?_,?_⟩
  · exact (frattini_factorization inf_le_left hAC S).trans
      (set_mul_normalizer_comm (A ⊓ normalizer (R1 : Set G) : Set G) C
        (inf_le_left.trans hAC)).symm
  · exact le_pCoreIn_of_normalizes (S.isPGroup'.map C.subtype)
      (le_inf hRA R1.le_normalizer) inf_le_right

/-- The same normalizer is an eta member above the original core and
component intersection. This is the common step in4.1.4(2) and(4). -/
theorem sectionSylow_normalizer_eta {M X Mminus I A : Subgroup G}
    (hMX : M ≤ normalizer (X : Set G)) (hminus : Mminus ≤ M)
    (hI : I ∈ eta M X Mminus) (hIA : I ≤ A) (hA : A ≤ Mminus)
    (hAN : A ≤ normalizer (I.pCoreIn 2 : Set G))
    (hRC : I.pCoreIn 2 ≤ sectionCentralizerIn M X)
    (S : Sylow 2 (sectionCentralizerIn A X)) :
    let R1 := (S : Subgroup (sectionCentralizerIn A X)).map
      (sectionCentralizerIn A X).subtype
    (A ⊓ normalizer (R1 : Set G)) ∈ eta M X Mminus ∧
      PushLE X I (A ⊓ normalizer (R1 : Set G)) ∧ I.pCoreIn 2 ≤ R1 ∧
      R1 ≤ (A ⊓ normalizer (R1 : Set G)).pCoreIn 2 := by
  let C := sectionCentralizerIn A X
  let R1 := (S : Subgroup C).map C.subtype
  obtain ⟨hXN,hcover,hcore⟩ := sectionSylow_normalizer_data (hA.trans hminus) hMX S
  have hRI : I.pCoreIn 2 ≤ I := pCoreIn_le 2 I
  have hR1 : I.pCoreIn 2 ≤ R1 := normal_two_le_sylow (isPGroup_pCoreIn 2 I)
    (le_inf (hRI.trans hIA) (hRC.trans inf_le_right)) (inf_le_left.trans hAN) S
  have hne : (A ⊓ normalizer (R1 : Set G)).pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hI.2.2.2 (bot_unique (he ▸ hR1.trans hcore))
  have hplus : (X ⊓ A : Set G) ⊆ (A ⊓ normalizer (R1 : Set G) : Set G) *
      (X.pCoreIn 2 : Set G) := by
    intro x hx
    exact ⟨x,⟨hx.2,hXN hx⟩,1,(X.pCoreIn 2).one_mem,mul_one x⟩
  refine ⟨lemma_4_1_3_1 hI hIA hA inf_le_left hne hcover hplus hminus,?_,hR1,hcore⟩
  exact ⟨hR1.trans hcore,fun x hx => ⟨⟨hIA hx.1,hXN ⟨hx.2,hIA hx.1⟩⟩,hx.2⟩⟩
end CFSG.Quasithin.Chapter4
