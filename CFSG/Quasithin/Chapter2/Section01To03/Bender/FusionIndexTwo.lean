module

public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.FusionInvariantTransfer
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionLocalControl

/-!
# The actual index-two contradiction in the Bender branch

If M contains a Sylow two-subgroup of a nonsolvable simple group and
controls fusion of its two-elements, M has no subgroup of index two.
Restrict the binary quotient character to the ambient Sylow subgroup.
Fusion invariance and transfer make that restriction trivial. The Sylow
subgroup would then lie inside the index-two subgroup, contradicting its
odd index. No choice of an outside involution and no stronger generalized
Thompson transfer theorem is needed.

The application uses the constructed local-control witness of Proposition
2.2.2. Every surjective image of M, in particular its faithful action image
on the selected elementary abelian subgroup, also has no subgroup of
index two. This discharges the transfer endgame on printed p.520.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.BenderFusion

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The fusion package kills every index-two subgroup of M. -/
theorem LocalControlWitness.index_ne_two [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) {T : Sylow 2 G} {M : Subgroup G}
    (w : LocalControlWitness T M) (hTM : (T : Subgroup G) ≤ M)
    (K : Subgroup M) : K.index ≠ 2 := by
  intro hK
  let : K.Normal := K.normal_of_index_eq_two hK
  have hcard : Nat.card (M ⧸ K) = 2 := hK
  let : IsCyclic (M ⧸ K) := isCyclic_of_prime_card hcard
  let : CommGroup (M ⧸ K) := IsCyclic.commGroup
  let q : M →* M ⧸ K := QuotientGroup.mk' K
  let character : T →* M ⧸ K := q.comp (inclusion hTM)
  have hrespect : ∀ x y : T, IsConj (x : G) (y : G) →
      character x = character y := by
    intro x y hxy
    have hxp : IsPGroup 2 (zpowers (x : G)) := T.isPGroup'.of_injective
      (inclusion (zpowers_le.mpr x.property)) (inclusion_injective _)
    obtain ⟨m, hm, he⟩ := w.two_element_fusion x y
      (hTM x.property) (hTM y.property) hxp hxy
    let mM : M := ⟨m, hm⟩
    let xM : M := inclusion hTM x
    let yM : M := inclusion hTM y
    have heM : mM⁻¹ * xM * mM = yM := Subtype.ext he
    change q xM = q yM
    rw [← heM]
    simp [map_mul, map_inv, mul_comm]
  have hzero : ∀ x : T, character x = 1 :=
    T.fusion_invariant_eq_one_of_simple hns character hcard hrespect
  have hTK : ((T.subtype hTM : Sylow 2 M) : Subgroup M) ≤ K := by
    intro x hx
    have hz := hzero ⟨(x : G), hx⟩
    change QuotientGroup.mk' K x = 1 at hz
    exact (QuotientGroup.eq_one_iff x).mp hz
  have hd := index_dvd_of_le hTK
  rw [hK] at hd
  exact (T.subtype hTM).not_dvd_index hd

/-- In particular the faithful image Aut_M(U) has no index-two subgroup.
The theorem uses an actual surjective map, rather than an abstract label. -/
theorem LocalControlWitness.image_index_ne_two [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) {T : Sylow 2 G} {M : Subgroup G}
    (w : LocalControlWitness T M) (hTM : (T : Subgroup G) ≤ M)
    {X : Type*} [Group X] (f : M →* X) (hf : Function.Surjective f)
    (K : Subgroup X) : K.index ≠ 2 := by
  have hn := w.index_ne_two hns hTM (K.comap f)
  rwa [K.index_comap_of_surjective hf] at hn

/-- The simple-QTKE hypotheses discharge nonsolvability for this exact
source application. -/
theorem LocalControlWitness.source_index_ne_two {C : GroupClass.{u}}
    (hG : IsSimpleQTKE C G) {T : Sylow 2 G} {M : Subgroup G}
    (w : LocalControlWitness T M) (hTM : (T : Subgroup G) ≤ M)
    (K : Subgroup M) : K.index ≠ 2 := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩
  exact w.index_ne_two hns hTM K

end CFSG.Quasithin.Chapter2.BenderFusion
