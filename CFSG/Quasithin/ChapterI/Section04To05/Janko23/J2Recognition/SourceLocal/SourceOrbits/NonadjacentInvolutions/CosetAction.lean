module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Completion
public import Theory.GroupAction.SixPointInvolutionStabilizers
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The six-coset argument for the nonneighbor involutions

Write L = C_G(X), F for the actual A₅ pointwise edge fixer, and
S = C_L(U). The central X has order three, is disjoint from F, and
centralizes F. Thus FX has order 180 and index six in L. Quasisimplicity
and L/Z(L) ≃ A₆ identify the left coset action's kernel with Z(L) = X.
In particular, every subgroup of order ten acts faithfully on these cosets.

The structural six-point lemmas supply an involution of S fixing the
base coset in each of the order-eight and order-ten cases. If this
involution is f*x in FX, then its cube equals both itself and f³, so it
lies in F. Its literal memberships in F and C_L(U), together with the
source class identification in F, give the required ambient witness.

Source: Aschbacher, *Sporadic Groups* (1994), final paragraph of the proof
of 47.6, printed p.264. All actions here are left actions on the literal
quotient by `(F ⊔ X).subgroupOf L`. The central quotient is taken by
`center L`, with an explicit equality identifying it with `X.subgroupOf L`;
no ambient normality of X is asserted.

`CentralizerTypes` records the remaining source calculation: C_L(U) is
Sylow two for an SL₂(3) join, and is D₁₀ for an A₅ join. This module proves
the subsequent implication, but does not construct that record from 47.5.
The source assembly must discharge it before claiming either full branch.
-/

@[expose] public section

open Subgroup MulAction
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.NonadjacentInvolutions
variable {G : Type*} [Group G] [Finite G]

/-- The source L, with its actual ambient inclusion. -/
abbrev localCentralizer (D : Seed G) : Subgroup G := centralizer (D.X : Set G)

/-- The point stabilizer for the six-point action, formed inside L. -/
def cosetSubgroup (D : Seed G) (Y : D.Vertex) : Subgroup (localCentralizer D) :=
  (Theory.GroupTheory.GraphUniquenessSystem.edgeFixer G D.base Y ⊔ D.X).subgroupOf
    (localCentralizer D)

/-- The group C_L(U), retaining both literal centralizer conditions. -/
def nonneighborCentralizer (D : Seed G) (U : D.Vertex) : Subgroup (localCentralizer D) :=
  (centralizer (U.val : Set G)).subgroupOf (localCentralizer D)

open Theory.GroupTheory.GraphUniquenessSystem

private theorem edgeFixer_centralizes_X (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5))) :
    edgeFixer G D.base Y ≤ centralizer (D.X : Set G) := by
  rw [edgeFixer_eq_centralizer_join_of_alternatingFive D D.base Y hF]
  exact centralizer_le (show D.X ≤ D.base.val ⊔ Y.val from le_sup_left)

private theorem X_le_localCentralizer (D : Seed G) : D.X ≤ localCentralizer D := by
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  intro x hx
  exact mem_centralizer_iff.mpr (fun y hy =>
    congrArg Subtype.val (mul_comm (⟨y, hy⟩ : D.X) ⟨x, hx⟩))

theorem involution_mem_edgeFixer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    {t : G} (ht : t ^ 2 = 1) (hmem : t ∈ edgeFixer G D.base Y ⊔ D.X) :
    t ∈ edgeFixer G D.base Y := by
  let F := edgeFixer G D.base Y
  have hcomm : D.X ≤ centralizer (F : Set G) :=
    le_centralizer_iff.mp (edgeFixer_centralizes_X D Y hF)
  have hmul : t ∈ (F : Set G) * (D.X : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left F D.X
      (hcomm.trans (centralizer_le_normalizer _))]
    exact hmem
  obtain ⟨f, hf, x, hx, rfl⟩ := hmul
  have hx3 : x ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : D.X))
    rw [D.card_X] at hh
    exact congrArg Subtype.val hh
  have hfx : Commute f x := mem_centralizer_iff.mp (hcomm hx) f hf
  have ht3 : (f * x) ^ 3 = f * x := by rw [pow_succ, ht, one_mul]
  have he : f * x = f ^ 3 := by rw [← ht3, hfx.mul_pow, hx3, mul_one]
  change f * x ∈ F
  rw [he]
  exact F.pow_mem hf 3

private theorem edgeFixer_disjoint_X (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5))) :
    Disjoint (edgeFixer G D.base Y) D.X := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  rintro x ⟨hf, hx⟩
  have hcomm := le_centralizer_iff.mp (edgeFixer_centralizes_X D Y hF)
  have hz : (⟨x, hf⟩ : edgeFixer G D.base Y) ∈ center (edgeFixer G D.base Y) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hcomm hx) y y.property)
  have he := (centerCongr hF.some ⟨⟨x, hf⟩, hz⟩).property
  change hF.some ⟨x, hf⟩ ∈ center (alternatingGroup (Fin 5)) at he
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  exact congrArg Subtype.val (hF.some.map_eq_one_iff.mp he)

theorem card_cosetSubgroup (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5))) :
    Nat.card (cosetSubgroup D Y) = 180 := by
  have hle : edgeFixer G D.base Y ⊔ D.X ≤ localCentralizer D :=
    sup_le (edgeFixer_centralizes_X D Y hF) (X_le_localCentralizer D)
  rw [cosetSubgroup, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    ((le_centralizer_iff.mp (edgeFixer_centralizes_X D Y hF)).trans
      (centralizer_le_normalizer _)) (edgeFixer_disjoint_X D Y hF)]
  rw [D.card_X, Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem card_cosets (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hL : Nat.card (localCentralizer D) = 1080) :
    Nat.card (localCentralizer D ⧸ cosetSubgroup D Y) = 6 := by
  have hh := (cosetSubgroup D Y).index_mul_card
  rw [card_cosetSubgroup D Y hF, hL, (cosetSubgroup D Y).index_eq_card] at hh
  omega


theorem center_card (D : Seed G)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D)) :
    Nat.card (center (localCentralizer D)) = 3 := by
  rw [hZ, Nat.card_congr (subgroupOfEquivOfLe (X_le_localCentralizer D)).toEquiv,
    D.card_X]

theorem localCentralizer_card (D : Seed G)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6)) :
    Nat.card (localCentralizer D) = 1080 := by
  have hh := (center (localCentralizer D)).index_mul_card
  rw [center_card D hZ, (center (localCentralizer D)).index_eq_card,
    Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hh
  norm_num at hh
  exact hh.symm

/-- The kernel of the literal left coset action is exactly X inside L. -/
theorem coset_action_kernel (D : Seed G) (Y : D.Vertex)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6)) :
    (MulAction.toPermHom (localCentralizer D)
      (localCentralizer D ⧸ cosetSubgroup D Y)).ker =
        D.X.subgroupOf (localCentralizer D) := by
  rw [← normalCore_eq_ker, ← hZ]
  apply le_antisymm
  · rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top
      (cosetSubgroup D Y).normalCore with hh | hh
    · exact hh
    · have htop := top_unique (hh ▸ (cosetSubgroup D Y).normalCore_le)
      have hc := card_cosetSubgroup D Y hF
      rw [htop, card_top, localCentralizer_card D hZ e] at hc
      omega
  · apply normal_le_normalCore.mpr
    rw [hZ]
    exact fun x hx => (show D.X ≤ edgeFixer G D.base Y ⊔ D.X from le_sup_right) hx

/-- The source order-ten subgroup acts faithfully: the coset kernel has
order three, coprime to its order. -/
theorem nonneighbor_action_faithful (D : Seed G) (Y U : D.Vertex)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (hS : Nat.card (nonneighborCentralizer D U) = 10) :
    FaithfulSMul (nonneighborCentralizer D U)
      (localCentralizer D ⧸ cosetSubgroup D Y) := by
  let S := nonneighborCentralizer D U
  let Ω := localCentralizer D ⧸ cosetSubgroup D Y
  let f := MulAction.toPermHom S Ω
  have hd : Disjoint S (D.X.subgroupOf (localCentralizer D)) :=
    disjoint_of_coprime_natCard (by
      rw [hS, ← hZ, center_card D hZ]
      decide)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro s hs
    have he : (MulAction.toPermHom (localCentralizer D) Ω) (s : localCentralizer D) = 1 := hs
    have hm : (s : localCentralizer D) ∈ D.X.subgroupOf (localCentralizer D) := by
      rw [← coset_action_kernel D Y hF hZ e]
      exact he
    apply Subtype.ext
    exact (disjoint_iff.mp hd).le ⟨s.property, hm⟩
  exact ⟨fun {s t} h => hf (Equiv.ext h)⟩


/-- The two centralizer calculations still to be derived from 47.5 and the
earlier source local structure. This record contains subgroup types, not
fixed points or the desired triple-centralizing involution. -/
structure CentralizerTypes (D : Seed G) : Prop where
  sl_sylow : ∀ U : D.Vertex, sl2Join D D.base U →
    ∃ P : Sylow 2 (localCentralizer D),
      (P : Subgroup (localCentralizer D)) = nonneighborCentralizer D U
  five_dihedral : ∀ U : D.Vertex, a5Join D D.base U →
    Nonempty (nonneighborCentralizer D U ≃* DihedralGroup 5)

private theorem ambientWitness_of_fixed_involution (D : Seed G) (Y U : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (t : nonneighborCentralizer D U) (ht : orderOf t = 2)
    (hfix : t • ((1 : localCentralizer D) :
      localCentralizer D ⧸ cosetSubgroup D Y) =
        ((1 : localCentralizer D) : localCentralizer D ⧸ cosetSubgroup D Y)) :
    ∃ v : G, IsConj D.z v ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer v := by
  have hm : (t : localCentralizer D) ∈ cosetSubgroup D Y := by
    rw [← stabilizer_quotient (cosetSubgroup D Y)]
    exact hfix
  have ho : orderOf ((t : localCentralizer D) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hf : ((t : localCentralizer D) : G) ∈ edgeFixer G D.base Y :=
    involution_mem_edgeFixer D Y hF (by
      simpa only [ho] using (pow_orderOf_eq_one ((t : localCentralizer D) : G))) hm
  refine ⟨((t : localCentralizer D) : G), hclass _ hf ho, sup_le ?_ ?_⟩
  · have hh : ((t : localCentralizer D) : G) ∈
        centralizer ((D.X ⊔ Y.val : Subgroup G) : Set G) := by
      have hh := hf
      rw [edgeFixer_eq_centralizer_join_of_alternatingFive D D.base Y hF] at hh
      exact hh
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hh x hx)
  · intro u hu
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp t.property u hu)

/-- The source SL₂(3) branch once its centralizer has been computed. The
involution is constructed by orbit-stabilizer on the actual six cosets. -/
theorem commonInvolution_of_card_eight (D : Seed G) (Y U : D.Vertex)
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hL : Nat.card (localCentralizer D) = 1080)
    (hS : Nat.card (nonneighborCentralizer D U) = 8) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  obtain ⟨t, ht, hfix⟩ := SixPointInvolutionStabilizers.exists_involution_fixed_of_card_eight
    hS (card_cosets D Y hF hL)
    ((1 : localCentralizer D) : localCentralizer D ⧸ cosetSubgroup D Y)
  exact ambientWitness_of_fixed_involution D Y U hF hclass t ht hfix

/-- The source A₅ branch once its centralizer has been computed. Its order-ten
subgroup acts faithfully because the coset kernel is the central X. -/
theorem commonInvolution_of_card_ten (D : Seed G) (Y U : D.Vertex)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (hS : Nat.card (nonneighborCentralizer D U) = 10) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  let := nonneighbor_action_faithful D Y U hF hZ e hS
  obtain ⟨t, ht, hfix⟩ := SixPointInvolutionStabilizers.exists_involution_fixed_of_card_ten
    hS (card_cosets D Y hF (localCentralizer_card D hZ e))
    ((1 : localCentralizer D) : localCentralizer D ⧸ cosetSubgroup D Y)
  exact ambientWitness_of_fixed_involution D Y U hF hclass t ht hfix

/-- Both nonneighbor branches from their literal centralizer types. The
remaining source calculation is precisely `CentralizerTypes`, not a
triple-centralizer or fixed-point premise. -/
theorem commonInvolution_of_centralizerTypes (D : Seed G) (Y : D.Vertex)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (hF : Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (types : CentralizerTypes D) (U : D.Vertex)
    (hU : sl2Join D D.base U ∨ a5Join D D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  rcases hU with hsl | hfive
  · apply commonInvolution_of_card_eight D Y U hF hclass (localCentralizer_card D hZ e)
    obtain ⟨P, hP⟩ := types.sl_sylow U hsl
    rw [← hP, P.card_eq_multiplicity, localCentralizer_card D hZ e]
    decide +kernel
  · apply commonInvolution_of_card_ten D Y U hF hclass hZ e
    rw [Nat.card_congr (types.five_dihedral U hfive).some.toEquiv,
      Nat.card_eq_fintype_card, DihedralGroup.card]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.NonadjacentInvolutions
