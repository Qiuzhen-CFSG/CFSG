module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Model
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers
public import Theory.GroupAction.CyclicDisplacement

/-!
# The two literal quotients identified with the moved image

The restriction of U → U/Z(U) identifies A/⟨z⟩ with the moved image.
The displacement u ↦ [u,i]Z(U) identifies U/A with that same image:
it kills A because D is elementary, and its range has order 16, so
its kernel has order 32 and is exactly A. No duality or transvection
hypothesis is required.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The base lies in U. -/
theorem liftBase_le_core (U : Subgroup G) (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) : liftBase U z i ≤ U := by
  apply sup_le (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU))
  rw [← hZ]
  exact map_subtype_le _

/-- K U normalizes the actual base. -/
theorem liftBase_normalized (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hKi : K ≤ centralizer ({i} : Set G))
    (hmoved : Nat.card (movedImage U i) = 16) :
    K ⊔ U ≤ normalizer (liftBase U z i : Set G) := by
  rw [(liftBase_eq_commutator_and_card U z i hZ hiU hmoved).1]
  refine sup_le ?_ (normalizer_commutator_ge_left _ _)
  intro k hk
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hKU hk), MonoidHom.map_zpowers]
  congr 2
  change k * i * k⁻¹ = i
  rw [mem_centralizer_singleton_iff.mp (hKi hk)]
  group

/-- The restricted central quotient identifies the literal A/Z with M. -/
theorem liftBase_quotient_equiv_moved
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hmoved : Nat.card (movedImage U i) = 16)
    (hN : ((zpowers z).subgroupOf (liftBase U z i)).Normal) :
    let _ := hN
    ∃ e : (liftBase U z i ⧸ (zpowers z).subgroupOf (liftBase U z i)) ≃* movedImage U i,
      ∀ a : liftBase U z i,
        (e (QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i)) a) : U ⧸ center U) =
          QuotientGroup.mk' (center U) ⟨a, liftBase_le_core U z i hZ hiU a.property⟩ := by
  let _ := hN
  let j := inclusion (liftBase_le_core U z i hZ hiU)
  let f := (QuotientGroup.mk' (center U)).comp j
  have hker : f.ker = (zpowers z).subgroupOf (liftBase U z i) := by
    ext a
    change QuotientGroup.mk' (center U) (j a) = 1 ↔ (a : G) ∈ zpowers z
    change j a ∈ (QuotientGroup.mk' (center U)).ker ↔ _
    rw [QuotientGroup.ker_mk', ← hZ]
    constructor
    · intro ha; exact mem_map_of_mem U.subtype ha
    · rintro ⟨u,hu,he⟩
      exact (show u = j a from Subtype.ext he) ▸ hu
  have hrange : f.range = movedImage U i := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      refine ⟨j a, ?_, rfl⟩
      change (a : G) ∈ ⁅U,zpowers i⁆
      rw [← (liftBase_eq_commutator_and_card U z i hZ hiU hmoved).1]
      exact a.property
    · rintro ⟨u,hu,rfl⟩
      refine ⟨⟨u, (le_sup_left : ⁅U,zpowers i⁆ ≤ liftBase U z i) hu⟩,rfl⟩
  exact exists_quotient_equiv_image f _ _ hker hrange

/-- Displacement gives the literal U/A isomorphism, with its defining formula. -/
theorem core_quotient_equiv_moved
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (movedImage U i) = 16)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hN : ((liftBase U z i).subgroupOf U).Normal) :
    let _ := hN
    ∃ e : (U ⧸ (liftBase U z i).subgroupOf U) ≃* movedImage U i,
      ∀ u : U,
        (e (QuotientGroup.mk' ((liftBase U z i).subgroupOf U) u) : U ⧸ center U) =
          QuotientGroup.mk' (center U) ⟨⁅(u : G),i⁆,
            (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU))
              (commutator_mem_commutator u.property (mem_zpowers i))⟩ := by
  let _ := hN
  let _ := hD
  let _ := IsExtraspecial.quotient_elementary_abelian 2 U
  let q := QuotientGroup.mk' (center U)
  let f := cyclicDisplacement U q i hiU
  have hrange : f.range = movedImage U i := cyclicDisplacement_range U q i hiU
  have hAD : liftBase U z i ≤ centralizerLift U z i :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hiD : i ∈ centralizerLift U z i :=
    (le_sup_right.trans le_sup_left : zpowers i ≤ centralizerLift U z i) (mem_zpowers i)
  have hAker : (liftBase U z i).subgroupOf U ≤ f.ker := by
    intro a ha
    rw [MonoidHom.mem_ker, cyclicDisplacement_apply]
    have hc : Commute (a : G) i := by
      exact ((centralizerLift U z i).le_centralizer (hAD ha) i hiD).symm
    have he : (⟨⁅(a : G),i⁆, (le_normalizer_iff_commutator_le_left.mp
      (zpowers_le.mpr hiU)) (commutator_mem_commutator a.property (mem_zpowers i))⟩ : U) = 1 := Subtype.ext hc.commutator_eq
    rw [he, map_one]
  have hAcard : Nat.card ((liftBase U z i).subgroupOf U) = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (liftBase_le_core U z i hZ hiU)).toEquiv]
    exact (liftBase_eq_commutator_and_card U z i hZ hiU hmoved).2
  have hker : f.ker = (liftBase U z i).subgroupOf U := by
    symm
    apply eq_of_le_of_card_ge hAker
    have hh := f.ker.card_mul_index
    rw [index_ker,hrange,hmoved,hUcard] at hh
    rw [hAcard]
    omega
  obtain ⟨e,he⟩ := exists_quotient_equiv_image f _ _ hker hrange
  exact ⟨e, fun u => (he u).trans (cyclicDisplacement_apply U q i hiU u)⟩
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
