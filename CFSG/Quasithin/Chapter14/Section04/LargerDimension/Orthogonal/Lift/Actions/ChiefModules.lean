module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Equivariance
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Series

/-!
# Chief modules of the orthogonal lift

From the selected moved A₅-module in the literal quotient U/Z(U), this module
constructs A and D, the two binary quotient modules A/⟨z⟩ and U/A, and the
actual chief series 1<⟨z⟩<A<D. Both quotient actions are ambient conjugation
and descend to P/U through the supplied quotient presentation. The order-two
factors have explicit trivial conjugation actions.

The final specialization uses K₀ = O²(C_{C_G(z)}(i)). Its centralization of i
is proved from that definition. The orthogonal selection remains an input;
no lifted quotient identification or irreducibility assertion is assumed.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010. The parent Actions
module owns the remaining source assembly and the independent transvection
calculation.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- The constructed chief modules, retaining literal denominators and actions. -/
structure ChiefModuleResult (U K : Subgroup G) (z i : G)
    (hKU : K ≤ normalizer (U : Set G)) (m : MovedCoreModel U K i hKU) where
  elementary_D : IsElementaryAbelian 2 (centralizerLift U z i)
  card_D : Nat.card (centralizerLift U z i) = 64
  elementary_A : IsElementaryAbelian 2 (liftBase U z i)
  card_A : Nat.card (liftBase U z i) = 32
  series : LiftChiefSeries U K z i
  normal_ZA : ((zpowers z).subgroupOf (liftBase U z i)).Normal
  normal_AU : ((liftBase U z i).subgroupOf U).Normal
  normal_AD : ((liftBase U z i).subgroupOf (centralizerLift U z i)).Normal
  base : let _ := normal_ZA
    BinaryFactorModel (K ⊔ U) (liftBase U z i) (zpowers z) m.π series.normalizes_A
  core : let _ := normal_AU
    BinaryFactorModel (K ⊔ U) U (liftBase U z i) m.π (sup_le hKU U.le_normalizer)
  card_Z : Nat.card (zpowers z) = 2
  card_top : let _ := normal_AD
    Nat.card (centralizerLift U z i ⧸ (liftBase U z i).subgroupOf (centralizerLift U z i)) = 2
  lineAction : ↥(K ⊔ U) →* MulAut (zpowers z)
  line_trivial : lineAction = 1
  line_formula : ∀ (p : ↥(K ⊔ U)) (v : zpowers z),
    ((lineAction p v : zpowers z) : G) = (p : G) * (v : G) * (p : G)⁻¹
  topAction : let _ := normal_AD
    ↥(K ⊔ U) →* MulAut (centralizerLift U z i ⧸
      (liftBase U z i).subgroupOf (centralizerLift U z i))
  top_trivial : let _ := normal_AD
    topAction = 1
  top_formula : let _ := normal_AD
    ∀ (p : ↥(K ⊔ U)) (v : centralizerLift U z i),
      topAction p (QuotientGroup.mk' ((liftBase U z i).subgroupOf (centralizerLift U z i)) v) =
        QuotientGroup.mk' ((liftBase U z i).subgroupOf (centralizerLift U z i))
          ⟨(p : G) * (v : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (series.normalizes_D p.property) v).mp v.property⟩

  quotient_base : let _ := normal_ZA
    let _ := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
    ∃ ψ : (↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U)) →* MulAut
      (liftBase U z i ⧸ (zpowers z).subgroupOf (liftBase U z i)),
      (∀ (p : ↥(K ⊔ U)) (a : liftBase U z i),
        ψ (QuotientGroup.mk' (U.subgroupOf (K ⊔ U)) p)
          (QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i)) a) =
          QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i))
            ⟨(p : G) * (a : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp (series.normalizes_A p.property) a).mp a.property⟩) ∧
      (∀ (p : ↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U))
          (v : liftBase U z i ⧸ (zpowers z).subgroupOf (liftBase U z i)),
        base.equiv (ψ p v) = Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (m.actorEquiv p).val (base.equiv v).toAdd))
  quotient_core : let _ := normal_AU
    let _ := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
    ∃ ψ : (↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U)) →* MulAut
      (U ⧸ (liftBase U z i).subgroupOf U),
      (∀ (p : ↥(K ⊔ U)) (u : U),
        ψ (QuotientGroup.mk' (U.subgroupOf (K ⊔ U)) p)
          (QuotientGroup.mk' ((liftBase U z i).subgroupOf U) u) =
          QuotientGroup.mk' ((liftBase U z i).subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp ((sup_le hKU U.le_normalizer) p.property) u).mp u.property⟩) ∧
      (∀ (p : ↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U)) (v : U ⧸ (liftBase U z i).subgroupOf U),
        core.equiv (ψ p v) = Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (m.actorEquiv p).val (core.equiv v).toAdd))
  relative_normal :
    ((zpowers z).subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal ∧
      ((liftBase U z i).subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal ∧
      ((centralizerLift U z i).subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal

namespace MovedCoreModel
variable {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable [IsExtraspecial 2 U] (m : MovedCoreModel U K i hKU)

/-- Complete construction of the requested chief factors from the selected
moved module. In particular U/A is constructed, not supplied as an input. -/
theorem chief_modules (z : G) (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKi : K ≤ centralizer ({i} : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (movedImage U i) = 16) :
    Nonempty (ChiefModuleResult U K z i hKU m) := by
  obtain ⟨hD,hDcard,hA,hAcard⟩ := m.elementary_lift z hz hi hZ hiU hiz hout hKi hmoved
  have s := m.chief_series z hz hi hZ hiU hiz hout hKi hmoved
  let _ := hD
  let _ := hA
  have hZA : ((zpowers z).subgroupOf (liftBase U z i)).Normal := by infer_instance
  have hAD : ((liftBase U z i).subgroupOf (centralizerLift U z i)).Normal := by infer_instance
  have hAU : ((liftBase U z i).subgroupOf U).Normal :=
    normal_subgroupOf_of_le_normalizer (le_sup_right.trans s.normalizes_A)
  let _ := hZA
  let _ := hAD
  let _ := hAU
  obtain ⟨b⟩ := m.base_binary_factor z hZ hiU hmoved s.normalizes_A s.normalizes_Z hZA
  obtain ⟨c⟩ := m.core_binary_factor z hZ hiU hKi hUcard hmoved hD s.normalizes_A hAU
  obtain ⟨ρZ,hρZ,hZformula⟩ := s.line_action
  obtain ⟨ρD,hρD,hDformula⟩ := s.top_action hAD
  have htop : Nat.card (centralizerLift U z i ⧸
      (liftBase U z i).subgroupOf (centralizerLift U z i)) = 2 := by
    have hh := ((liftBase U z i).subgroupOf (centralizerLift U z i)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe s.strict.2.2.le).toEquiv,hAcard,hDcard] at hh
    change 32 * Nat.card (centralizerLift U z i ⧸
      (liftBase U z i).subgroupOf (centralizerLift U z i)) = 64 at hh
    omega
  exact ⟨⟨hD,hDcard,hA,hAcard,s,hZA,hAU,hAD,b,c,
    by rw [Nat.card_zpowers,hz],htop,ρZ,hρZ,hZformula,ρD,hρD,hDformula,
    m.quotient_actor_action _ _ s.normalizes_A b,
    m.quotient_actor_action _ _ (sup_le hKU U.le_normalizer) c,
    s.relative_normal hD⟩⟩
end MovedCoreModel

/-- The source-specialized conditional result for the actual diagonal residual.
The source selection producer supplies precisely the moved-module model and
geometric hypotheses; the lifted modules and chief series are conclusions. -/
theorem diagonalResidual_chief_modules
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) i ≤ normalizer (U : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (movedImage U i) = 16)
    (m : MovedCoreModel U (diagonalResidual (centralizer ({z} : Set G)) i) i hKU) :
    Nonempty (ChiefModuleResult U (diagonalResidual (centralizer ({z} : Set G)) i) z i hKU m) := by
  have hKi : diagonalResidual (centralizer ({z} : Set G)) i ≤ centralizer ({i} : Set G) :=
    (map_subtype_le _).trans inf_le_right
  exact m.chief_modules z hz hi hZ hiU hiz hout hKi hUcard hmoved
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
