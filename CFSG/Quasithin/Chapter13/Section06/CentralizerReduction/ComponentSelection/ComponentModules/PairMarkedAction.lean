module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairBaumannImage
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairFullAction
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
/-!
The actual marked paired quotient extends to the full plus group. The pair has trivial center, and plus generation and two-reducedness kill its full centralizer. The existing normal-layer quotient theorem therefore gives a faithful full action with the same quotient map.

Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem pair_marked_full_action_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (d : SourceTwoFactorCase ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hI : offenderSubgroup (wkRepresentation K L T z v hL hz) =
      plusImage K L T z v hL hz (Kminus K T v)) :
    let e := (MulEquiv.subgroupCongr hI.symm).trans c.action.groupEquiv
    ∃ ρ : Representation (ZMod 2) (Gplus K L T z v hL hz)
        ((Fin 2 → F.Carrier) × (Fin 2 → F.Carrier)),
      Function.Injective ρ ∧
      (∀ g w, c.quotientMap (wkRepresentation K L T z v hL hz g w) =
        ρ g (c.quotientMap w)) ∧
      ∀ (g : plusImage K L T z v hL hz (Kminus K T v)) (a b : Fin 2 → F.Carrier),
        ρ (g : Gplus K L T z v hL hz) (a,b) =
          ((e g).1.val.mulVec a,(e g).2.val.mulVec b) := by
  let α := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup α
  let C := plusImage K L T z v hL hz (Kminus K T v)
  let := offenderSubgroup_normal α
  let e := (MulEquiv.subgroupCongr hI.symm).trans c.action.groupEquiv
  have hZ : center C = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have he : e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F.Carrier ×
        Matrix.SpecialLinearGroup (Fin 2) F.Carrier) := (centerCongr e ⟨x,hx⟩).property
    rw [Subgroup.center_prod,Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,
      Subgroup.bot_prod_bot] at he
    exact e.injective ((mem_bot.mp he).trans e.map_one.symm)
  have hc : centralizer (I : Set (Gplus K L T z v hL hz)) ≤ I := by
    rw [show I = C from hI,
      paired_plus_centralizer_eq_bot_source K L T z v hL hz hK hLv hSylow hZ]
    exact bot_le
  obtain ⟨ρ,hρ,he,hres⟩ := c.linear_full_faithful_action α I hc d F
  exact ⟨ρ,hρ,he,fun g a b => hres ((MulEquiv.subgroupCongr hI.symm) g) a b⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
