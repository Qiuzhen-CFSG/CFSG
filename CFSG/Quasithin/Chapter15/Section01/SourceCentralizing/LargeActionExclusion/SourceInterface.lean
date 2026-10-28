module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Seed

/-!+# Common source interfaces for the end of original 15.1.15

After 15.1.24 the surviving actions are the elementary-nine action and the
two exchanged four-dimensional dihedral-three actions. Their planes have
orders four and sixteen, respectively. The common interface retains these
different sizes, the actual marked centralizer, and the original cubic
residual. It does not assert that either row has been excluded.

The natural-module interface records an actual intertwining map for the
action of L on [<Z2^L>,L] and the projection of Z2, including its point
stabilizer. Its construction is precisely the outstanding 15.1.27--28
argument; the contradiction using it is the separate 15.1.29 argument.

Source: Aschbacher--Smith, 15.1.24--29, printed pp.1101--1104.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The genuine common conclusions preceding natural-module recognition.
The sixteen-element planes in source row (6) are deliberately retained. -/
structure ExchangedSource (d : CaseIComponentData T M Mc V) : Prop where
  sizes :
    (d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      Nat.card d.nineFixedPlane = 4 ∧ Nat.card d.nineMovingPlane = 4) ∨
    (d.row = .six ∧ Nat.card d.Z1 = 4 ∧
      Nat.card d.nineFixedPlane = 16 ∧ Nat.card d.nineMovingPlane = 16)
  odd_core : pPrimeCore 2 d.G1 = ⊥
  quasisimple : IsQuasisimple (d.L ⧸ pCore 2 d.L)
  local_component : d.L ∈ Chapter1.L G d.S
  component_sylow : Chapter1.IsSylowIn 2 d.SL d.L
  centralizer_sylow : Chapter1.IsSylowIn 2 d.S d.G1
  outside_M : ¬ d.L ≤ M
  ordinary : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinarySource
  planes_sup : d.nineFixedPlane ⊔ d.nineMovingPlane = V
  planes_inf : d.nineFixedPlane ⊓ d.nineMovingPlane = ⊥
  marked_le_fixed : d.Z1 ≤ d.nineFixedPlane
  index : d.S.relIndex (T : Subgroup G) = 2
  sylow_normal : (d.S.subgroupOf (T : Subgroup G)).Normal
  fixes_planes : d.S ≤ normalizer (d.nineFixedPlane : Set G) ∧
    d.S ≤ normalizer (d.nineMovingPlane : Set G)
  fixed_centralizer_index : (centralizer (d.nineFixedPlane : Set G)).relIndex d.S = 2
  exchanges : ∀ t ∈ (T : Subgroup G), t ∉ d.S →
    d.nineFixedPlane.map (MulAut.conj t).toMonoidHom = d.nineMovingPlane ∧
    d.nineMovingPlane.map (MulAut.conj t).toMonoidHom = d.nineFixedPlane
  exchange_exists : ∃ t ∈ (T : Subgroup G), t ∉ d.S
  cubic_escape : ¬ d.nineCubic ≤ d.MZ
  cubic_idempotent : (primeToResidual 3 d.nineCubic).map d.nineCubic.subtype = d.nineCubic
  cubic_two_perfect : IsPPerfect 2 d.nineCubic
  cubic_normalizes : d.nineCubic ≤ normalizer (V : Set G)
  cubic_commutator : ⁅V,d.nineCubic⁆ = d.nineMovingPlane
  cubic_moving : ⁅d.nineMovingPlane,d.nineCubic⁆ = d.nineMovingPlane
  fixed_noncentral : Facts (d.L ⧸ pCore 2 d.L) →
    ¬ d.nineFixedPlane ≤ centralizer (d.L : Set G)
  seed_bound : centralInvolutions T ⊓ V ≤ d.Z1 ⊔ d.nineMovingPlane
  moving_noncentral : ⁅d.L,d.nineMovingPlane⁆ ≠ ⊥
  core_nontrivial : d.Q1 ≠ ⊥
  characteristic_control : d.Q1.characteristicNormalizerClosure ≤ Mc
  core_normalizer : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ
  sylow_normalizes_MZ : (T : Subgroup G) ≤ normalizer (d.MZ : Set G)
  sylow_normalizes_Q1 : (T : Subgroup G) ≤ normalizer (d.Q1 : Set G)

/-- The existing actual Nine selection is a special case of the common data. -/
theorem NineSource.toExchangedSource {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) : d.ExchangedSource where
  sizes := Or.inl ⟨s.row,s.marked_card,s.fixed_card,s.moving_card⟩
  odd_core := s.odd_core
  quasisimple := s.quasisimple
  local_component := s.local_component
  component_sylow := s.component_sylow
  centralizer_sylow := s.centralizer_sylow
  outside_M := s.outside_M
  ordinary := s.ordinary
  planes_sup := s.planes_sup
  planes_inf := s.planes_inf
  marked_le_fixed := s.marked_le_fixed
  index := s.index
  sylow_normal := s.sylow_normal
  fixes_planes := s.fixes_planes
  fixed_centralizer_index := s.fixed_centralizer_index
  exchanges := s.exchanges
  exchange_exists := s.exchange_exists
  cubic_escape := s.cubic_escape
  cubic_idempotent := s.cubic_idempotent
  cubic_two_perfect := s.cubic_two_perfect
  cubic_normalizes := s.cubic_normalizes
  cubic_commutator := s.cubic_commutator
  cubic_moving := s.cubic_moving
  fixed_noncentral := s.fixed_noncentral
  seed_bound := s.seed_bound
  moving_noncentral := s.moving_noncentral
  core_nontrivial := s.core_nontrivial
  characteristic_control := s.characteristic_control
  core_normalizer := s.core_normalizer
  sylow_normalizes_MZ := s.sylow_normalizes_MZ
  sylow_normalizes_Q1 := s.sylow_normalizes_Q1

/-- Original 15.1.26's literal quotient identification, with both possible
plane sizes and all of their embeddings still present. -/
def HasExchangedLinearSource (d : CaseIComponentData T M Mc V) : Prop :=
  d.ExchangedSource ∧ generalizedFitting d.L = pCore 2 d.L ∧
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))

/-- The natural action and projected seed asserted in original 15.1.28.
The marking uses the original quotient map, not an unrelated family tag. -/
def HasNaturalMovedModule (d : CaseIComponentData T M Mc V) (t : G) : Prop :=
  IsElementaryAbelian 2 (d.U t) ∧ ∃ hE : IsElementaryAbelian 2 (d.UL t),
    letI := hE
    ∃ hn : d.L ≤ normalizer (d.UL t : Set G),
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        ∃ e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
          ∃ x : Additive (d.UL t) ≃ₗ[ZMod 2] (Fin n → ZMod 2),
            (∀ (l : d.L) (v : Additive (d.UL t)),
              x (Additive.ofMul (actionHom d.L (d.UL t) hn l v.toMul)) =
                (e (QuotientGroup.mk' (pCore 2 d.L) l)).val.mulVec (x v)) ∧
            let C := d.U t ⊓ centralizer (d.L : Set G)
            d.UL t ⊔ C = d.U t ∧ d.UL t ⊓ C = ⊥ ∧
              ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
                ZU ≤ centralizer (d.S : Set G) ∧
                d.Z2 t ⊔ C = ZU ⊔ C ∧ d.L ⊓ centralizer (ZU : Set G) = d.ML

end CaseIComponentData

/-- Application of the common interface to the same original Nine action.
This supplies its source geometry, not component recognition or exclusion. -/
theorem PreparedChosenModule.source_caseI_nine_exchanged_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource := by
  obtain ⟨d,s⟩ := h.source_caseI_nine_source_selection hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s.toExchangedSource⟩

end CFSG.Quasithin.Chapter15.Section01
