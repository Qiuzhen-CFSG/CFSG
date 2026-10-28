module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Movement
public import Theory.SpecificGroups.SL2.ElementaryMovement
public import Theory.GroupTheory.SubgroupTransport

/-!
# The equal and radical branches of the point-core argument

The original elementary V is fully moved by L₁. In the E₄₉-by-SL₂(7)
alternative for K/O₂(K), its image is therefore trivial: its further SL₂
image is scalar, and a two-group cannot survive in the odd kernel.
Relative normality of K in G₁ then gives V ≤ O₂(G₁).

Together with Movement, this removes the equal and Ξ₇ rows from any
failure of point-core containment. The literal LocalComponents consumer
retains exactly the three large quotient models and Y ≤ K₁. Constructing
LocalComponents and excluding those large rows remain with this local owner;
qt-d-1251-source owns the final exterior exclusion.
Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

theorem seed_le_twoCore_of_radical_model {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K)
    (hm : HasExtension (K ⧸ pCore 2 K) (ElementaryModel 7 2)
      (fun X _ => IsSL X 2 7)) : V ≤ K.pCoreIn 2 := by
  obtain ⟨N, hn, ⟨eN⟩, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hm
  let := hn
  let := D.elementary
  let Q := K ⧸ pCore 2 K
  let r : K →* Q := QuotientGroup.mk' (pCore 2 K)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hk : IsPGroup 7 f.ker := by
    have he : f.ker = N := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    rw [he]
    apply IsPGroup.of_equiv _ eN.symm
    exact IsPGroup.of_card (n := 2) (by simp)
  have hVK : V ≤ K := s.seed_le_point_residual.trans hLK
  let A := V.subgroupOf K
  let B := (s.marking.Li 1).subgroupOf K
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 (A.map r) := IsElementaryAbelian.map r
  have hmove : ⁅A.map r, B.map r⁆ = A.map r := by
    rw [← map_commutator, ← SubgroupTransport.subgroupOf_commutator V _ hVK hLK]
    exact congrArg (fun X : Subgroup G => (X.subgroupOf K).map r) s.seed_point_commutator
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  have hfc : Fintype.card F = Fintype.card (ZMod 7) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF := FiniteField.ringEquivOfCardEq hfc
  have htwo : (2 : F) ≠ 0 := by
    intro hz
    exact (by decide : (2 : ZMod 7) ≠ 0) (by simpa only [map_ofNat, map_zero] using congrArg eF hz)
  have hz : A.map r = ⊥ :=
    Matrix.SpecialLinearGroup.elementary_fully_moved_eq_bot_of_odd_prime_kernel
      htwo
      (by decide : Nat.Coprime 2 7) f hk (A.map r) (B.map r) hmove
  have hA : A ≤ pCore 2 K := by
    have hh := (Subgroup.map_eq_bot_iff A).mp hz
    change A ≤ (QuotientGroup.mk' (pCore 2 K)).ker at hh
    rwa [QuotientGroup.ker_mk'] at hh
  intro v hv
  exact ⟨⟨v, hVK hv⟩, hA hv, rfl⟩

theorem seed_le_point_core_of_radical_model {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) (hKG : K ≤ s.marking.Gi 1)
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : HasExtension (K ⧸ pCore 2 K) (ElementaryModel 7 2)
      (fun X _ => IsSL X 2 7)) : V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  (s.seed_le_twoCore_of_radical_model hLK hm).trans
    (pCoreIn_mono_of_normalizes hKG ((normal_subgroupOf_iff_le_normalizer hKG).mp hn))

theorem point_core_failure_large (c : LocalComponents s)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    (ClassicalGroup.IsPSL (c.K 1 ⧸ pCore 2 (c.K 1)) 5 2 ∨
      Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* Janko4.Model)) ∧ s.Y ≤ c.K 1 := by
  have hi : LocalIndex 1 := Or.inl rfl
  cases c.alternative 1 hi with
  | equal he =>
    exact (hfail (s.seed_le_point_core_of_normal (he.symm ▸ c.normal 1 hi))).elim
  | large _ hm hy => exact ⟨hm, hy⟩
  | radical _ _ hm =>
    exact (hfail (s.seed_le_point_core_of_radical_model (c.contains 1 hi)
      (c.component 1 hi).1 (c.normal 1 hi) hm)).elim

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
