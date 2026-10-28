module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SylowMarkSource
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.NineAction
public import Theory.ElementaryAbelian.KernelTransport

/-!
# The source exceptional Sylow's diagonal rigidity

The original source setup supplies elementary full preimages under the
actual central-cover projection. Its actual component is perfect, so central
Sylow transfer discharges the covering-kernel premise. We construct a mark
on each original component Sylow in which every non-elementary subgroup
invariant under the full diagonal nine-group is the whole Sylow.

The common E₉ and its action on this marking must still be constructed from
the preceding exceptional A.3.18 alternative. This theorem discharges the
subgroup-rigidity step, without assuming triviality of the component center.
Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The literal exceptional component Sylow has the required rigidity under
its full diagonal action, including every permitted central two-cover. -/
theorem MathieuSourceSetup.linear_four_root_mark
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) (P : Sylow 2 L) :
    ∃ f : P →* Root, Function.Surjective f ∧ f.ker = (center L).subgroupOf P ∧
      ∀ W : Subgroup Root, IsElementaryAbelian 2 W →
        IsElementaryAbelian 2 (W.comap f) := by
  obtain ⟨q, hq, hk, hlift⟩ :=
    MathieuSourceSetup.linear_four_sylow_mark c hG hempty e P
  let f : P →* Root := evenRootEquiv.toMonoidHom.comp q
  have hf : Function.Surjective f := evenRootEquiv.surjective.comp hq
  have hfk : f.ker = (center L).subgroupOf P := by
    ext a
    change evenRootEquiv (q a) = 1 ↔ a ∈ (center L).subgroupOf P
    rw [← hk]
    exact ⟨fun h => evenRootEquiv.injective (h.trans (map_one _).symm),
      fun h => by change q a = 1 at h; rw [h, map_one]⟩
  have hflift (W : Subgroup Root) (hW : IsElementaryAbelian 2 W) :
      IsElementaryAbelian 2 (W.comap f) := by
    let := hW
    let : IsElementaryAbelian 2 (W.comap evenRootEquiv.toMonoidHom) :=
      IsElementaryAbelian.comap_of_injective evenRootEquiv.toMonoidHom
        evenRootEquiv.injective W
    exact hlift (W.comap evenRootEquiv.toMonoidHom) inferInstance
  exact ⟨f, hf, hfk, hflift⟩

omit [Finite G] in
private theorem component_perfect (c : MathieuSourceSetup H L M S z) : Group.IsPerfect L := by
  let : IsQuasisimple (L.subgroupOf H) := c.component.2
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe c.component_le
  exact Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective

/-- The full diagonal action has no proper non-elementary invariant subgroup
in the original exceptional component Sylow. -/
theorem MathieuSourceSetup.linear_four_diagonal_rigidity
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) (P : Sylow 2 L) :
    ∃ f : P →* Root, Function.Surjective f ∧ f.ker = (center L).subgroupOf P ∧
      ∀ A : Subgroup P,
        (∀ d : Matrix.PSL3Four.Fˣ × Matrix.PSL3Four.Fˣ,
          ∀ q ∈ A.map f, diagonal d q ∈ A.map f) →
        ¬ IsElementaryAbelian 2 A → A = ⊤ := by
  obtain ⟨f, hf, hk, hlift⟩ := MathieuSourceSetup.linear_four_root_mark c hG hempty e P
  let : Group.IsPerfect L := component_perfect c
  exact ⟨f, hf, hk, fun A hi hn =>
    diagonal_invariant_sylow_cover_eq_top P f hk hlift A hi hn⟩

/-- Every actual nine-group of automorphisms has the same rigidity; no
additional choice aligning it with the diagonal torus is necessary. -/
theorem MathieuSourceSetup.linear_four_nine_rigidity
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) (P : Sylow 2 L) :
    ∃ f : P →* Root, Function.Surjective f ∧ f.ker = (center L).subgroupOf P ∧
      ∀ (B : Subgroup (MulAut Root)) (A : Subgroup P), Nat.card B = 9 →
        (∀ b ∈ B, ∀ q ∈ A.map f, b q ∈ A.map f) →
        ¬ IsElementaryAbelian 2 A → A = ⊤ := by
  obtain ⟨f, hf, hk, hlift⟩ := MathieuSourceSetup.linear_four_root_mark c hG hempty e P
  let : Group.IsPerfect L := component_perfect c
  refine ⟨f, hf, hk, ?_⟩
  intro B A hB hi hn
  have hc : f.ker ≤ center P := by
    rw [hk]
    intro a ha
    exact mem_center_iff.mpr (fun b => Subtype.ext (mem_center_iff.mp ha b))
  have hd : f.ker ≤ _root_.commutator P := by
    rw [hk]
    exact center_subgroupOf_sylow_le_commutator P
  exact nine_invariant_cover_eq_top f hc hd hlift B hB A hi hn

/-- Rigidity holds for the literal marking chosen by the original E₉ action;
matching kernels transport elementary preimages from the source cover mark. -/
theorem MathieuSourceSetup.linear_four_nine_rigidity_of_mark
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) (P : Sylow 2 L)
    (f : P →* Root) (hk : f.ker = (center L).subgroupOf P)
    (B : Subgroup (MulAut Root)) (hB : Nat.card B = 9) (A : Subgroup P)
    (hinv : ∀ b ∈ B, ∀ q ∈ A.map f, b q ∈ A.map f)
    (hne : ¬ IsElementaryAbelian 2 A) : A = ⊤ := by
  obtain ⟨q, hq, hqk, hqLift⟩ := MathieuSourceSetup.linear_four_root_mark c hG hempty e P
  have hlift (W : Subgroup Root) (hW : IsElementaryAbelian 2 W) :
      IsElementaryAbelian 2 (W.comap f) :=
    IsElementaryAbelian.comap_of_same_kernel q f hq (hqk.trans hk.symm) hqLift W hW
  let : Group.IsPerfect L := component_perfect c
  have hc : f.ker ≤ center P := by
    rw [hk]
    intro a ha
    exact mem_center_iff.mpr (fun b => Subtype.ext (mem_center_iff.mp ha b))
  have hd : f.ker ≤ _root_.commutator P := by
    rw [hk]
    exact center_subgroupOf_sylow_le_commutator P
  exact nine_invariant_cover_eq_top f hc hd hlift B hB A hinv hne
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
