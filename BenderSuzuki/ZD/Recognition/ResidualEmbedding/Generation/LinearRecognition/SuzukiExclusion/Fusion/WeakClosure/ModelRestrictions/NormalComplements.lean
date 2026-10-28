module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Embedding
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Complements
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Geometry
public import Theory.SpecificGroups.Suzuki.ElementarySylowSubgroups.NormalComplements

/-!
# Normal Suzuki Sylows and the source odd complements

The literal embedding J = C_G(L) → L ≃ Sz(q) sends the supplied elementary
Sylow subgroup U to the concrete Suzuki group. Solvability of J and |U|>2
therefore make U normal in J. If U is normal, its nontriviality puts J in a
conjugate Borel. Every odd subgroup Y of J is cyclic of order dividing q-1,
and Commute u y with u in U and nonidentity y in Y forces u=1 in G.

The final application uses the existing odd-complement construction and
normality transport to D. It discharges the intrinsic Suzuki premises used
in Chapter 2, Lemmas 14.7–14.8 without changing the surrounding geometry.

Source: GLS4, Chapter 4, Lemma 3.8; Chapter 2, Lemmas 14.7–14.8,
refs/KGroup/GLS4/Chapter4.tex and refs/KGroup/GLS4/Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The elementary Sylow factor of the actual centralizer is normal when its
order exceeds two (GLS4, Chapter 2, Lemma 14.8). -/
public theorem Context.U_normal_centralizer_of_two_lt_card
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hcard : 2 < Nat.card g.U) :
    (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal := by
  let J := centralizer (residualGenerated M z t : Set G)
  obtain ⟨V, hV⟩ := g.U_sylow_centralizer
  let eU : V ≃* g.U := ((V : Subgroup J).equivMapOfInjective J.subtype
    J.subtype_injective).trans (MulEquiv.subgroupCongr hV)
  let := g.U_elementary
  let : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.of_surjective eU.symm.toMonoidHom eU.symm.surjective
  let := g.centralizer_solvable
  have hnormal := suzuki_normal_elementary_sylow_of_embedding
    (by have := d.parameter_pos; omega) (d.model.toMonoidHom.comp f)
    (d.model.injective.comp hf) V
    (by rw [Nat.card_congr eU.toEquiv]; exact hcard)
  have he : g.U.subgroupOf J = (V : Subgroup J) := by
    rw [← hV]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  rw [he]
  exact hnormal

/-- For normal U, every odd subgroup of the actual centralizer has cyclic
order dividing q-1 and acts freely on the nonidentity elements of U.
In particular this applies to every source complement J = UY. -/
public theorem Context.odd_subgroup_restrictions_of_U_normal
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f)
    (hn : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hodd : Odd (Nat.card Y)) :
    IsCyclic Y ∧ Nat.card Y ∣ 2 ^ (2 * m + 1) - 1 ∧
      ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1 := by
  let J := centralizer (residualGenerated M z t : Set G)
  let V := g.U.subgroupOf J
  let eV := subgroupOfEquivOfLe g.U_le_centralizer
  let := g.U_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf g.U_le_centralizer
  have hVne : V ≠ ⊥ := (one_lt_card_iff_ne_bot V).mp (by
    rw [Nat.card_congr eV.toEquiv]
    exact d.two_le_U_card g)
  let W := Y.subgroupOf J
  let eW : W ≃* Y := subgroupOfEquivOfLe hYJ
  have hcardW : Nat.card W = Nat.card Y := Nat.card_congr eW.toEquiv
  obtain ⟨hcyclic, hdiv, hfree⟩ := suzuki_odd_subgroup_of_normal_two_embedding
    (by have := d.parameter_pos; omega) (d.model.toMonoidHom.comp f)
    (d.model.injective.comp hf) V (IsElementaryAbelian.isPGroup 2 V) hn hVne
    W (hcardW.symm ▸ hodd)
  refine ⟨eW.isCyclic.mp hcyclic, hcardW ▸ hdiv, ?_⟩
  intro y hy hy1 u hu hc
  have hcJ : Commute (⟨u, g.U_le_centralizer hu⟩ : J) (⟨y, hYJ hy⟩ : J) :=
    show _ = _ from Subtype.ext hc.eq
  exact congrArg Subtype.val (hfree (⟨y, hYJ hy⟩ : J) hy
    (fun h => hy1 (congrArg Subtype.val h)) (⟨u, g.U_le_centralizer hu⟩ : J) hu hcJ)

/-- The precise odd-complement instance used in GLS4, Chapter 2, Lemma 14.7.
The product and nontriviality hypotheses match that source application. -/
public theorem Context.normal_complement_restrictions
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f)
    (hn : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (_hYne : Y ≠ ⊥) (hodd : Odd (Nat.card Y))
    (_hprod : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G)) :
    IsCyclic Y ∧ Nat.card Y ∣ 2 ^ (2 * m + 1) - 1 ∧
      ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1 :=
  d.odd_subgroup_restrictions_of_U_normal g f hf hn Y hYJ hodd

/-- The |U|>2 branch supplies a nontrivial cyclic odd complement with all
Suzuki restrictions, and discharges the normality premise of the transport
from J to the pair stabilizer D. -/
public theorem Context.exists_normal_cyclic_complement_of_two_lt_card
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hcard : 2 < Nat.card g.U) :
    (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal ∧
      (g.U.subgroupOf (residualPairStabilizer M t)).Normal ∧
      ∃ Y : Subgroup G, Y ≤ centralizer (residualGenerated M z t : Set G) ∧
        Y ≠ ⊥ ∧ Odd (Nat.card Y) ∧
        (centralizer (residualGenerated M z t : Set G) : Set G) =
          (g.U : Set G) * (Y : Set G) ∧
        IsCyclic Y ∧ Nat.card Y ∣ 2 ^ (2 * m + 1) - 1 ∧
        ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1 := by
  have hn := d.U_normal_centralizer_of_two_lt_card g f hf hcard
  obtain ⟨Y, hYJ, hYne, hodd, hprod⟩ := s.exists_nontrivial_odd_complement g
  exact ⟨hn, d.U_normal_pair_of_normal g hn, Y, hYJ, hYne, hodd, hprod,
    d.normal_complement_restrictions g f hf hn Y hYJ hYne hodd hprod⟩

end BenderSuzuki.ZD.SuzukiExclusion
