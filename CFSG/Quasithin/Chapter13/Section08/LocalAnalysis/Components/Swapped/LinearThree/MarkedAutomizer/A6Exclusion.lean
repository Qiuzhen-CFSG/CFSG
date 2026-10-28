module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Transports
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
public import Theory.Representation.HexacodeAction.Cover

/-!
# Excluding the simple marked A₆ case by three-rank

For the four-dimensional natural binary A₆-module, a nonzero vector has
stabilizer S₄, of order 24. A subgroup fixing that vector with a two-group
kernel therefore has three-rank at most one. Applied to the literal
L₁ = O²(N_{LT}(V₁)), this excludes the simple case when m₃(L₁) = 2.
The remaining alternative retains an equivalence to the concrete hexacode
triple cover, not merely its central quotient or a family name.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.16(1),
printed p.952 (PDF p.969), with Notation 13.2.1 on p.877 and the natural
module and model alternatives of 13.5.2, pp.915–916. Those earlier model
alternatives are explicit inputs. The E₄ automizer calculation is separate
and is not asserted in this module.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymmetricSix

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer



private theorem rank_le_one_of_card24 {A : Type*} [Group A] [Finite A] (hc : Nat.card A = 24) :
    primeRank 3 A ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le A).mpr
  intro E hE
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd : 3 ^ n ∣ 24 := by rw [← hn, ← hc]; exact E.card_subgroup_dvd_card
  have hnle : n ≤ 1 := by
    by_contra! h
    have : 9 ∣ 24 := (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd
    norm_num at this
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle

private theorem threeRank_twoGroup {A : Type*} [Group A] [Finite A] (hA : IsPGroup 2 A) :
    primeRank 3 A = 0 := by
  apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn]
  intro hd
  have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hd
  norm_num at this

private noncomputable def pointModel (x : BinaryPoint) :
    MulAction.stabilizer A6 x ≃* a6DuadStabilizer := by
  have he : MulAction.stabilizer A6 x =
      MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
    ext g
    change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
    rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
    simp
  have hg := Classical.choose_spec (a6_duad_transitive 0 (duadPolarEquiv.symm x))
  exact (MulEquiv.subgroupCongr he).trans
    ((MulAction.stabilizerEquivStabilizer hg.symm).symm.trans
      (MulEquiv.subgroupCongr a6_duad_stabilizer_zero))

private theorem point_stabilizer_rank (x : BinaryPoint) :
    primeRank 3 (MulAction.stabilizer A6 x) ≤ 1 := by
  apply rank_le_one_of_card24
  exact (Nat.card_congr (pointModel x).toEquiv).trans a6DuadStabilizer_card

variable {G : Type*} [Group G]

/-- The actual simple quotient and its natural binary module, with the
conjugation action retained. The multiplicative equivalence on V is an
additive (hence F₂-linear) identification with the natural module. -/
structure SimplePointModel (L V : Subgroup G) (hLV : L ≤ normalizer (V : Set G)) where
  quotientEquiv : (L ⧸ pCore 2 L) ≃* A6
  moduleEquiv : V ≃* Multiplicative NaturalModule
  equivariant : ∀ (l : L) (v : V),
    Multiplicative.toAdd (moduleEquiv (V.normalizerMonoidHom (inclusion hLV l) v)) =
      polarAction (quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)).val
        (Multiplicative.toAdd (moduleEquiv v))

/-- A subgroup of L fixing a nonidentity marked vector has three-rank at
most one in the simple A₆ case. Its kernel is proved to be a two-group. -/
theorem simple_marked_rank [Finite G] (L V X : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : SimplePointModel L V hLV)
    (hXL : X ≤ L) (z : V) (hz : z ≠ 1)
    (hfix : ∀ x : X, (x : G) * z.val * (x : G)⁻¹ = z.val) :
    primeRank 3 X ≤ 1 := by
  let f : X →* A6 := d.quotientEquiv.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hXL))
  let v : BinaryPoint := ⟨Multiplicative.toAdd (d.moduleEquiv z),
    d.moduleEquiv.map_ne_one_iff.mpr hz⟩
  have hf : ∀ x : X, f x ∈ MulAction.stabilizer A6 v := by
    intro x
    change (f x).val • v = v
    apply Subtype.ext
    change (polarPointPerm (f x).val v).val = v.val
    rw [← polarAction_point]
    change polarAction (d.quotientEquiv (QuotientGroup.mk' (pCore 2 L)
      (inclusion hXL x))).val (Multiplicative.toAdd (d.moduleEquiv z)) = _
    rw [← d.equivariant]
    have he : V.normalizerMonoidHom (inclusion hLV (inclusion hXL x)) z = z :=
      Subtype.ext (hfix x)
    rw [he]
  let f' : X →* MulAction.stabilizer A6 v := f.codRestrict _ hf
  have hk : f'.ker = (pCore 2 L).comap (inclusion hXL) := by
    rw [MonoidHom.ker_codRestrict]
    ext x
    change d.quotientEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hXL x)) = 1 ↔ _
    rw [d.quotientEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hk2 : IsPGroup 2 f'.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective (inclusion hXL) (inclusion_injective hXL)
  have hr := Theory.GroupTheory.primeRank_le_ker_add (p := 3) f'
  rw [threeRank_twoGroup hk2, zero_add] at hr
  exact hr.trans (point_stabilizer_rank v)

private theorem normalizer_fixes_two (U : Subgroup G) (hc : Nat.card U = 2)
    (z : U) (hz : z ≠ 1) (g : normalizer (U : Set G)) :
    (g : G) * (z : G) * (g : G)⁻¹ = z.val := by
  have hne : U.normalizerMonoidHom g z ≠ 1 :=
    (U.normalizerMonoidHom g).map_ne_one_iff.mpr hz
  have he := (Nat.card_eq_two_iff' (1 : U)).mp hc
  exact congrArg Subtype.val (he.unique hne hz)

/-- N_{LT}(V₁), with normality understood inside the local overgroup. -/
def markedParabolic (L T V₁ : Subgroup G) : Subgroup G :=
  (L ⊔ T) ⊓ normalizer (V₁ : Set G)

/-- The ambient image of O²(N_{LT}(V₁)). -/
def markedResidual (L T V₁ : Subgroup G) : Subgroup G :=
  (pResidual 2 (markedParabolic L T V₁)).map (markedParabolic L T V₁).subtype

/-- The literal residual normalizes its marked line. -/
theorem markedResidual_le_normalizer (L T V₁ : Subgroup G) :
    markedResidual L T V₁ ≤ normalizer (V₁ : Set G) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property.2

/-- Adjoining a normalizing two-group puts the two-residual inside L. -/
theorem markedResidual_le_left (L T V₁ : Subgroup G)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G)) :
    markedResidual L T V₁ ≤ L := by
  let N := L.subgroupOf (L ⊔ T)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  have hq : IsPGroup 2 ((L ⊔ T : Subgroup G) ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N (T.subgroupOf (L ⊔ T)) hT.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  let f : markedParabolic L T V₁ →* ((L ⊔ T : Subgroup G) ⧸ N) :=
    (QuotientGroup.mk' N).comp (inclusion inf_le_left)
  have hk : IsPGroup 2 (markedParabolic L T V₁ ⧸ f.ker) :=
    (hq.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hr : pResidual 2 (markedParabolic L T V₁) ≤ f.ker :=
    sInf_le ⟨inferInstance, hk⟩
  rintro x ⟨y, hy, rfl⟩
  exact (QuotientGroup.eq_one_iff (inclusion (show markedParabolic L T V₁ ≤ L ⊔ T
    from inf_le_left) y)).mp (hr hy)

/-- The simple-case rank bound for the actual marked two-residual. -/
theorem simple_residual_rank [Finite G] (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : SimplePointModel L V hLV)
    (hL₁L : markedResidual L T V₁ ≤ L)
    (hV₁V : V₁ ≤ V) (hV₁ : Nat.card V₁ = 2) :
    primeRank 3 (markedResidual L T V₁) ≤ 1 := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hV₁
  let zV : V := inclusion hV₁V z
  have hzV : zV ≠ 1 := by
    intro he
    apply hz
    exact Subtype.ext (congrArg (fun a : V => (a : G)) he)
  apply simple_marked_rank L V _ hLV d hL₁L zV hzV
  intro x
  exact normalizer_fixes_two V₁ hV₁ z hz
    (inclusion (markedResidual_le_normalizer L T V₁) x)

/-- The marked rank-two input rules out A₆ in the earlier model alternative.
The output is a genuine equivalence to the concrete triple cover. -/
theorem tripleCover_of_marked_rank [Finite G] (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G))
    (hmodels : Nonempty (SimplePointModel L V hLV) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hV₁ : Nat.card V₁ = 2)
    (hrank : primeRank 3 (markedResidual L T V₁) = 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases hmodels with hs | hcover
  · obtain ⟨d⟩ := hs
    have h := simple_residual_rank L T V V₁ hLV d
      (markedResidual_le_left L T V₁ hT hn) hV₁V hV₁
    omega
  · exact hcover

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

end
