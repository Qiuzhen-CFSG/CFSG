module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.MaximalNormalizerOddCore

/-!
# The perfect-actor contradiction in the maximal-W quotient

The centerless Bender normal closure of U/W has a solvable Borel normalizer
and a solvable outer automorphism group. Consequently a perfect group
normalizing U/W acts trivially on this normal closure. If it contains U/W,
then U/W lies in the trivial center, contradicting W<U.

The second theorem combines this with the actual maximal-W unique fixed
cosets and odd-core exclusion. A perfect subgroup containing U and
centralizing U normalizes every intervening W, so its image is the required
actor in the literal N(W)/W. This proves that the local stabilizer is the
whole ambient group under those hypotheses.

Source: Aschbacher–Smith F.4.42, final paragraph, printed p.296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitarySource
variable {G : Type*} [Group G] [Finite G]

/-- A centerless Bender normal closure cannot have a nontrivial generating
subgroup inside a perfect subgroup of its ambient normalizer. -/
theorem eq_bot_of_perfect_normalizer
    (V P : Subgroup G) [Group.IsPerfect P]
    (hVP : V ≤ P) (hPN : P ≤ normalizer (V : Set G))
    (hcenter : center (normalClosure (V : Set G)) = ⊥)
    (hquasi : IsQuasisimple (normalClosure (V : Set G)))
    (hmodel : BenderSuzuki.IsSimpleBenderGroup
      (normalClosure (V : Set G) ⧸ center (normalClosure (V : Set G))))
    (hB : Group.IsSolvable (normalizer
      (V.subgroupOf (normalClosure (V : Set G)) : Set (normalClosure (V : Set G))))) :
    V = ⊥ := by
  let K := normalClosure (V : Set G)
  let : IsQuasisimple K := hquasi
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) := hmodel.outer_isSolvable
  let : Group.IsSolvable (MulAut.Outer K) :=
    Group.isSolvable_of_isSolvable_injective
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let : Group.IsSolvable (normalizer (V.subgroupOf K : Set K)) := hB
  let f : P →* MulAut K := (MulAut.conjNormal : G →* MulAut K).comp P.subtype
  have hpres : ∀ a : f.range, ∀ x : K,
      x ∈ V.subgroupOf K ↔ (a : MulAut K) x ∈ V.subgroupOf K := by
    rintro ⟨a,p,rfl⟩ x
    exact mem_normalizer_iff.mp (hPN p.property) x.val
  let : Group.IsSolvable f.range :=
    MulAut.isSolvable_of_preserves_subgroup (V.subgroupOf K) f.range hpres
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have htriv : f.range = ⊥ := by
    by_contra hn
    let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  apply bot_unique
  intro v hv
  let p : P := ⟨v,hVP hv⟩
  have hp : f p = 1 := (mem_bot (G := MulAut K)).mp
    (htriv ▸ (show f p ∈ f.range from ⟨p,rfl⟩))
  have hvK : v ∈ K := le_normalClosure hv
  have hc : (⟨v,hvK⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    have he := congrArg (fun a : MulAut K => (a k).val) hp
    change v * k.val * v⁻¹ = k.val at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have he : (⟨v,hvK⟩ : K) = 1 := (mem_bot (G := K)).mp (hcenter ▸ hc)
  exact mem_bot.mpr (congrArg Subtype.val he)

/-- The maximal-W contradiction, retaining its entire quotient kernel. -/
theorem eq_top_of_perfect_line
    (X U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hUX : U ≤ X) (hZU : Z ≤ U) (hZ : Z ≤ center G)
    (hNU : normalizer (U : Set G) = X)
    (S : Sylow 2 G) (hSX : (S : Subgroup G) ≤ X)
    (z : G) (hzS : z ∈ (S : Subgroup G))
    (hzcentral : ∀ a ∈ (S : Subgroup G), Commute z a)
    (hfix : ∃! q : G ⧸ X, z • q = q)
    (P : Subgroup G) [Group.IsPerfect P]
    (hUP : U ≤ P) (hPC : P ≤ centralizer (U : Set G))
    (hodd : ∀ W : Subgroup G, W ≤ U → pPrimeCore 2 (normalizer (W : Set G)) = ⊥) :
    X = ⊤ := by
  by_contra hX
  obtain ⟨W,hZW,hWU,hWX,hmax,hVne,hYne,hNY,hVe,hVN,hfixV,_,_⟩ :=
    maximal_normalizer_section X U Z hX hUX hZU hZ hNU S hSX z hzS hzcentral hfix
  let N := normalizer (W : Set G)
  let f := QuotientGroup.mk' (W.subgroupOf N)
  let V := (U.subgroupOf N).map f
  let Y := (X.subgroupOf N).map f
  have hPN : P ≤ N :=
    (hPC.trans (centralizer_le hWU.le)).trans (Subgroup.centralizer_le_normalizer _)
  have hPX : P ≤ X := hNU ▸ hPC.trans (Subgroup.centralizer_le_normalizer _)
  have hUN : U ≤ N := hUP.trans hPN
  let : IsElementaryAbelian 2 (U.subgroupOf N) := IsElementaryAbelian.subgroupOf hUN
  obtain ⟨_,hcenter,hquasi,hmodel,hBorel,hB,_⟩ :=
    quotient_bender_of_odd_core (U.subgroupOf N) (W.subgroupOf N)
      (comap_mono hWU.le) (hodd W hWU.le) Y (map_mono (comap_mono hUX))
      hVne hYne hNY hfixV
  let : Group.IsPerfect (P.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPN).symm.surjective
  let : Group.IsPerfect ((P.subgroupOf N).map f) := Group.IsPerfect.map f
  exact hVne (eq_bot_of_perfect_normalizer V ((P.subgroupOf N).map f)
    (map_mono (comap_mono hUP))
    ((map_mono (comap_mono hPX)).trans hNY.ge) hcenter hquasi hmodel
    (hBorel ▸ hB.1))

end CFSG.Quasithin.ChapterF.UnitarySource
