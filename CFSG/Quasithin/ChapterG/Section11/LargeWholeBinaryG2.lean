module
public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
public import Theory.Representation.G2BinaryDerivedRatios
public import Theory.SpecificGroups.G2.BinaryElementaryRank
public import Theory.LinearAlgebra.AlternatingFinrank

/-!
# Recognizing the entire binary G2 action from its whole component

The actor's half-degree bound forces degree six and actor rank three.
The genuine component recognition extends to an embedding in G2(2).
The actor is too large to lie in its derived group, so the embedding is
surjective. The resulting CaseSix includes the actual module coordinates.
The original HS consumer uses its already checked G2(2) exclusion.
Source: Aschbacher--Smith G.9.3(10), G.11.2(6), 14.3.24, pp.354,364,1000.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.LargeWhole
open Section09 Section09.DefiningCharacteristic
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X} {C : GroupClass}

/-- Whole-component recognition gives the literal full G2(2) natural action. -/
theorem caseSix_of_binary_g2
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : ComponentHypothesis C ρ X L L (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X))
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) : CaseSix ρ := by
  let : L.Normal := h9.normal_H
  let : IsIrreducible (ρ.comp L.subtype) := h9.irreducible
  have hr := h9.toSetup.rank_le_automorphisms (L := L) (by
    rw [normalizer_eq_top_iff.mpr h9.normal_H]
    exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e),
    ← primeRank_equiv 2 Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv] at hr
  have hb : primeRank 2 (Atlas.G2.Model (ZMod 2)) ≤ 3 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro A hA
    let := hA
    exact Atlas.G2.binary_elementary_card_le_eight A
  have hl := hlarge
  have hd6 : finrank (ZMod 2) V = 6 := by
    obtain ⟨n,hn⟩ := (AlternatingForm.even_finrank B h.alternating h.nondegenerate)
    omega
  have hm3 : finrank (ZMod 2) (Additive X) = 3 := by omega
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  obtain ⟨a,c,hc⟩ := G2Recognition.BinarySix.quasiequivalent_of_finrank_eq_six σ hd6
  let E := e.trans a
  let c' : V ≃ₗ[ZMod 2] Atlas.G2.Natural.BinaryNormalizer.N :=
    LinearEquiv.ofBijective (c.toAddMonoidHom.toZModLinearMap 2) c.bijective
  have hE (l : L) (w : V) :
      c' (ρ l w) =
        Atlas.G2.Natural.derivedAction (ZMod 2) (E l) (c' w) := by
    change c (ρ l w) =
      Atlas.G2.Natural.action (ZMod 2) (a (e l)).val (c w)
    have he := hc (e l) w
    simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,
      Subgroup.coe_subtype,G2Recognition.derivedNaturalBinary_apply,
      G2Recognition.naturalBinary_apply] using he
  obtain ⟨f,hf,hfL,hact⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    ρ L E c' hE h.faithful
  have hder : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range := by
    intro x hx
    obtain ⟨l,hl⟩ := E.surjective ⟨x,hx⟩
    exact ⟨l,(hfL l).trans (congrArg Subtype.val hl)⟩
  let A := X.map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hcard : Nat.card A = 8 := by
    rw [Subgroup.card_map_of_injective hf,h9.card_actor,hm3]
    norm_num
  have hnot : ¬ A ≤ commutator (Atlas.G2.Model (ZMod 2)) := by
    intro hA
    let D := commutator (Atlas.G2.Model (ZMod 2))
    let E := A.subgroupOf D
    have hcardE : Nat.card E = 8 :=
      (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans hcard
    have he : IsElementaryTwo E := by
      refine ⟨?_,IsElementaryAbelian.subgroupOf hA⟩
      intro hz
      rw [hz,card_bot] at hcardE
      omega
    have hh := Atlas.G2.Natural.BinaryNormalizer.derived_rank_le_two E he
    rw [Representation.BinaryOffender.rank,hcardE] at hh
    norm_num at hh
  obtain ⟨x,hx,hxd⟩ := SetLike.not_le_iff_exists.mp hnot
  have htop : f.range = ⊤ := Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le
    hder ((Subgroup.map_le_range f _ ) hx) hxd
  exact ⟨hd6,MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp htop⟩,c',hact⟩

end CFSG.Quasithin.ChapterG.Section11.LargeWhole
