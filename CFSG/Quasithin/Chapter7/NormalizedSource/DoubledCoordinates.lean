module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.Representation.ElementaryPerfectSplit
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Coordinates on the marked doubled orbit

Multiplication identifies the two disjoint conjugate seeds with their
whole elementary abelian orbit. On these coordinates the original actor
acts on the first seed and on its inverse-conjugation twist in the second
coordinate. The intertwining formula retains the actual conjugator.

This is the coordinate preparation for the middle rows of Table 7.1.1;
it does not identify that twist with a graph automorphism or prove any
numerical bounds. Its chosen-module application is NonFFSourceDoubledSetup.
Source: Aschbacher--Smith D.3.10 and 7.1, printed pp.201 and696--697.
-/


open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource
variable {G : Type*} [Group G] (L V W : Subgroup G)
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]

def doubledSeedAction (hLV : L ≤ normalizer (V : Set G)) :
    Representation (ZMod 2) L (Additive V) :=
  elementaryRepresentation (V.normalizerMonoidHom.comp (inclusion hLV))

def doubledTwist (t : G) (htL : t ∈ normalizer (L : Set G)) : MulAut L :=
  L.normalizerMonoidHom ⟨t⁻¹, inv_mem htL⟩

def doubledPairAction (hLV : L ≤ normalizer (V : Set G))
    (t : G) (htL : t ∈ normalizer (L : Set G)) :
    Representation (ZMod 2) L (Additive V × Additive V) :=
  (doubledSeedAction L V hLV).prod
    ((doubledSeedAction L V hLV).comp (doubledTwist L t htL).toMonoidHom)

theorem exists_doubled_coordinates (t : G)
    (hW : W = V ⊔ V.map (MulAut.conj t).toMonoidHom)
    (hd : V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥) :
    ∃ e : (Additive V × Additive V) ≃ₗ[ZMod 2] Additive W,
      ∀ v w, ((e (v,w)).toMul : G) =
        (v.toMul : G) * (t * (w.toMul : G) * t⁻¹) := by
  have hVW : V ≤ W := hW ▸ le_sup_left
  have hBW : V.map (MulAut.conj t).toMonoidHom ≤ W := hW ▸ le_sup_right
  have hc : V ≤ centralizer (V.map (MulAut.conj t).toMonoidHom : Set G) := by
    intro v hv w hw
    exact congrArg Subtype.val (mul_comm (⟨w,hBW hw⟩ : W) ⟨v,hVW hv⟩)
  obtain ⟨m,hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    V (V.map (MulAut.conj t).toMonoidHom) (disjoint_iff.mpr hd) hc
  let c := V.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  let f : V × V ≃* W := ((MulEquiv.refl V).prodCongr c).trans
    (m.trans (MulEquiv.subgroupCongr hW.symm))
  let a : (Additive V × Additive V) ≃+ Additive W :=
    (AddEquiv.prodAdditive V V).symm.trans f.toAdditive
  refine ⟨a.toLinearEquiv (ZMod.map_smul a), ?_⟩
  intro v w
  exact hm v.toMul (c w.toMul)

theorem doubled_coordinates_intertwine
    (hLV : L ≤ normalizer (V : Set G))
    (hLW : L ≤ normalizer (W : Set G))
    (t : G) (htL : t ∈ normalizer (L : Set G))
    (e : (Additive V × Additive V) ≃ₗ[ZMod 2] Additive W)
    (he : ∀ v w, ((e (v,w)).toMul : G) =
      (v.toMul : G) * (t * (w.toMul : G) * t⁻¹))
    (l : L) (p : Additive V × Additive V) :
    e (doubledPairAction L V hLV t htL l p) =
      doubledSeedAction L W hLW l (e p) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((e (doubledSeedAction L V hLV l p.1,
    doubledSeedAction L V hLV (doubledTwist L t htL l) p.2)).toMul : G) =
      (l : G) * ((e p).toMul : G) * (l : G)⁻¹
  rw [he, show ((e p).toMul : G) = _ from he p.1 p.2]
  simp only [doubledSeedAction, elementaryRepresentation_apply,
    MonoidHom.comp_apply, doubledTwist]
  change (V.normalizerMonoidHom (inclusion hLV l) p.1.toMul : G) *
    (t * (V.normalizerMonoidHom (inclusion hLV
      (L.normalizerMonoidHom ⟨t⁻¹, inv_mem htL⟩ l)) p.2.toMul : G) * t⁻¹) = _
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  group

end CFSG.Quasithin.Chapter7.NormalizedSource
