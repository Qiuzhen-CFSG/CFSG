module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.ModuleRank
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.Cubics
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The original full moved module of B.2.16

Take the actual space moved by the full cubic product, inside the supplied
conjugation module, and embed its additive group in the original local
group. The module is normal and elementary, and its order is determined
by the natural planes. The global Thompson image acts faithfully on it:
an element fixing all those planes already fixes the complementary fixed
space in B.2.16's internal module sum.

Source: Aschbacher--Smith B.2.16 and the B.6.10 application in15.4.11,
printed pp.79,117 and1160.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open Chapter1.RadicalNormalizers.ThompsonSource FamilySource.ThompsonFactors
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure S)]

def fullMoved (d : Exceptional S) : Submodule (ZMod 2) (Additive (closure S)) :=
  subspaceCommutator d.representation ⊤ (cubicProduct d Finset.univ)

def moduleGroup (d : Exceptional S) : Subgroup H :=
  (binarySubgroup (fullMoved d)).map (closure S).subtype

theorem moduleGroup_le (d : Exceptional S) : moduleGroup d ≤ closure S := map_subtype_le _

theorem mem_moduleGroup (d : Exceptional S) (v : closure S) :
    (v : H) ∈ moduleGroup d ↔ Additive.ofMul v ∈ fullMoved d := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

instance moduleGroup_elementary (d : Exceptional S) : IsElementaryAbelian 2 (moduleGroup d) :=
  IsElementaryAbelian.of_le (moduleGroup_le d)

theorem fullMoved_stable (d : Exceptional S) :
    (⊤ : Subgroup (Star (S := S))) ≤ subspaceStabilizer d.representation (fullMoved d) := by
  let := cubicProduct_normal d
  apply subspaceCommutator_invariant_normalizer
  · intro a _ v
    simp only [Submodule.mem_top]
  · rw [normalizer_eq_top]

instance moduleGroup_normal (d : Exceptional S) : (moduleGroup d).Normal where
  conj_mem := by
    rintro _ ⟨v,hv,rfl⟩ g
    refine ⟨(d.representation (starMap (closure S) g) (Additive.ofMul v)).toMul,?_,?_⟩
    · exact (fullMoved_stable d (mem_top _) (Additive.ofMul v)).mpr hv
    · exact d.conjugation g v

variable [Finite H]

omit [Finite H] in
theorem moduleGroup_le_sylow (d : Exceptional S) : moduleGroup d ≤ (S : Subgroup H) :=
  (IsElementaryAbelian.isPGroup 2 _).le_sylow_of_normal S

theorem moduleGroup_card (d : Exceptional S) (hc : d.count = 1 ∨ d.count = 2) :
    Nat.card (moduleGroup d) = 2^(2*d.count) := by
  classical
  have hi : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
      (Finset.univ : Finset (Fin d.count)).card = 2 := by simpa using hc
  rw [moduleGroup,card_map_of_injective (closure S).subtype_injective,binarySubgroup_card]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  change 2 ^ Module.finrank (ZMod 2)
    (subspaceCommutator d.representation ⊤ (cubicProduct d Finset.univ)) = _
  rw [cubicProduct_moved_finrank d Finset.univ hi,Finset.card_univ,Fintype.card_fin]

/-- On the global Thompson image, the full moved space has trivial kernel. -/
theorem thompson_faithful_on_fullMoved (d : Exceptional S)
    (a : Star (S := S)) (ha : a ∈ thompsonImage (S := S))
    (hfix : ∀ w ∈ fullMoved d, d.representation a w = w) : a = 1 := by
  classical
  apply representation_injective d
  rw [map_one]
  apply LinearMap.ext
  intro v
  change d.representation a v = v
  obtain ⟨⟨f,p⟩,rfl⟩ := d.moduleSum.surjective v
  have hp : d.moduleSum (0,p) ∈ fullMoved d := by
    let l := d.moduleSum.toLinearMap.comp (LinearMap.inr (ZMod 2) _ _)
    have he : p = ∑ i : Fin d.count, Pi.single i (p i) := by
      funext i
      simp
    change l p ∈ fullMoved d
    rw [he,map_sum]
    apply Submodule.sum_mem
    intro i _
    change d.moduleSum (0,Pi.single i (p i)) ∈ fullMoved d
    rw [d.moduleSum_single]
    change (p i).val ∈ subspaceCommutator d.representation ⊤ (cubicProduct d Finset.univ)
    rw [cubicProduct_moved]
    exact (Finset.le_sup (f := plane d) (Finset.mem_univ i)) (p i).property
  have hsplit : d.moduleSum (f,p) = d.moduleSum (f,0) + d.moduleSum (0,p) := by
    rw [←map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  rw [hsplit,map_add,d.moduleSum_fixed,hfix _ hp]
  exact congrArg (fun z => z + d.moduleSum (0,p)) (f.property ⟨a,ha⟩)

/-- Canonical conjugation on the embedded moved group detects exactly
the star kernel for every element in the global Thompson preimage. -/
theorem centralizer_star_eq_one (d : Exceptional S) (g : H)
    (hg : starMap (closure S) g ∈ thompsonImage (S := S))
    (hgw : g ∈ centralizer (moduleGroup d : Set H)) :
    starMap (closure S) g = 1 := by
  apply thompson_faithful_on_fullMoved d _ hg
  intro w hw
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((d.representation (starMap (closure S) g) (Additive.ofMul w.toMul)).toMul : H) = _
  rw [d.conjugation]
  have hm : (w.toMul : H) ∈ moduleGroup d := (mem_moduleGroup d w.toMul).mpr hw
  exact mul_inv_eq_iff_eq_mul.mpr (hgw _ hm).symm

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
