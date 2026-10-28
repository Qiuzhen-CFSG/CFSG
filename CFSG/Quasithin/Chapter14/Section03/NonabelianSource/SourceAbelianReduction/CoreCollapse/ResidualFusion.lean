module

public import Theory.SpecificGroups.G2.BinaryResidualCover
public import Theory.GroupTheory.CentralInvolutionResidualFusion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs

/-!
# The residual splitting and fusion step of original 14.3.22

Here C is the literal ambient centralizer of w, W is its subgroup generated
by w, L is its solvable (perfect) residual embedded back in G, and
J = ⟨w⟩ ∨ L. A supplied isomorphism C/W ≃ G₂(2), through the actual
binary octonion carrier, induces an isomorphism L ≃ G₂(2)′. The lower
model theorem proves injectivity using the odd-parameter PSU₃ central
two-kernel exclusion. The multiplication map identifies J with ⟨w⟩ × L,
and [C : J] = 2. No splitting of the whole C is asserted.

The commutator of C equals its residual, so the source commutator premise
puts z in L. The one involution class of L excludes the wL coset.
Conjugating into the supplied Sylow subgroup and applying outside nonfusion
then proves C controls ambient fusion of z. The last theorem uses the
literal R ∨ Q and original `OutsidePointNonfusion`; all local construction
premises remain explicit for the core-collapse assembly.

Source: Aschbacher--Smith 14.3.22, printed p.999 (PDF p.1016), with the
residual-cover correction in `docs/quasithin-proof-basis.md`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.ResidualFusion
variable {G : Type*} [Group G]

/-- The opposite involution centralizer in the original ambient group. -/
abbrev C (w : G) := centralizer ({w} : Set G)

/-- The marked centralizer element with ambient value w. -/
def point (w : G) : C w := ⟨w, mem_centralizer_singleton_iff.mpr rfl⟩

/-- The actual cyclic subgroup used in the centralizer quotient. -/
def W (w : G) : Subgroup (C w) := zpowers (point w)

/-- The marked involution is central in its own centralizer. -/
theorem point_central (w : G) : point w ∈ center (C w) := by
  exact mem_center_iff.mpr (fun x => Subtype.ext (mem_centralizer_singleton_iff.mp x.property))

/-- The quotient kernel is central, relative to C. -/
theorem W_central (w : G) : W w ≤ center (C w) :=
  zpowers_le.mpr (point_central w)

/-- Normality is in the centralizer, not in the ambient group. -/
instance W_normal (w : G) : (W w).Normal where
  conj_mem a ha g := by
    have hc := mem_center_iff.mp (W_central w ha) g
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using ha

/-- Compatibility with the ambient-generated-subgroup quotient convention. -/
theorem W_eq_subgroupOf (w : G) : W w = (zpowers w).subgroupOf (C w) := by
  change W w = (zpowers w).comap (C w).subtype
  rw [← show (W w).map (C w).subtype = zpowers w from
    (C w).subtype.map_zpowers (point w),
    comap_map_eq_self_of_injective (C w).subtype_injective]

/-- The original perfect residual, embedded in G by inclusion. -/
def L (w : G) : Subgroup G := (solvableResidual (C w)).map (C w).subtype

/-- The embedded residual is contained in the original centralizer. -/
theorem L_le_C (w : G) : L w ≤ C w := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- The residual embedding is an actual group equivalence onto its ambient image. -/
noncomputable def residualEmbeddingEquiv (w : G) : solvableResidual (C w) ≃* L w :=
  (solvableResidual (C w)).equivMapOfInjective (C w).subtype (C w).subtype_injective

/-- The source index-two product subgroup in G. -/
def J (w : G) : Subgroup G := zpowers w ⊔ L w

/-- Both factors of J lie in C, so its relative index is the genuine subgroup index. -/
theorem J_le_C (w : G) : J w ≤ C w :=
  sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) (L_le_C w)

/-- The given recognition composed with the natural centralizer quotient map. -/
def quotientMap (w : G) (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    C w →* Atlas.G2.Model (ZMod 2) := e.toMonoidHom.comp (QuotientGroup.mk' (W w))

/-- The literal recognized quotient map is onto. -/
theorem quotientMap_surjective (w : G) (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    Function.Surjective (quotientMap w e) := e.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The original cyclic subgroup is exactly the recognized quotient kernel. -/
theorem quotientMap_ker (w : G) (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    (quotientMap w e).ker = W w := by
  rw [quotientMap, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- Centrality of the literal recognized quotient kernel. -/
theorem quotientMap_central (w : G) (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    (quotientMap w e).ker ≤ center (C w) := by
  rw [quotientMap_ker]
  exact W_central w

/-- The involution hypothesis makes the kernel have order two. -/
theorem quotientMap_kernel_card (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) : Nat.card (quotientMap w e).ker = 2 := by
  rw [quotientMap_ker, W, Nat.card_zpowers, ← Subgroup.orderOf_coe]
  exact hw

/-- The intrinsic kernel-residual join has exactly the source ambient image. -/
theorem join_map (w : G) :
    (W w ⊔ solvableResidual (C w)).map (C w).subtype = J w := by
  rw [Subgroup.map_sup]
  exact congrArg (fun A : Subgroup G => A ⊔ L w) ((C w).subtype.map_zpowers (point w))

variable [Finite G]

/-- The natural quotient restriction onto the actual derived G₂(2). -/
noncomputable def residualEquiv (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    solvableResidual (C w) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  Atlas.G2.BinaryResidualCover.residualEquiv (quotientMap w e)
    (quotientMap_surjective w e) (quotientMap_central w e) (quotientMap_kernel_card w hw e)

/-- The isomorphism retains the original natural quotient map. -/
theorem residualEquiv_apply (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) (l : solvableResidual (C w)) :
    (residualEquiv w hw e l : Atlas.G2.Model (ZMod 2)) =
      e (QuotientGroup.mk' (W w) l) := rfl

/-- The same isomorphism on the residual embedded in the original G. -/
noncomputable def ambientResidualEquiv (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    L w ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (residualEmbeddingEquiv w).symm.trans (residualEquiv w hw e)

/-- On the ambient residual the isomorphism is still the literal quotient restriction. -/
theorem ambientResidualEquiv_apply (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) (l : L w) :
    (ambientResidualEquiv w hw e l : Atlas.G2.Model (ZMod 2)) =
      e (QuotientGroup.mk' (W w) ⟨l.val, L_le_C w l.property⟩) := by
  change (residualEquiv w hw e ((residualEmbeddingEquiv w).symm l) : Atlas.G2.Model (ZMod 2)) = _
  rw [residualEquiv_apply]
  apply congrArg (fun x : C w => e (QuotientGroup.mk' (W w) x))
  apply Subtype.ext
  calc
    _ = (residualEmbeddingEquiv w ((residualEmbeddingEquiv w).symm l) : G) :=
      (coe_equivMapOfInjective_apply (solvableResidual (C w)) (C w).subtype
        (C w).subtype_injective ((residualEmbeddingEquiv w).symm l)).symm
    _ = _ := congrArg (fun x : L w => (x : G)) ((residualEmbeddingEquiv w).apply_symm_apply l)

/-- Every original centralizer commutator lies in its perfect residual. -/
theorem commutator_eq_residual (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    commutator (C w) = solvableResidual (C w) :=
  Atlas.G2.BinaryResidualCover.commutator_eq_residual (quotientMap w e)
    (quotientMap_surjective w e) (quotientMap_central w e) (quotientMap_kernel_card w hw e)

/-- The source commutator premise supplies z ∈ L; no extra membership premise is added. -/
theorem mem_residual_of_mem_commutator (w z : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2))
    (hz : z ∈ (commutator (C w)).map (C w).subtype) : z ∈ L w := by
  rwa [commutator_eq_residual w hw e] at hz

/-- The genuine internal direct product: the displayed isomorphism is ambient multiplication. -/
theorem internal_product (w : G) (hw : orderOf w = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    ∃ m : zpowers w × L w ≃* J w,
      ∀ a l, (m (a, l) : G) = (a : G) * (l : G) := by
  have hdis : Disjoint (W w) (solvableResidual (C w)) := by
    rw [← quotientMap_ker w e]
    exact residual_disjoint_kernel (quotientMap w e)
      (Atlas.G2.BinaryResidualCover.residualMap_bijective (quotientMap w e)
        (quotientMap_surjective w e) (quotientMap_central w e)
        (quotientMap_kernel_card w hw e)).1
  have hdisG := Subgroup.disjoint_map (C w).subtype_injective hdis
  have hWmap : (W w).map (C w).subtype = zpowers w :=
    (C w).subtype.map_zpowers (point w)
  rw [hWmap] at hdisG
  apply exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hdisG
  apply zpowers_le.mpr
  rintro x ⟨y, _, rfl⟩
  exact mem_centralizer_singleton_iff.mp y.property

/-- The residual product has index two in the original centralizer. -/
theorem join_index (w : G) (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2)) :
    (J w).relIndex (C w) = 2 := by
  change ((J w).comap (C w).subtype).index = 2
  rw [← join_map, comap_map_eq_self_of_injective (C w).subtype_injective,
    ← quotientMap_ker w e]
  exact Atlas.G2.BinaryResidualCover.residual_join_index (quotientMap w e)
    (quotientMap_surjective w e)

/-- The conditional ambient-fusion conclusion on the original centralizer and local Sylow. -/
theorem controls_fusion (w z : G) (hw : orderOf w = 2) (hz : orderOf z = 2)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2))
    (hzD : z ∈ (commutator (C w)).map (C w).subtype)
    (hnon : ¬ IsConj z w) (hopp : IsConj w (w * z))
    (T : Sylow 2 G) (S : Sylow 2 (C w)) (B : Subgroup G)
    (hST : (S : Subgroup (C w)).map (C w).subtype ≤ (T : Subgroup G))
    (hB : (S : Subgroup (C w)).map (C w).subtype ⊓ B ≤ J w)
    (hout : ∀ t ∈ (T : Subgroup G), orderOf t = 2 → t ∉ B → ¬ IsConj z t)
    (a : G) (ha : a ∈ C w) (hza : IsConj z a) :
    ∃ c ∈ C w, c * z * c⁻¹ = a := by
  have hzL := mem_residual_of_mem_commutator w z hw e hzD
  obtain ⟨zC, hzR, rfl⟩ := hzL
  have hzC : orderOf zC = 2 := (Subgroup.orderOf_coe zC).symm.trans hz
  have hclass : ∀ x y : solvableResidual (C w), orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    Atlas.G2.BinaryResidualCover.residual_involutions_isConj (quotientMap w e)
      (quotientMap_surjective w e) (quotientMap_central w e) (quotientMap_kernel_card w hw e)
  have hlocal := fusion_control_of_central_involution_join (C w) (solvableResidual (C w))
    (point w) zC ((Subgroup.orderOf_coe _).symm.trans hw) (point_central w) hzC hzR
    hclass hnon hopp S (T : Subgroup G) B hST
    (by simpa only [← join_map w, W] using hB) hout ⟨a, ha⟩ hza
  obtain ⟨c, hc⟩ := isConj_iff.mp hlocal
  exact ⟨c, c.property, congrArg Subtype.val hc⟩

open Chapter12.Section08 Chapter12.Section08.InvariantFlag

/-- Literal source application with B = R ∨ Q and original 14.3.21(2). -/
theorem controls_fusion_of_outsidePointNonfusion
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2) (K : Subgroup G)
    (hout : OutsidePointNonfusion F K)
    (w z : G) (hw : orderOf w = 2) (hz : orderOf z = 2) (hzV : z ∈ F.Vi 1)
    (e : (C w ⧸ W w) ≃* Atlas.G2.Model (ZMod 2))
    (hzD : z ∈ (commutator (C w)).map (C w).subtype)
    (hnon : ¬ IsConj z w) (hopp : IsConj w (w * z))
    (S : Sylow 2 (C w))
    (hST : (S : Subgroup (C w)).map (C w).subtype ≤ (T : Subgroup G))
    (hB : (S : Subgroup (C w)).map (C w).subtype ⊓
      ((F.I₂ K).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤ J w)
    (a : G) (ha : a ∈ C w) (hza : IsConj z a) :
    ∃ c ∈ C w, c * z * c⁻¹ = a := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  exact controls_fusion w z hw hz e hzD hnon hopp T S
    ((F.I₂ K).pCoreIn 2 ⊔ F.H.pCoreIn 2) hST hB (hout z hzV hz1) a ha hza
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.ResidualFusion
