module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinaryChiefOffender
public import Theory.Representation.BinaryPermutation.SixCoreExtension.InvariantForm

/-!
# Two genuine module obstructions in the binary M₂₂ source case

Retain the constructed minimal normal W, actual faithful irreducible action
of M/C_M(W), literal A₆ section, augmentation-core embedding, covering-center
marking and paired-four offender. Its A₆ action admits no invariant
nondegenerate bilinear form: the nonzero constant line lies in every such
form's radical.

The full quotient action is also not transitive on nonzero vectors. Such
transitivity would lift to conjugation by an element of M sending a
nontrivial element of the original Z(L) to the original z. Since C_G(z)≤M,
this would put L inside M, contradicting the source setup.

These rule out the two concrete model behaviors. The separate B.5.6
comparison must still show that the actual offender-generated group has
one of them; that classification is not an input or conclusion here.
Source: Aschbacher--Smith 2.3.9(7), pp.525–526; B.3 and B.5.
-/

public section
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers M22Local Sporadic.Mathieu.M22CentralCover
open BinaryPermutation BinaryPermutation.SixCoreExtension
open Representation Representation.BinaryOffender Representation.NormalElementaryQuotient
variable {G : Type*} [Group G] [Finite G] {L M : Subgroup G}
variable {C : GroupClass} {H : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual chief offender has neither an A₆-invariant nondegenerate
form nor transitivity on its nonzero vectors. All marked source data is retained. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_chief_module_obstructions
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      B ∈ m22Blocks ∧ ∃ W : Subgroup M,
        W.Normal ∧ W ≠ ⊥ ∧ W ≤ pCore 2 M ∧ IsElementaryAbelian 2 W ∧
        (∀ U : Subgroup M, U.Normal → U ≤ W → U = ⊥ ∨ U = W) ∧
        z ∈ W.map M.subtype ∧
        W.map M.subtype = (hexadRadical e B).map L.subtype ⊔
          (W.map M.subtype ⊓ centralizer (L : Set G)) ∧
        ∀ (hn : W.Normal) (hE : IsElementaryAbelian 2 W),
          letI : W.Normal := hn
          letI : IsElementaryAbelian 2 W := hE
          let q := QuotientGroup.mk' (centralizer (W : Set M))
          let ρ := NormalElementaryQuotient.representation W q
            (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
          Function.Injective ρ ∧ IsIrreducible ρ ∧
          ∃ f : A →* M, Function.Injective (q.comp f) ∧
            ∃ j : V →ₗ[ZMod 2] Additive W, Function.Injective j ∧
              (∀ a v, j (coreAltRepresentation a v) = ρ (q (f a)) (j v)) ∧
              j.range ⊔ Representation.invariants (ρ.comp (q.comp f)) = ⊤ ∧
              (∀ v, (((j v).toMul : M) : G) ∈ (center L).map L.subtype ↔
                coreToNatural (Fin 6) v = 0) ∧
              IsOffender ρ (pairedFour.map (q.comp f)) ∧
        (q.comp f).range ≤ offenderSubgroup ρ ∧
              (∀ B : LinearMap.BilinForm (ZMod 2) (Additive W),
                (∀ a v w, B (ρ (q (f a)) v) (ρ (q (f a)) w) = B v w) → ¬ B.Nondegenerate) ∧
              ¬ (∀ v w : Additive W, v ≠ 0 → w ≠ 0 → ∃ x, ρ x v = w) := by
  dsimp only
  obtain ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,hsplit,hdata⟩ :=
    c.mathieuTwentyTwo_binary_chief_offender hG sourceC d hc
  refine ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,hsplit,?_⟩
  intro hn hE
  let : W.Normal := hn
  let : IsElementaryAbelian 2 W := hE
  let q := QuotientGroup.mk' (centralizer (W : Set M))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨hfaith,hirr,f,hf,j,hj,hact,hgen,hcenter,hoff,hJ⟩ := hdata hn hE
  refine ⟨hfaith,hirr,f,hf,j,hj,hact,hgen,hcenter,hoff,hJ,?_,?_⟩
  · intro B hInv
    exact not_nondegenerate_of_fixed_supplement (ρ.comp (q.comp f)) j hj hact hgen B hInv
  · intro htrans
    let h := c.localSetup hG structural115Input sourceC
    have hk0 : j constant ≠ 0 := by
      intro he
      have he' : constant = 0 := hj (he.trans j.map_zero.symm)
      exact (by decide : constant ≠ 0) he'
    have hconst : coreToNatural (Fin 6) constant = 0 := by
      apply Subtype.ext
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have he : constant.val = allOne (Fin 6) := by decide
      change constant.val ∈ constants (Fin 6)
      rw [he]
      exact Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨k,hk,hke⟩ := (hcenter constant).mpr hconst
    obtain ⟨zm,hzm,hze⟩ := hzW
    let zw : Additive W := Additive.ofMul ⟨zm,hzm⟩
    have hz0 : zw ≠ 0 := by
      intro hz0
      have he : (zm : G) = 1 := congrArg (fun a : Additive W => ((a.toMul : M) : G)) hz0
      change (zm : G) = z at hze
      have hz1 : z = 1 := hze.symm.trans he
      have ho := c.involution
      rw [hz1,orderOf_one] at ho
      omega
    obtain ⟨x,hx⟩ := htrans (j constant) zw hk0 hz0
    obtain ⟨m,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (W : Set M)) x
    have hconj := congrArg (fun a : Additive W => ((a.toMul : M) : G)) hx
    change (k : G) = (((j constant).toMul : M) : G) at hke
    change (zm : G) = z at hze
    rw [NormalElementaryQuotient.representation_apply] at hconj
    change (m : G) * (((j constant).toMul : M) : G) * (m : G)⁻¹ = (zm : G) at hconj
    rw [← hke,hze] at hconj
    apply h.outside
    intro l hl
    have hcL : (m : G) * l * (m : G)⁻¹ ∈ centralizer ({z} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hkl : (k : G) * l = l * (k : G) :=
        (congrArg Subtype.val (mem_center_iff.mp hk (⟨l,hl⟩ : L))).symm
      rw [← hconj]
      calc
        ((m : G) * l * (m : G)⁻¹) * ((m : G) * (k : G) * (m : G)⁻¹) =
          (m : G) * (l * (k : G)) * (m : G)⁻¹ := by group
        _ = (m : G) * ((k : G) * l) * (m : G)⁻¹ := by rw [hkl]
        _ = ((m : G) * (k : G) * (m : G)⁻¹) * ((m : G) * l * (m : G)⁻¹) := by group
    have hm := M.mul_mem (M.mul_mem (M.inv_mem m.property) (h.centralizer_le hcL)) m.property
    have he : (m : G)⁻¹ * ((m : G) * l * (m : G)⁻¹) * (m : G) = l := by group
    rwa [he] at hm

end CFSG.Quasithin.Chapter2.ComponentRefinement
