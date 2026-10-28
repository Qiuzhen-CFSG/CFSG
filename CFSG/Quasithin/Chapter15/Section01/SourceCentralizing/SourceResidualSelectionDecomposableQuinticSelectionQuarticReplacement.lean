module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwap
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwap

/-!
# Replacement from large intersections with both original supports

Each support action has order at most two. An eight-element intersection
with a support cannot lie inside its nontrivial four-element fixed group.
The two fixed-point indices multiply on the direct product of the two
intersections, so they dominate the full action index. Maximum elementary
replacement puts W in J(Q). The Thompson-center envelope then centralizes
both large intersections, and hence both entire supports.

The `import all` is an intentional internal proof split: it reuses the
already checked maximum-elementary cardinal replacement lemma from
SelectionSwap without changing that frozen file's public interface.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_index_product_of_disjoint
    (X Y A : Subgroup G) (hd : Disjoint X Y)
    (hXY : X≤centralizer (Y:Set G))
    (hAX : A≤normalizer (X:Set G)) (hAY : A≤normalizer (Y:Set G)) :
    (centralizer (A:Set G)).relIndex (X⊔Y)=
      (centralizer (A:Set G)).relIndex X*(centralizer (A:Set G)).relIndex Y := by
  let CX := X⊓centralizer (A:Set G)
  let CY := Y⊓centralizer (A:Set G)
  have hYX : Y≤normalizer (X:Set G) :=
    (le_centralizer_iff.mp hXY).trans (Subgroup.centralizer_le_normalizer _)
  have hfix : (X⊔Y)⊓centralizer (A:Set G)=CX⊔CY := by
    apply le_antisymm
    · intro z hz
      have hzprod : z∈(X:Set G)*(Y:Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left X Y hYX]
        exact hz.1
      obtain ⟨x,hx,y,hy,rfl⟩ := hzprod
      have hf (a:G) (ha:a∈A) : a*x*a⁻¹=x ∧ a*y*a⁻¹=y := by
        have hx' : a*x*a⁻¹∈X := (mem_normalizer_iff.mp (hAX ha) x).mp hx
        have hy' : a*y*a⁻¹∈Y := (mem_normalizer_iff.mp (hAY ha) y).mp hy
        have he : (a*x*a⁻¹)*(a*y*a⁻¹)=x*y := by
          calc
            _ = a*(x*y)*a⁻¹ := by group
            _ = x*y := by rw [hz.2 a ha,mul_inv_cancel_right]
        have hh := mul_injective_of_disjoint hd
          (a₁:=(⟨a*x*a⁻¹,hx'⟩,⟨a*y*a⁻¹,hy'⟩)) (a₂:=(⟨x,hx⟩,⟨y,hy⟩)) he
        exact ⟨congrArg (fun u:X×Y => (u.1:G)) hh,congrArg (fun u:X×Y => (u.2:G)) hh⟩
      exact mul_mem_sup ⟨hx,fun a ha => mul_inv_eq_iff_eq_mul.mp (hf a ha).1⟩
        ⟨hy,fun a ha => mul_inv_eq_iff_eq_mul.mp (hf a ha).2⟩
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  have hcc : CY≤normalizer (CX:Set G) :=
    ((show CY≤Y from inf_le_left).trans
      ((le_centralizer_iff.mp hXY).trans (centralizer_le (show CX≤X from inf_le_left)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hcard := card_sup_eq_mul_of_normalizes_of_disjoint X Y hYX hd
  have hcardC := card_sup_eq_mul_of_normalizes_of_disjoint CX CY hcc
    (hd.mono inf_le_left inf_le_left)
  have hx : Nat.card CX*(centralizer (A:Set G)).relIndex X=Nat.card X := by
    simpa only [CX,relIndex_bot_left,inf_relIndex_left] using
      relIndex_mul_relIndex (⊥:Subgroup G) CX X bot_le inf_le_left
  have hy : Nat.card CY*(centralizer (A:Set G)).relIndex Y=Nat.card Y := by
    simpa only [CY,relIndex_bot_left,inf_relIndex_left] using
      relIndex_mul_relIndex (⊥:Subgroup G) CY Y bot_le inf_le_left
  have hxy : Nat.card ((X⊔Y)⊓centralizer (A:Set G) : Subgroup G)*
      (centralizer (A:Set G)).relIndex (X⊔Y)=Nat.card (X⊔Y : Subgroup G) := by
    simpa only [relIndex_bot_left,inf_relIndex_left] using
      relIndex_mul_relIndex (⊥:Subgroup G) ((X⊔Y)⊓centralizer (A:Set G)) (X⊔Y) bot_le inf_le_left
  rw [hfix,hcardC,hcard] at hxy
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.card_pos (α:=CX)) (Nat.card_pos (α:=CY)))
  calc
    _ = Nat.card X*Nat.card Y := hxy
    _ = _ := by rw [←hx,←hy]; ring

omit [Finite G] in
private theorem centralizer_join (X Y : Subgroup G) :
    centralizer ((X⊔Y : Subgroup G) : Set G)=centralizer (X:Set G)⊓centralizer (Y:Set G) := by
  apply le_antisymm (le_inf
    (centralizer_le (show X≤X⊔Y from le_sup_left))
    (centralizer_le (show Y≤X⊔Y from le_sup_right)))
  intro a ha
  have hh : X⊔Y≤centralizer ({a}:Set G) := sup_le
    (fun x hx => mem_centralizer_singleton_iff.mpr (ha.1 x hx))
    (fun y hy => mem_centralizer_singleton_iff.mpr (ha.2 y hy))
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hh hx)

/-- Large intersections with both supports dominate every elementary action
index. Thus W lies in J(Q), and any central envelope with the same support
fixed-point bounds centralizes the whole original module. -/
theorem DecomposableMarker.maxJ_envelope_centralizes_of_large_support_intersections
    (Q V W V₁ V₂ F : Subgroup G) [IsElementaryAbelian 2 V]
    (hWV : W≤V) (hWQ : W≤Q) (hV : V₁⊔V₂=V) (hd : Disjoint V₁ V₂)
    (hc₁ : 8≤Nat.card (W⊓V₁ : Subgroup G)) (hc₂ : 8≤Nat.card (W⊓V₂ : Subgroup G))
    (hFC : F≤centralizer (elementaryAbelianMaxJ Q:Set G))
    (hact : ∀A∈elementaryAbelianMaxSubgroups Q,
      A≤normalizer (W:Set G) ∧ A≤normalizer (V₁:Set G) ∧ A≤normalizer (V₂:Set G) ∧
      (centralizer (V₁:Set G)).relIndex A≤2 ∧ (centralizer (V₂:Set G)).relIndex A≤2 ∧
      (¬A≤centralizer (V₁:Set G) → Nat.card (V₁⊓centralizer (A:Set G) : Subgroup G)≤4) ∧
      (¬A≤centralizer (V₂:Set G) → Nat.card (V₂⊓centralizer (A:Set G) : Subgroup G)≤4))
    (hFfixed : ∀f∈F,
      (f∉centralizer (V₁:Set G) → Nat.card (V₁⊓centralizer ({f}:Set G) : Subgroup G)≤4) ∧
      (f∉centralizer (V₂:Set G) → Nat.card (V₂⊓centralizer ({f}:Set G) : Subgroup G)≤4)) :
    W≤elementaryAbelianMaxJ Q ∧ F≤centralizer (V:Set G) := by
  let W₁ := W⊓V₁
  let W₂ := W⊓V₂
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hW₁W₂ : W₁≤centralizer (W₂:Set G) :=
    (show W₁≤V from inf_le_left.trans hWV).trans
      (V.le_centralizer.trans (centralizer_le (show W₂≤V from inf_le_left.trans hWV)))
  have hWJ : W≤elementaryAbelianMaxJ Q := by
    apply maxJ_contains_elementary_of_large_fixed_index Q W hWQ
    intro A hA _
    obtain ⟨hAW,hA₁,hA₂,hi₁,hi₂,hfix₁,hfix₂⟩ := hact A hA
    have hi (Vi:Subgroup G) (hcard:8≤Nat.card (W⊓Vi : Subgroup G))
        (ha:(centralizer (Vi:Set G)).relIndex A≤2)
        (hf:¬A≤centralizer (Vi:Set G) → Nat.card (Vi⊓centralizer (A:Set G) : Subgroup G)≤4) :
        (centralizer (Vi:Set G)).relIndex A≤(centralizer (A:Set G)).relIndex (W⊓Vi) := by
      by_cases hc:A≤centralizer (Vi:Set G)
      · rw [relIndex_eq_one.mpr hc]
        exact Nat.one_le_iff_ne_zero.mpr ((centralizer (A:Set G)).subgroupOf (W⊓Vi)).index_ne_zero_of_finite
      have hcf : Nat.card ((W⊓Vi)⊓centralizer (A:Set G) : Subgroup G)≤4 :=
        (card_le_of_le (inf_le_inf_right _ inf_le_right)).trans (hf hc)
      have he : Nat.card ((W⊓Vi)⊓centralizer (A:Set G) : Subgroup G)*
          (centralizer (A:Set G)).relIndex (W⊓Vi)=Nat.card (W⊓Vi : Subgroup G) := by
        simpa only [relIndex_bot_left,inf_relIndex_left] using
          relIndex_mul_relIndex (⊥:Subgroup G) ((W⊓Vi)⊓centralizer (A:Set G)) (W⊓Vi) bot_le inf_le_left
      have hlo : 2≤(centralizer (A:Set G)).relIndex (W⊓Vi) := by nlinarith
      exact ha.trans hlo
    have hprod := fixed_index_product_of_disjoint W₁ W₂ A
      (hd.mono inf_le_right inf_le_right) hW₁W₂
      ((le_inf hAW hA₁).trans inf_normalizer_le_normalizer_inf)
      ((le_inf hAW hA₂).trans inf_normalizer_le_normalizer_inf)
    calc
      (centralizer (W:Set G)).relIndex A ≤ (centralizer (V:Set G)).relIndex A :=
        relIndex_le_of_le_left (centralizer_le hWV)
          ((centralizer (V:Set G)).subgroupOf A).index_ne_zero_of_finite
      _ = (centralizer (V₁:Set G)⊓centralizer (V₂:Set G)).relIndex A := by rw [←hV,centralizer_join]
      _ ≤ (centralizer (V₁:Set G)).relIndex A*(centralizer (V₂:Set G)).relIndex A := relIndex_inf_le
      _ ≤ (centralizer (A:Set G)).relIndex W₁*(centralizer (A:Set G)).relIndex W₂ :=
        Nat.mul_le_mul (hi V₁ hc₁ hi₁ hfix₁) (hi V₂ hc₂ hi₂ hfix₂)
      _ = (centralizer (A:Set G)).relIndex (W₁⊔W₂) := hprod.symm
      _ ≤ (centralizer (A:Set G)).relIndex W :=
        relIndex_le_of_le_right (sup_le inf_le_left inf_le_left)
          ((centralizer (A:Set G)).subgroupOf W).index_ne_zero_of_finite
  have hFW : F≤centralizer (W:Set G) := hFC.trans (centralizer_le hWJ)
  have hc (Vi:Subgroup G) (hcard:8≤Nat.card (W⊓Vi : Subgroup G))
      (hf:∀f∈F, f∉centralizer (Vi:Set G) → Nat.card (Vi⊓centralizer ({f}:Set G) : Subgroup G)≤4) :
      F≤centralizer (Vi:Set G) := by
    intro f hfF
    by_contra hn
    have hl : W⊓Vi≤Vi⊓centralizer ({f}:Set G) :=
      le_inf inf_le_right (fun w hw => mem_centralizer_singleton_iff.mpr (hFW hfF w hw.1))
    have hh := (card_le_of_le hl).trans (hf f hfF hn)
    omega
  refine ⟨hWJ,?_⟩
  rw [←hV,centralizer_join]
  exact le_inf (hc V₁ hc₁ (fun f hf => (hFfixed f hf).1))
    (hc V₂ hc₂ (fun f hf => (hFfixed f hf).2))

end CFSG.Quasithin.Chapter15.Section01
