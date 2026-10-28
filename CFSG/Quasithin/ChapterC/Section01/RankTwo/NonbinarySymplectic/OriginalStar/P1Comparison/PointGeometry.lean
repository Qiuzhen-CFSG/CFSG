module
public import Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections.Marked
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
public import Theory.ElementaryAbelian.Injective

/-!
# The point parabolic preserves the opposite elementary layer

In the full fixed-core quotient the natural kernel and the opposite critical
center are elementary abelian. The latter projects onto a long root and its
intersection has index q in the natural kernel. Root action identifies that
intersection with the cofixed hyperplane. Every involution in their product
then belongs to one of these two factors. The point parabolic preserves the
product and the natural kernel, so it preserves the other elementary factor.

This is the maximal-elementary argument in MS93 (3.7), printed p.877. It uses
the same natural action and quotient marking throughout, and does not assume
normalization of the opposite layer.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison

variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E] [CharP E 2]

omit [Finite E] in
/-- The geometric normalization clause follows from the elementary pair and
its original natural marking. No action on the final two-dimensional
critical quotient is supplied as a premise. -/
theorem point_parabolic_normalizes_opposite
    (κ : G →* Sp E) (A B : Subgroup G) (hker : κ.ker=A)
    (natural : A ≃* Multiplicative (Vector E))
    (hconj : ∀ (g : G) (x y : A), (y : G)=g*x*g⁻¹ →
      (natural y).toAdd=κ g • (natural x).toAdd)
    (hroot : B.map κ=RootSubgroup.group 0)
    [IsElementaryAbelian 2 B] (hi : B.relIndex A=Nat.card E) :
    (stabilizer (point E)).comap κ ≤ normalizer (B : Set G) := by
  let f : A →* Multiplicative E :=
    coordinate.toAddMonoidHom.toMultiplicative.comp natural.toMonoidHom
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v,hv⟩ := coordinate_surjective x.toAdd
    refine ⟨natural.symm (Multiplicative.ofAdd v),?_⟩
    change Multiplicative.ofAdd (coordinate ((natural (natural.symm _)).toAdd))=x
    rw [natural.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hv
  have root_lift (r : E) : ∃ b : B, κ b=rootElement 0 r := by
    have hr : rootElement 0 r ∈ B.map κ := hroot.symm ▸
      ((RootSubgroup.mem_group_iff 0 _).mpr ⟨r,rfl⟩)
    obtain ⟨b,hb,he⟩ := hr
    exact ⟨⟨b,hb⟩,he⟩
  have hfker : f.ker=B.subgroupOf A := by
    have hle : B.subgroupOf A ≤ f.ker := by
      intro x hx
      obtain ⟨b,hb⟩ := root_lift 1
      have hc : (x : G)=b*x*(b : G)⁻¹ := by
        have hh : (b:G)*x=x*b := congrArg Subtype.val (mul_comm b (⟨x,hx⟩ : B))
        rw [hh,mul_inv_cancel_right]
      have hh := hconj b x x hc
      rw [hb,root_natural] at hh
      have hh' := congrArg (fun v : Vector E => v (.inl 0)) hh
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,one_mul,e,
        Pi.single_eq_same,mul_one] at hh'
      change coordinate (natural x).toAdd=0
      exact add_eq_left.mp hh'.symm
    have he : f.ker.index=(B.subgroupOf A).index := by
      rw [index_ker,MonoidHom.range_eq_top.mpr hf,
        Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative E)) ≃* _).toEquiv]
      exact hi.symm
    apply le_antisymm ?_ hle
    by_contra hn
    exact (ne_of_lt (Subgroup.index_strictAnti (lt_of_le_not_ge hle hn))) he
  let : A.Normal := hker ▸ inferInstance
  let : IsElementaryAbelian 2 (Multiplicative (Vector E)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      change (2 : ℕ) • v.toAdd=0
      rw [two_nsmul]
      ext i
      exact CharTwo.add_self_eq_zero _) }
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_injective natural.toMonoidHom natural.injective
  have hfix : ∀ b ∈ B, b ∉ A → ∀ a ∈ A, Commute b a → a ∈ B := by
    intro b hb hbA a ha hc
    obtain ⟨r,hr⟩ := (RootSubgroup.mem_group_iff 0 (κ b)).mp
      (hroot ▸ mem_map_of_mem κ hb)
    have hr0 : r≠0 := by
      intro he
      apply hbA
      apply hker.le
      change κ b=1
      rw [←hr,he,RootSubgroup.element_zero]
    have hh := hconj b ⟨a,ha⟩ ⟨a,ha⟩ (by
      change a=b*a*b⁻¹
      rw [hc.eq,mul_inv_cancel_right])
    rw [←hr,root_natural] at hh
    have hh' := congrArg (fun v : Vector E => v (.inl 0)) hh
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,e,
      Pi.single_eq_same,mul_one] at hh'
    have hz : coordinate (natural ⟨a,ha⟩).toAdd=0 :=
      (mul_eq_zero.mp (add_eq_left.mp hh'.symm)).resolve_left hr0
    exact (show (⟨a,ha⟩ : A) ∈ B.subgroupOf A from hfker ▸ hz)
  have hspan : A ⊔ B=(RootSubgroup.group (F := E) 0).comap κ := by
    rw [←hroot,comap_map_eq,hker,sup_comm]
  apply le_normalizer_iff.mpr
  intro g hg
  have hmap : B.map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
    rintro _ ⟨b,hb,rfl⟩
    rw [hspan]
    change κ (g*b*g⁻¹) ∈ RootSubgroup.group 0
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (parabolic_normalizes_root hg) (κ b)).mp
      (hroot ▸ mem_map_of_mem κ hb)
  have hpair := elementary_pair_involution_union (A ⊔ B) A B rfl
    (show B ≤ normalizer (A : Set G) from le_normalizer_of_normal) hfix
  let : IsElementaryAbelian 2 (B.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcases := le_one_of_elementwise_union (B.map (MulAut.conj g).toMonoidHom) A B
    (fun b hb => hpair b (hmap hb)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb))
  have hn : ¬ B.map (MulAut.conj g).toMonoidHom ≤ A := by
    intro hh
    obtain ⟨b,hb⟩ := root_lift 1
    have hc : g*(b : G)*g⁻¹ ∈ A := hh (mem_map_of_mem _ b.property)
    have hbA : (b : G) ∈ A := by
      have hz := (inferInstance : A.Normal).conj_mem _ hc g⁻¹
      have he : g⁻¹*(g*(b:G)*g⁻¹)*g=b := by group
      simpa only [inv_inv,he] using hz
    have hb1 : κ b=1 := show b.val ∈ κ.ker from hker.symm ▸ hbA
    have h10 := RootSubgroup.element_injective 0
      (hb.symm.trans (hb1.trans (RootSubgroup.element_zero 0).symm))
    exact one_ne_zero h10
  exact fun b hb => (hcases.resolve_left hn) (mem_map_of_mem _ hb)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
