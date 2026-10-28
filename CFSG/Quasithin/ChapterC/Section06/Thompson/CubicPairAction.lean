module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicCoordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.BinaryPair
public import Theory.GroupTheory.DisjointCommutingProduct
/-!
# The paired cubic blocks give the actual binary pair-swap action

The two original order-four modules are disjoint and commute. Their binary
coordinates identify their product with the five-letter even-weight core.
The two noncommuting conjugate factors supply the two independent pair-swap
actors. Thus the literal action has the required core centralizer kernel and
full four-group image, including on the original opposite module.

Source: Aschbacher–Smith C.6.1, paired A₃ branch, printed p.165.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open BinaryPair
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
variable {F F' : Type*} [Field F] [Field F']

omit [Finite G] in
theorem cubic_module_disjoint (hA : IsAlternatingBlock K 3) (D : Subgroup G)
    (hDK : D ≤ centralizer (K : Set G)) : Disjoint (U K) D := by
  apply disjoint_def.mpr
  intro u hu hd
  obtain ⟨v,hv,rfl⟩ := hu
  have hc : v ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hDK hd k k.property)
  have hf : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := hc
  rw [alternatingThreeCoverInput K hA,mem_bot] at hf
  exact congrArg (fun z : blockU K => ((z : K) : G)) hf

noncomputable def Setup.paired_cubic_action
    (h : Setup R K F) (h' : Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3) : S R →* Perm :=
  BinaryPair.actor.comp ((h.cubic_parameter hK).prod (h'.cubic_parameter hL))

omit [Finite G] in
private theorem centralizer_join (A B : Subgroup G) :
    centralizer (A ⊔ B : Subgroup G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · exact le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))

omit [Finite G] in
theorem Setup.paired_cubic_kernel
    (h : Setup R K F) (h' : Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3) :
    (h.paired_cubic_action h' hK hL).ker =
      (centralizer (U K ⊔ U L : Subgroup G)).subgroupOf (S R) := by
  ext s
  change BinaryPair.actor (h.cubic_parameter hK s,h'.cubic_parameter hL s) = 1 ↔ _
  rw [← map_one BinaryPair.actor,BinaryPair.actor_injective.eq_iff,Prod.mk_eq_one]
  rw [Setup.cubic_parameter_eq_one,Setup.cubic_parameter_eq_one,centralizer_join]
  rfl

omit [Finite G] in
/-- The two original cubic modules supply the full sixteen-vector action. -/
theorem Setup.exists_paired_cubic_coordinates
    (h : Setup R K F) (h' : Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G)) :
    ∃ e : (U K ⊔ U L : Subgroup G) ≃* Multiplicative Vector,
      ∀ (s : S R) (v : (U K ⊔ U L : Subgroup G)),
        (e.symm (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
          (h.paired_cubic_action h' hK hL s) (e v).toAdd)) : G) =
          (s : G) * (v : G) * (s : G)⁻¹ := by
  have hcomm : U K ≤ centralizer (U L : Set G) :=
    (map_subtype_le _).trans (le_centralizer_iff.mp hKL |>.trans (centralizer_le (map_subtype_le _)))
  have hdisj : Disjoint (U K) (U L) := cubic_module_disjoint hK _ ((map_subtype_le _).trans hKL)
  obtain ⟨e₀,he₀⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (U K) (U L) hdisj hcomm
  let e₁ := h.cubic_coordinates hK
  let e₂ := h'.cubic_coordinates hL
  let e : (U K ⊔ U L : Subgroup G) ≃* Multiplicative Vector :=
    e₀.symm.trans ((e₁.prodCongr e₂).trans BinaryPair.coordinates.symm)
  refine ⟨e,?_⟩
  intro s v
  obtain ⟨⟨u₁,u₂⟩,rfl⟩ := e₀.surjective v
  let w₁ := moduleConjugate h.coordinates.normalizes s u₁
  let w₂ := moduleConjugate h'.coordinates.normalizes s u₂
  have hc : BinaryPair.coordinates (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (h.paired_cubic_action h' hK hL s)
        (e (e₀ (u₁,u₂))).toAdd)) = (e₁ w₁,e₂ w₂) := by
    have ha := BinaryPair.coordinate_action (h.cubic_parameter hK s,h'.cubic_parameter hL s)
      (e (e₀ (u₁,u₂))).toAdd
    have heq : BinaryPair.coordinates (e (e₀ (u₁,u₂))) = (e₁ u₁,e₂ u₂) := by
      simp [e]; rfl
    simp only [ofAdd_toAdd,heq] at ha
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      exact ha.1.trans (h.cubic_equivariant hK s u₁).symm
    · apply Multiplicative.toAdd.injective
      exact ha.2.trans (h'.cubic_equivariant hL s u₂).symm
  have hec : e.symm (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (h.paired_cubic_action h' hK hL s)
        (e (e₀ (u₁,u₂))).toAdd)) = e₀ (w₁,w₂) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply BinaryPair.coordinates.injective
    rw [hc]
    simp [e]; rfl
  rw [hec,he₀,he₀]
  change ((s : G) * u₁ * (s : G)⁻¹) * ((s : G) * u₂ * (s : G)⁻¹) =
    (s : G) * ((u₁ : G) * u₂) * (s : G)⁻¹
  group

omit [Finite G] in
private theorem bit_eq_one (b : Bit) (h : b ≠ 1) : b = Multiplicative.ofAdd 1 := by
  have hh : ∀ b : Bit, b = 1 ∨ b = Multiplicative.ofAdd 1 := by decide +kernel
  exact (hh b).resolve_left h

theorem Setup.paired_cubic_range
    (h : Setup R K F) (h' : Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    (h.paired_cubic_action h' hK hL).range = ChapterB.Offenders.D 5 ∧
      (((U K ⊔ U L).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf (S R)).map
        (h.paired_cubic_action h' hK hL) = ChapterB.Offenders.D 5 := by
  let V₁ := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let σ := h.paired_cubic_action h' hK hL
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (h.four_module_geometry hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc).2.2.2
  have hV₁ : V₁ ≤ S R := h.conjugate_le hxR
  have hV₂ : V₂ ≤ S R := h'.conjugate_le hxR
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnc
  obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp (second_noncommuting hi)
  let a₀ : S R := ⟨a,hV₁ ha⟩
  let b₀ : S R := ⟨b,hV₂ hb⟩
  have ha1 : h.cubic_parameter hK a₀ = Multiplicative.ofAdd 1 :=
    bit_eq_one _ (fun he => han ((h.cubic_parameter_eq_one hK a₀).mp he))
  have ha2 : h'.cubic_parameter hL a₀ = 1 := (h'.cubic_parameter_eq_one hL a₀).mpr
    ((le_sup_right.trans hc).trans (centralizer_le (show U L ≤ U L ⊔ V₂ from le_sup_left)) ha)
  have hb1 : h.cubic_parameter hK b₀ = 1 := (h.cubic_parameter_eq_one hK b₀).mpr
    ((le_sup_right.trans (le_centralizer_iff.mp hc)).trans
      (centralizer_le (show U K ≤ U K ⊔ V₁ from le_sup_left)) hb)
  have hb2 : h'.cubic_parameter hL b₀ = Multiplicative.ofAdd 1 :=
    bit_eq_one _ (fun he => hbn ((h'.cubic_parameter_eq_one hL b₀).mp he))
  have has : σ a₀ = transposition 0 := by
    change BinaryPair.actor (h.cubic_parameter hK a₀,h'.cubic_parameter hL a₀) = _
    rw [ha1,ha2]
    exact BinaryPair.actor_left
  have hbs : σ b₀ = transposition 1 := by
    change BinaryPair.actor (h.cubic_parameter hK b₀,h'.cubic_parameter hL b₀) = _
    rw [hb1,hb2]
    exact BinaryPair.actor_right
  have hrange : σ.range ≤ BinaryPair.actor.range := by
    rintro p ⟨s,rfl⟩
    exact ⟨(h.cubic_parameter hK s,h'.cubic_parameter hL s),rfl⟩
  have hm : ((V₁ ⊔ V₂).subgroupOf (S R)).map σ = ChapterB.Offenders.D 5 := by
    apply le_antisymm
    · exact ((map_le_range σ _).trans hrange).trans BinaryPair.actor_range.le
    · rw [Enumeration.actor_eq_sup]
      apply sup_le (zpowers_le.mpr _) (zpowers_le.mpr _)
      · exact has ▸ mem_map_of_mem σ (show a₀ ∈ (V₁ ⊔ V₂).subgroupOf (S R) from mem_sup_left ha)
      · exact hbs ▸ mem_map_of_mem σ (show b₀ ∈ (V₁ ⊔ V₂).subgroupOf (S R) from mem_sup_right hb)
  refine ⟨le_antisymm (hrange.trans BinaryPair.actor_range.le)
    (hm.symm ▸ map_le_range σ _),?_⟩
  simpa only [Subgroup.map_sup] using hm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
