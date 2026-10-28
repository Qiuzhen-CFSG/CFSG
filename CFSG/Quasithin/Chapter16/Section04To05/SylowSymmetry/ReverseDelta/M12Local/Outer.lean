module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupAction.NormalizerFixedCentralizer


/-!
# Transporting the outer M₁₂ centralizer action

An automorphism centralizing an outer involution acts on its fixed subgroup
by a fixed-element conjugation, provided the intrinsic automorphism-centralizer
decomposition holds. In the fixed subgroup C₂ × A₅, that conjugation is realized
by an element of the actual two-residual: the central factor acts trivially,
and perfectness places the A₅ factor in O². The equivalences here preserve the
original elements and transport the residual before recovering ambient conjugation.

`OuterCentralizerDecomposition` is a remaining intrinsic model obligation,
not an asserted theorem. A fixed-subgroup isomorphism alone does not supply it.
The conditional transport below is not the completed source-theorem assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 16.4.11(2), printed p.1193, and the outer row of 16.1.5(4), p.1171.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.M12Local
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

/-- Intrinsic centralizer generation in Aut(M₁₂). This is an unproved model
input, distinct from the requested ambient residual action. -/
def OuterCentralizerDecomposition : Prop :=
  ∀ (a b : MulAut Sporadic.Mathieu.M12), orderOf a = 2 →
    (¬ ∃ g, a = MulAut.conj g) → Commute a b →
      ∃ c : a.fixedSubgroup,
        b = MulAut.conj (c : Sporadic.Mathieu.M12) ∨
        b = MulAut.conj (c : Sporadic.Mathieu.M12) * a

private theorem a5_residual : pResidual 2 ReverseDelta.A5 = ⊤ := by
  let : Group.IsPerfect ReverseDelta.A5 :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hp
  let := hN
  have hsub : Subsingleton (ReverseDelta.A5 ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- In C₂×A₅, conjugation by every element is realized by the actual two-residual. -/
private theorem product_inner_by_residual {H : Type*} [Group H]
    (e : H ≃* OtherPreliminaries.Mathieu.C2 × OtherPreliminaries.Mathieu.A5) (c : H) :
    ∃ v ∈ pResidual 2 H, ∀ w : H, c * w * c⁻¹ = v * w * v⁻¹ := by
  let k : ReverseDelta.A5 →* H := e.symm.toMonoidHom.comp (MonoidHom.inr _ _)
  let v := k (e c).2
  refine ⟨v, ?_, ?_⟩
  · apply map_pResidual_le 2 k
    exact ⟨(e c).2, by rw [a5_residual]; trivial, rfl⟩
  · intro w
    apply e.injective
    simp only [map_mul, map_inv]
    have hv : e v = (1, (e c).2) := e.apply_symm_apply _
    rw [hv]
    apply Prod.ext
    · change (e c).1 * (e w).1 * ((e c).1)⁻¹ = 1 * (e w).1 * (1 : OtherPreliminaries.Mathieu.C2)⁻¹
      simp [mul_comm]
    · rfl

/-- The intrinsic automorphism-centralizer decomposition and the outer table
row imply inner action on the actual fixed subgroup's two-residual. -/
theorem model_outer_restriction
    (hdecomp : OuterCentralizerDecomposition)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (a b : MulAut Sporadic.Mathieu.M12) (ha : orderOf a = 2)
    (houter : ¬ ∃ g, a = MulAut.conj g) (hcomm : Commute a b) :
    ∃ v ∈ pResidual 2 a.fixedSubgroup, ∀ w : a.fixedSubgroup,
      b (w : Sporadic.Mathieu.M12) =
        (v : Sporadic.Mathieu.M12) * (w : Sporadic.Mathieu.M12) * (v : Sporadic.Mathieu.M12)⁻¹ := by
  have hprod : Nonempty (a.fixedSubgroup ≃* OtherPreliminaries.Mathieu.C2 × OtherPreliminaries.Mathieu.A5) := by
    rcases htable a ha with ⟨hi, _⟩ | ⟨_, hp⟩
    · exact (houter hi).elim
    · exact hp
  obtain ⟨e⟩ := hprod
  obtain ⟨c, hc⟩ := hdecomp a b ha houter hcomm
  obtain ⟨v, hv, he⟩ := product_inner_by_residual e c
  refine ⟨v, hv, ?_⟩
  intro w
  have hw := (MulAut.mem_fixedSubgroup a w).mp w.property
  rcases hc with rfl | rfl
  · exact congrArg Subtype.val (he w)
  · change MulAut.conj (c : Sporadic.Mathieu.M12) (a w) = _
    rw [hw]
    exact congrArg Subtype.val (he w)

variable {G : Type*} [Group G]

/-- Conjugation by two commuting ambient normalizers gives commuting actual
automorphisms, including after transport to the fixed M₁₂ carrier. -/
private theorem normalizer_actions_commute (M : Subgroup G)
    (x y : normalizer (M : Set G)) (h : Commute (x : G) (y : G)) :
    Commute (M.normalizerMonoidHom x) (M.normalizerMonoidHom y) := by
  apply Commute.map
  exact Subtype.ext h.eq

/-- Transport the model calculation to the original embedded O²(C_M(z)). -/
theorem ambient_outer_restriction [Finite G]
    (hdecomp : OuterCentralizerDecomposition)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (M : Subgroup G) (z : G) (hz : z ∈ normalizer (M : Set G))
    (e : M ≃* Sporadic.Mathieu.M12)
    (ha : orderOf (M.normalizerMonoidHom ⟨z, hz⟩) = 2)
    (ho : ¬ ∃ g, M.normalizerMonoidHom ⟨z, hz⟩ = MulAut.conj g) :
    ∀ x ∈ normalizer (M : Set G) ⊓ centralizer ({z} : Set G),
      ∃ v ∈ residual M z, ∀ w ∈ residual M z,
        x * w * x⁻¹ = v * w * v⁻¹ := by
  intro x hx
  let an := M.normalizerMonoidHom ⟨z, hz⟩
  let bn := M.normalizerMonoidHom ⟨x, hx.1⟩
  let a := MulAut.congr e an
  let b := MulAut.congr e bn
  have hao : orderOf a = 2 := ((MulAut.congr e).orderOf_eq an).trans ha
  have hoo : ¬ ∃ g, a = MulAut.conj g :=
    fun h => ho ((MulAut.congr_inner_iff e an).mp h)
  have hab : Commute a b := by
    apply Commute.map
    apply normalizer_actions_commute
    exact (mem_centralizer_singleton_iff.mp hx.2).symm
  obtain ⟨v, hv, hvact⟩ := model_outer_restriction hdecomp htable a b hao hoo hab
  let f : (M ⊓ centralizer ({z} : Set G) : Subgroup G) →* a.fixedSubgroup :=
    ((e.toMonoidHom.comp (inclusion inf_le_left)).codRestrict a.fixedSubgroup (by
      intro w
      rw [MulAut.mem_fixedSubgroup]
      change e (an (e.symm (e ⟨w, w.property.1⟩))) = e ⟨w, w.property.1⟩
      rw [e.symm_apply_apply]
      congr 1
      apply Subtype.ext
      change z * (w : G) * z⁻¹ = w
      rw [← mem_centralizer_singleton_iff.mp w.property.2, mul_inv_cancel_right]))
  have hf : Function.Surjective f := by
    intro v
    have hvfix := (MulAut.mem_fixedSubgroup a v).mp v.property
    have hfix : an (e.symm v) = e.symm v := by
      apply e.injective
      exact hvfix.trans (e.apply_symm_apply v).symm
    have hcomm : (e.symm v : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have he := congrArg Subtype.val hfix
      change z * (e.symm v : G) * z⁻¹ = (e.symm v : G) at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    refine ⟨⟨e.symm v, (e.symm v).property, hcomm⟩, ?_⟩
    exact Subtype.ext (e.apply_symm_apply v)
  obtain ⟨u, hu, heu⟩ := mem_map.mp ((map_pResidual_of_surjective 2 f hf).symm ▸ hv)
  refine ⟨u, ⟨u, hu, rfl⟩, ?_⟩
  intro w hw
  obtain ⟨w, hw, rfl⟩ := hw
  have he := hvact (f w)
  rw [← heu] at he
  have he' : e (bn ⟨w, w.property.1⟩) =
      e ⟨u, u.property.1⟩ * e ⟨w, w.property.1⟩ * (e ⟨u, u.property.1⟩)⁻¹ := by
    change e (bn (e.symm (e ⟨w, w.property.1⟩))) =
      e ⟨u, u.property.1⟩ * e ⟨w, w.property.1⟩ * (e ⟨u, u.property.1⟩)⁻¹ at he
    simpa only [e.symm_apply_apply] using he
  have heq : bn ⟨w, w.property.1⟩ =
      (⟨u, u.property.1⟩ : M) * ⟨w, w.property.1⟩ * (⟨u, u.property.1⟩ : M)⁻¹ := by
    apply e.injective
    simpa only [map_mul, map_inv] using he'
  exact congrArg Subtype.val heq
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.M12Local
