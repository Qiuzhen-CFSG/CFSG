module

public import Stellmacher.SectionTwo.PushingUpSquareInputs
public import Theory.Frattini.CentralElementarySupplement
public import Theory.GroupTheory.TwoElementaryIndexTwo

/-!
# Square control for Sylow automorphisms

Under the exact hypotheses of Stellmacher (2.5), an automorphism `τ` of the
Sylow subgroup that moves the canonical module outside the ambient 2-core
has `τ²` preserving that core. The square is essential in the source result.

Write `Z` for the canonical module in `S`, `Q = C_S(Z)`, and
`N = Φ(Q)` embedded in `S`. The imported Section 2 inputs make `Z`
elementary central in `Q` and give `[S:Q]=2`. If `τZ` is outside `Q`,
centralizer reciprocity makes `Z` lie outside `τQ`. The two coset
calculations yield `Q = Z (Q ∩ τQ)` and
`τQ = (τZ) (Q ∩ τQ)`. Central elementary supplements do not change
Frattini subgroups, hence `τN=N`.

In `S/N`, the image of `Q` is elementary of index two and the ambient
quotient is not elementary. If an automorphism moves this image, it and
its image are the only maximal elementary subgroups, by the imported
index-two theorem. Thus every automorphism has square fixing it. Apply
this to the automorphism induced by `τ`, then reflect equality through
the quotient map to obtain the literal `τ²Q=Q` in `S`.

This is the `p=2,n=1` specialization of Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), (3.4)(c), journal p.16, followed by the
`Aut(S)` specialization used in (3.5) and in (2.5) of
`refs/latex/stellmacher-n-group.tex`. The index-two proof uses the
canonical module directly and does not require a stronger structural
identification from (3.2).
-/

open scoped Pointwise
namespace Stellmacher.SectionTwo
universe u

private theorem frattini_map_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  exact e.mapSubgroup.map_radical

private theorem eq_sup_inf_of_index_two
    {H : Type*} [Group H] (Q Z B : Subgroup H)
    (hZQ : Z ≤ Q) (hZi : ¬ Z ≤ B) (hBi : B.index = 2) :
    Q = Z ⊔ (Q ⊓ B) := by
  obtain ⟨z, hz, hzB⟩ := SetLike.not_le_iff_exists.mp hZi
  apply le_antisymm
  · intro x hx
    by_cases hxB : x ∈ B
    · exact (le_sup_right : Q ⊓ B ≤ Z ⊔ (Q ⊓ B)) ⟨hx, hxB⟩
    · have hyB : x * z⁻¹ ∈ B :=
        (B.mul_mem_iff_of_index_two hBi).mpr (by simp [hxB, hzB])
      have hyQ : x * z⁻¹ ∈ Q := Q.mul_mem hx (Q.inv_mem (hZQ hz))
      have hy : x * z⁻¹ ∈ Z ⊔ (Q ⊓ B) := (le_sup_right : Q ⊓ B ≤ Z ⊔ (Q ⊓ B)) ⟨hyQ, hyB⟩
      simpa [mul_assoc] using (Z ⊔ (Q ⊓ B)).mul_mem hy ((le_sup_left : Z ≤ Z ⊔ (Q ⊓ B)) hz)
  · exact sup_le hZQ inf_le_left

private theorem moved_core_frattini_invariant
    {H : Type*} [Group H] [Finite H]
    (Q Z : Subgroup H) (hQp : IsPGroup 2 Q)
    (hZe : IsElementaryAbelian 2 Z) (hZQ : Z ≤ Q)
    (hQC : Q = Subgroup.centralizer (Z : Set H)) (hQi : Q.index = 2)
    (τ : MulAut H) (hout : ¬ τ • Z ≤ Q) :
    τ • ((frattini Q).map Q.subtype) = (frattini Q).map Q.subtype := by
  let Q' : Subgroup H := τ • Q
  let Z' : Subgroup H := τ • Z
  let E := Q ⊓ Q'
  have hZcentral : Z ≤ Subgroup.centralizer (Q : Set H) :=
    Subgroup.le_centralizer_iff.mp (le_of_eq hQC)
  have hZ'central : Z' ≤ Subgroup.centralizer (Q' : Set H) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    change ⁅Z.map τ.toMonoidHom, Q.map τ.toMonoidHom⁆ = ⊥
    rw [← Subgroup.map_commutator,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcentral,
      Subgroup.map_bot]
  have hZnot : ¬ Z ≤ Q' := by
    intro hle
    apply hout
    exact (hZ'central.trans (Subgroup.centralizer_le hle)).trans (le_of_eq hQC.symm)
  have hQ'i : Q'.index = 2 := by
    change (Q.map τ.toMonoidHom).index = 2
    exact (Subgroup.index_map_of_bijective (f := τ.toMonoidHom) τ.bijective Q).trans hQi
  have hZ'Q' : Z' ≤ Q' := Subgroup.map_mono hZQ
  have hQ'2 : IsPGroup 2 Q' := hQp.map τ.toMonoidHom
  have hZ'2 : IsElementaryAbelian 2 Z' := by
    let _ : IsElementaryAbelian 2 Z := hZe
    exact IsElementaryAbelian.map τ.toMonoidHom
  have hQgen : Q = Z ⊔ E := eq_sup_inf_of_index_two Q Z Q' hZQ hZnot hQ'i
  have hQ'gen : Q' = Z' ⊔ E := by
    simpa [E, inf_comm] using eq_sup_inf_of_index_two Q' Z' Q hZ'Q' hout hQi
  have hPhi : (frattini Q').map Q'.subtype = (frattini Q).map Q.subtype :=
    (frattini_map_eq_of_central_elementary_supplement Q' E Z' hQ'2 hZ'2 hZ'central hQ'gen).trans
      (frattini_map_eq_of_central_elementary_supplement Q E Z hQp hZe hZcentral hQgen).symm
  have hτPhi : τ • ((frattini Q).map Q.subtype) = (frattini Q').map Q'.subtype := by
    let e : Q ≃* Q' := τ.subgroupMap Q
    have he := congrArg (Subgroup.map Q'.subtype) (frattini_map_equiv e)
    change ((frattini Q).map Q.subtype).map τ.toMonoidHom = _
    rw [Subgroup.map_map]
    have hcomp : Q'.subtype.comp e.toMonoidHom = τ.toMonoidHom.comp Q.subtype := by
      ext x
      exact MulEquiv.coe_subgroupMap_apply τ Q x
    rw [Subgroup.map_map, hcomp] at he
    exact he
  exact hτPhi.trans hPhi

private theorem elementary_of_surjective
    {A B : Type*} [Group A] [Group B]
    (hA : IsElementaryAbelian 2 A) (f : A →* B) (hf : Function.Surjective f) :
    IsElementaryAbelian 2 B := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    exact (map_mul f a b).symm.trans
      ((congrArg f (hA.toIsMulCommutative.is_comm.comm a b)).trans (map_mul f b a))
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨a, rfl⟩ := hf x
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p a, map_one]

private theorem elementary_image_of_frattini_le
    {H : Type*} [Group H] [Finite H]
    (Q N : Subgroup H) [N.Normal]
    (hQp : IsPGroup 2 Q)
    (hPhi : (frattini Q).map Q.subtype ≤ N) :
    IsElementaryAbelian 2 (Q.map (QuotientGroup.mk' N)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 Q) := ⟨hQp⟩
  let f := (QuotientGroup.mk' N).subgroupMap Q
  have hker : frattini Q ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change QuotientGroup.mk' N (x : H) = 1
    exact (QuotientGroup.eq_one_iff _).mpr
      (hPhi (Subgroup.mem_map_of_mem Q.subtype hx))
  let fbar := QuotientGroup.lift (frattini Q) f hker
  have hf : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective (frattini Q) f
      ((QuotientGroup.mk' N).subgroupMap_surjective Q) hker
  exact elementary_of_surjective (isElementaryAbelian_quotient_frattini (p := 2)) fbar hf

private theorem eq_of_le_of_both_index_two
    {H : Type*} [Group H] [Finite H]
    (A B : Subgroup H) (hA : A.index = 2) (hB : B.index = 2)
    (hAB : A ≤ B) : A = B := by
  have hca := A.card_mul_index
  have hcb := B.card_mul_index
  rw [hA] at hca
  rw [hB] at hcb
  exact Subgroup.eq_of_le_of_card_ge hAB (by omega)

private theorem square_fixes_elementary_index_two
    {H : Type*} [Group H] [Finite H]
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (hAi : A.index = 2) (hH : ¬ IsElementaryAbelian 2 H)
    (τ : MulAut H) : τ ^ 2 • A = A := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 A := hA
  by_cases heq : τ • A = A
  · rw [pow_two, mul_smul, heq, heq]
  let B : Subgroup H := τ • A
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map τ.toMonoidHom
  have hBi : B.index = 2 :=
    (Subgroup.index_map_of_bijective (f := τ.toMonoidHom) τ.bijective A).trans hAi
  let _ : IsElementaryAbelian 2 B := hB
  have hτB : IsElementaryAbelian 2 ↥(τ • B : Subgroup H) := IsElementaryAbelian.map τ.toMonoidHom
  have hτBi : (τ • B).index = 2 :=
    (Subgroup.index_map_of_bijective (f := τ.toMonoidHom) τ.bijective B).trans hBi
  have hne : A ≠ B := Ne.symm heq
  rcases Subgroup.elementary_le_one_of_two_index_two A B hA hB hAi hBi hne hH
      (τ • B) hτB with hleA | hleB
  · have hEq := eq_of_le_of_both_index_two (τ • B) A hτBi hAi hleA
    simpa [B, pow_two, mul_smul] using hEq
  · have hEq := eq_of_le_of_both_index_two (τ • B) B hτBi hBi hleB
    have hback : B = A := by
      apply Subgroup.map_injective (f := τ.toMonoidHom) τ.injective
      exact hEq
    exact False.elim (heq hback)

private theorem square_fixes_of_frattini_quotient
    {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal] (hQp : IsPGroup 2 Q)
    (hQi : Q.index = 2)
    (τ : MulAut H)
    (hNinv : τ • ((frattini Q).map Q.subtype) = (frattini Q).map Q.subtype)
    (hnot : ¬ IsElementaryAbelian 2 (H ⧸ (frattini Q).map Q.subtype)) :
    τ ^ 2 • Q = Q := by
  let N := (frattini Q).map Q.subtype
  let q := QuotientGroup.mk' N
  let τbar : MulAut (H ⧸ N) := QuotientGroup.congr N N τ hNinv
  let A := Q.map q
  have hNA : N ≤ Q := Subgroup.map_subtype_le _
  have hAe : IsElementaryAbelian 2 A := elementary_image_of_frattini_le Q N hQp le_rfl
  have hAi : A.index = 2 := by
    change (Q.map q).index = 2
    rw [Subgroup.index_map_eq Q (QuotientGroup.mk'_surjective N)
      (by simpa [QuotientGroup.ker_mk', q] using hNA)]
    exact hQi
  have hbarSquare : τbar ^ 2 • A = A :=
    square_fixes_elementary_index_two A hAe hAi hnot τbar
  have hcompat : τbar.toMonoidHom.comp q = q.comp τ.toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk' N N τ hNinv x
  have hmapCompat (B : Subgroup H) : (τ • B).map q = τbar • (B.map q) := by
    change (B.map τ.toMonoidHom).map q = (B.map q).map τbar.toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map, hcompat]
  have hmapSquare : (τ ^ 2 • Q).map q = Q.map q := by
    rw [pow_two, mul_smul, hmapCompat, hmapCompat]
    simpa [A, pow_two, mul_smul] using hbarSquare
  have hNτQ : N ≤ τ ^ 2 • Q := by
    have hNinv2 : τ ^ 2 • N = N := by rw [pow_two, mul_smul, hNinv, hNinv]
    rw [← hNinv2]
    exact Subgroup.map_mono hNA
  have hback := congrArg (Subgroup.comap q) hmapSquare
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq,
    show q.ker = N from QuotientGroup.ker_mk' N,
    sup_of_le_left hNτQ, sup_of_le_left hNA] at hback
  exact hback

/-- Source (3.4)(c), specialized to the exact n=1 Section 2 setting. -/
public theorem pushing_up_three_four_square_control
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (hbar : Nonempty (barG ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (τ : MulAut S) :
    ¬ τ • vSubgroupInSylow S ≤ pushingUpQ S → τ ^ 2 • pushingUpQ S = pushingUpQ S := by
  intro hout
  obtain ⟨hZe, hZQ, hQC, hQi, hnot⟩ := pushing_up_square_control_inputs h S hcharacteristic hunique q hq hker hbar
  let Q := pushingUpQ S
  let _ : Q.Normal := (pCore_normal (p := 2) (G := G)).comap (S : Subgroup G).subtype
  have hQp : IsPGroup 2 Q := S.isPGroup'.to_subgroup Q
  have hNinv := moved_core_frattini_invariant Q (vSubgroupInSylow S)
    hQp hZe hZQ hQC hQi τ hout
  exact square_fixes_of_frattini_quotient Q hQp hQi τ hNinv hnot

end Stellmacher.SectionTwo
