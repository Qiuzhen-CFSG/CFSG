module
public import Theory.Representation.BinaryAlternatingFiveExtension.FaithfulExtension
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
public import Theory.Alternating.Aut
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Marked faithful extensions of the binary affine A₅ group

An automorphism preserving the translation subgroup induces an automorphism of
A₅. Aut(A₅)=S₅ and the trivial invertible commutant of the binary five-letter
core identify its translation action with that same permutation. Vanishing
first cohomology then identifies the kernel of the resulting permutation map
with the original translations. A faithful action of an overgroup of order
1,920 therefore gives the full S₅ quotient. The proved faithful extension
splitting retains every original translation coordinate.

Source application: the literal extended plane endpoint in Aschbacher--Smith
13.5.17, printed p.922. Its concrete faithful action and order discharge the
hypotheses in the unitary model consumer.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.OuterRecognition
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A" => AlternatingModel
private abbrev Q : Subgroup A := (SemidirectProduct.rightHom : A →* A5).ker

private def kernelEquiv : Q ≃* V where
  toFun v := v.val.left
  invFun v := ⟨SemidirectProduct.inl v,rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact v.property.symm
  right_inv _ := rfl
  map_mul' x y := by
    change x.val.left * alternatingAction x.val.right y.val.left = _
    rw [show x.val.right=1 from x.property,map_one]
    rfl

private theorem conjugate_inl (g : A) (v : V) :
    g * SemidirectProduct.inl v * g⁻¹ = SemidirectProduct.inl (alternatingAction g.right v) := by
  apply SemidirectProduct.ext
  · change g.left * alternatingAction g.right v *
        alternatingAction g.right (alternatingAction g.right⁻¹ g.left⁻¹) = _
    rw [←MulAut.mul_apply,←map_mul,mul_inv_cancel,map_one]
    simp only [MulAut.one_apply]
    rw [mul_comm g.left]
    exact mul_inv_cancel_right _ _
  · simp

private theorem action_injective : Function.Injective coreAction := by
  intro a b he
  apply naturalRepresentation_injective (Fin 5) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (coreEquivNatural (Fin 5) (by decide)).surjective v
  rw [←coreEquivNatural_equivariant,←coreEquivNatural_equivariant]
  exact congrArg (coreEquivNatural (Fin 5) (by decide))
    (congrArg Multiplicative.toAdd (DFunLike.congr_fun he (Multiplicative.ofAdd w)))

private theorem automorphism_coordinates (α : MulAut A)
    (hQ : Q.map α.toMonoidHom = Q) :
    ∃ σ : S5, (∀ x : A, (α x).right = MulAut.conjNormal σ x.right) ∧
      ∀ v : V, α (SemidirectProduct.inl v) = SemidirectProduct.inl (coreAction σ v) := by
  let aQ : MulAut Q := (α.subgroupMap Q).trans (MulEquiv.subgroupCongr hQ)
  let f : MulAut V := kernelEquiv.symm.trans (aQ.trans kernelEquiv)
  have hf (v : V) : α (SemidirectProduct.inl v) = SemidirectProduct.inl (f v) := by
    apply SemidirectProduct.ext
    · rfl
    · exact (aQ (kernelEquiv.symm v)).property
  let b : A5 →* A5 := SemidirectProduct.rightHom.comp (α.toMonoidHom.comp SemidirectProduct.inr)
  have hb (x : A) : (α x).right = b x.right := by
    rw [←SemidirectProduct.inl_left_mul_inr_right x,map_mul,hf]
    simp only [SemidirectProduct.mul_right,SemidirectProduct.right_inl,one_mul]
    rfl
  have hbi : Function.Injective b := by
    intro x y hxy
    have hx : (α (SemidirectProduct.inr (x*y⁻¹))).right = 1 := by
      change b (x*y⁻¹)=1
      rw [map_mul,map_inv,hxy,mul_inv_cancel]
    have hpre : SemidirectProduct.inr (x*y⁻¹) ∈ Q := by
      have he : Q.comap α.toMonoidHom = Q := by
        calc
          Q.comap α.toMonoidHom = (Q.map α.toMonoidHom).comap α.toMonoidHom := congrArg (Subgroup.comap α.toMonoidHom) hQ.symm
          _ = Q := comap_map_eq_self_of_injective α.injective Q
      exact he ▸ hx
    exact mul_inv_eq_one.mp hpre
  have hbs : Function.Surjective b := by
    intro x
    obtain ⟨y,hy⟩ := α.surjective (SemidirectProduct.inr x)
    exact ⟨y.right,(hb y).symm.trans (congrArg SemidirectProduct.right hy)⟩
  let β : MulAut A5 := MulEquiv.ofBijective b ⟨hbi,hbs⟩
  obtain ⟨σ,hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).surjective β
  have hβ (x : A5) : b x = MulAut.conjNormal σ x :=
    (DFunLike.congr_fun hσ x).symm
  have he (g : A5) (v : V) : f (alternatingAction g v) =
      alternatingAction (MulAut.conjNormal σ g) (f v) := by
    have hh := congrArg α (conjugate_inl (SemidirectProduct.inr g) v)
    rw [map_mul,map_mul,map_inv,hf,hf,conjugate_inl] at hh
    apply (SemidirectProduct.inl_injective (φ := alternatingAction))
    exact hh.symm.trans (congrArg SemidirectProduct.inl (by rw [hb,hβ]; rfl))
  let f' : core (Fin 5) →ₗ[ZMod 2] core (Fin 5) :=
    (AddEquiv.toMultiplicative.symm ((coreAction σ).symm * f)).toAddMonoidHom.toZModLinearMap 2
  have hfi : Function.Injective f' :=
    (AddEquiv.toMultiplicative.symm ((coreAction σ).symm * f)).injective
  have hcomm (g : S5) (hg : g∈alternatingGroup (Fin 5)) (v : core (Fin 5)) :
      f' (coreRepresentation (Fin 5) g v) = coreRepresentation (Fin 5) g (f' v) := by
    change ((coreAction σ).symm (f (alternatingAction ⟨g,hg⟩ (Multiplicative.ofAdd v)))).toAdd = _
    rw [he]
    change ((coreAction σ).symm (coreAction (σ*g*σ⁻¹) (f (Multiplicative.ofAdd v)))).toAdd = _
    have hm : (coreAction σ).symm * coreAction (σ*g*σ⁻¹) = coreAction g * (coreAction σ).symm := by
      change (coreAction σ)⁻¹ * coreAction (σ*g*σ⁻¹) = coreAction g * (coreAction σ)⁻¹
      rw [←map_inv,←map_mul,←map_mul]
      congr 1
      group
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hm _)
  have hid := FiveCentralExtension.core_commuting_eq_id f' hcomm hfi
  have hfv (v : V) : f v = coreAction σ v := by
    have hh := congrArg (coreAction σ) (congrArg Multiplicative.ofAdd (hid v.toAdd))
    exact ((coreAction σ).apply_symm_apply (f v)).symm.trans hh
  exact ⟨σ,fun x => (hb x).trans (hβ x.right),fun v => (hf v).trans (congrArg SemidirectProduct.inl (hfv v))⟩


private theorem kernel_coordinate_action (g : A) (v : Q) :
    kernelEquiv (MulAut.conjNormal g v) = coreAction g.right.val (kernelEquiv v) := by
  have hv : (v : A) = SemidirectProduct.inl (kernelEquiv v) := by
    apply SemidirectProduct.ext
    · rfl
    · exact v.property
  have hh := congrArg SemidirectProduct.left (conjugate_inl g (kernelEquiv v))
  rw [←hv] at hh
  exact hh

private theorem kernel_coordinate_mark (v : Q) :
    (v : A) = SemidirectProduct.inl (kernelEquiv v) := by
  apply SemidirectProduct.ext
  · rfl
  · exact v.property

/-- A faithful degree-two extension of the marked natural affine A₅ group
is the actual affine S₅ group, retaining every translation coordinate. -/
theorem exists_marked_equiv_of_faithful_action {G : Type*} [Group G] [Finite G]
    (i : A →* G) (hi : Function.Injective i)
    (ρ : G →* MulAut A) (hρ : Function.Injective ρ)
    (hρi : ∀ a, ρ (i a) = MulAut.conj a)
    (hQ : ∀ g, ((SemidirectProduct.rightHom : A →* A5).ker).map (ρ g).toMonoidHom =
      (SemidirectProduct.rightHom : A →* A5).ker)
    (hcard : Nat.card G = 1920) :
    ∃ E : G ≃* V ⋊[coreAction] S5,
      ∀ v : V, E (i (SemidirectProduct.inl v)) = SemidirectProduct.inl v := by
  choose s hsq hsv using fun g => automorphism_coordinates (ρ g) (hQ g)
  have hs_unique {g : G} {σ : S5}
      (hσ : ∀ v : V, (ρ g) (SemidirectProduct.inl v) = SemidirectProduct.inl (coreAction σ v)) :
      s g = σ := by
    apply action_injective
    apply MulEquiv.ext
    intro v
    exact SemidirectProduct.inl_injective ((hsv g v).symm.trans (hσ v))
  let q : G →* S5 := {
    toFun := s
    map_one' := by
      apply hs_unique
      intro v
      simp
    map_mul' g h := by
      apply hs_unique
      intro v
      rw [map_mul,MulAut.mul_apply,hsv,hsv,map_mul,MulAut.mul_apply] }
  have hqi (a : A) : q (i a) = a.right.val := by
    apply hs_unique
    intro v
    rw [hρi]
    exact conjugate_inl a v
  let j : V →* G := i.comp SemidirectProduct.inl
  have hj : Function.Injective j := hi.comp SemidirectProduct.inl_injective
  have hker : q.ker = j.range := by
    apply le_antisymm
    · intro g hg
      have hs1 : s g = 1 := hg
      obtain ⟨n,hn⟩ := automorphism_correction SemidirectProduct.rightHom
        SemidirectProduct.rightHom_surjective kernelEquiv kernel_coordinate_action
        (MulEquiv.refl A) (fun _ => rfl) kernel_coordinate_mark
        (s g) (ρ g) (hsq g) (hsv g)
      have he : ρ g = ρ (i (n.val⁻¹)) := by
        rw [hρi]
        apply MulEquiv.ext
        intro a
        have hh := hn a
        rw [hs1,map_one] at hh
        change (ρ g) a = n.val⁻¹ * a * n.val at hh
        simpa only [MulAut.conj_apply,inv_inv] using hh
      have hg' : g = j ((kernelEquiv n)⁻¹) := by
        rw [hρ he]
        change i (n.val⁻¹) = i (SemidirectProduct.inl ((kernelEquiv n)⁻¹))
        rw [kernel_coordinate_mark n]
        simp only [map_inv]
      exact ⟨_,hg'.symm⟩
    · rintro _ ⟨v,rfl⟩
      change q (i (SemidirectProduct.inl v))=1
      rw [hqi]
      rfl
  have hcK : Nat.card q.ker = 16 := by
    rw [hker,←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
    change Nat.card (core (Fin 5)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_core]
    rfl
  have hq : Function.Surjective q := by
    have hm := q.ker.card_mul_index
    rw [index_ker,hcard,hcK] at hm
    have hcR : Nat.card q.range = 120 := by omega
    have he : q.range = ⊤ := by
      apply eq_of_le_of_card_ge le_top
      simpa only [card_top,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,show Nat.factorial 5=120 from rfl] using hcR.ge
    exact MonoidHom.range_eq_top.mp he
  let e : q.ker ≃* V := (MulEquiv.subgroupCongr hker).trans (MonoidHom.ofInjective hj).symm
  have heval (v : q.ker) : j (e v) = (v : G) :=
    congrArg Subtype.val ((MonoidHom.ofInjective hj).apply_symm_apply ((MulEquiv.subgroupCongr hker) v))
  have heact (g : G) (v : q.ker) : e (MulAut.conjNormal g v) = coreAction (q g) (e v) := by
    apply hj
    rw [heval]
    change g * (v:G) * g⁻¹ = i (SemidirectProduct.inl (coreAction (q g) (e v)))
    apply hρ
    rw [map_mul,map_mul,map_inv,hρi]
    have hconj (a : A) : ρ g * ρ (i a) * (ρ g)⁻¹ = MulAut.conj ((ρ g) a) := by
      rw [hρi]
      apply MulEquiv.ext
      intro x
      simp only [MulAut.mul_apply,MulAut.inv_apply,MulAut.conj_apply,map_mul,map_inv,
        MulEquiv.apply_symm_apply]
    rw [←heval v]
    change ρ g * ρ (i (SemidirectProduct.inl (e v))) * (ρ g)⁻¹ = _
    rw [hconj,hsv]
    rfl
  obtain ⟨E,_,hE⟩ := exists_marked_symmetric_equiv q hq e heact
  refine ⟨E,fun v => ?_⟩
  have hv : j v ∈ q.ker := hker.symm ▸ (show j v ∈ j.range from ⟨v,rfl⟩)
  have hev : e ⟨j v,hv⟩ = v := hj (heval ⟨j v,hv⟩)
  exact (hE ⟨j v,hv⟩).trans (congrArg SemidirectProduct.inl hev)

end BinaryPermutation.AlternatingFiveExtension.OuterRecognition

