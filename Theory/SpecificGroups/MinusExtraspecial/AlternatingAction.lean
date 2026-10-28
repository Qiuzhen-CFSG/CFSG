module
public import Theory.SpecificGroups.MinusExtraspecial.FivePointLifts
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.IsPerfect

/-!
# Alternating conjugation on the minus extraspecial core

Let Q be a normal subgroup isomorphic to the minus extraspecial group of
order 32, with C_G(Q) ≤ Q and G/Q isomorphic to A₅. Its conjugation action,
in any prescribed core coordinates, has image exactly the automorphisms
inducing even permutations of the five singular central cosets. The inner
automorphisms supply the full kernel of that permutation action; the faithful
quotient action supplies all of A₅. Its central kernel is the image of Z(Q),
which is also Z(G). Thus the literal central quotient is identified with this
fixed automorphism subgroup, retaining the value on every representative.

For a chosen complement, its transported action is faithful and the split
extension equivalence retains the actual core and complement coordinates.
These statements compare actions and central quotients; they do not assert
that arbitrary central extensions or marked amalgams are isomorphic.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.14)--(5.16), printed pp.116--117, and the field-four branch of (10.9), p.163.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace MinusExtraspecial.AlternatingAction
open FixedFourCalculation.Outside
variable {G : Type*} [Group G] (Q : Subgroup G) [Q.Normal]

/-- Conjugation on the literal core, transported by its given coordinates. -/
def coreAction (e : Q ≃* Model) : G →* MulAut Model :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

/-- Automorphisms inducing even permutations of the five singular points. -/
def evenAutomorphisms : Subgroup (MulAut Model) :=
  (alternatingGroup (Fin 5)).comap fivePointAction

theorem coreAction_apply (e : Q ≃* Model) (g : G) (q : Q) :
    coreAction Q e g (e q) = e (MulAut.conjNormal g q) := by
  change e (MulAut.conjNormal g (e.symm (e q))) = _
  rw [e.symm_apply_apply]

theorem coreAction_subtype (e : Q ≃* Model) (q : Q) :
    coreAction Q e (q : G) = MulAut.conj (e q) := by
  apply MulEquiv.ext
  intro v
  change e (q * e.symm v * q⁻¹) = e q * v * (e q)⁻¹
  simp only [map_mul,map_inv,e.apply_symm_apply]

theorem inner_le_range (e : Q ≃* Model) :
    (MulAut.conj : Model →* MulAut Model).range ≤ (coreAction Q e).range := by
  rintro _ ⟨m,rfl⟩
  refine ⟨(e.symm m : G), ?_⟩
  rw [coreAction_subtype,e.apply_symm_apply]

theorem coreAction_kernel (e : Q ≃* Model) :
    (coreAction Q e).ker = centralizer (Q : Set G) := by
  ext g
  constructor
  · intro hg
    apply mem_centralizer_iff.mpr
    intro q hq
    have hh := DFunLike.congr_fun hg (e (⟨q,hq⟩ : Q))
    rw [coreAction_apply] at hh
    have hh' := congrArg Subtype.val (e.injective hh)
    change g * q * g⁻¹ = q at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  · intro hg
    apply MulEquiv.ext
    intro v
    obtain ⟨q,rfl⟩ := e.surjective v
    rw [coreAction_apply]
    change e (MulAut.conjNormal g q) = e q
    congr 1
    apply Subtype.ext
    change g * (q : G) * g⁻¹ = (q : G)
    rw [←mem_centralizer_iff.mp hg q q.property,mul_inv_cancel_right]

theorem pointAction_kernel (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q) :
    (fivePointAction.comp (coreAction Q e)).ker = Q := by
  ext g
  constructor
  · intro hg
    have ha : coreAction Q e g ∈ (MulAut.conj : Model →* MulAut Model).range := by
      rw [←action_kernel]
      exact hg
    obtain ⟨m,hm⟩ := ha
    let q := e.symm m
    have hgq : g * (q : G)⁻¹ ∈ (coreAction Q e).ker := by
      change coreAction Q e (g * (q : G)⁻¹) = 1
      rw [map_mul,map_inv,coreAction_subtype]
      simp only [q,e.apply_symm_apply,←hm,mul_inv_cancel]
    rw [coreAction_kernel] at hgq
    have hmQ := Q.mul_mem (hc hgq) q.property
    simpa only [inv_mul_cancel_right] using hmQ
  · intro hg
    change coreAction Q e g ∈ fivePointAction.ker
    rw [action_kernel]
    exact ⟨e ⟨g,hg⟩,(coreAction_subtype Q e ⟨g,hg⟩).symm⟩

/-- The quotient is identified with its actual alternating action on the five points. -/
theorem exists_quotient_marking (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q)
    (eA : (G ⧸ Q) ≃* alternatingGroup (Fin 5)) :
    ∃ d : (G ⧸ Q) ≃* alternatingGroup (Fin 5),
      ∀ g, (d (QuotientGroup.mk' Q g) : Equiv.Perm (Fin 5)) =
        fivePointAction (coreAction Q e g) := by
  let f := fivePointAction.comp (coreAction Q e)
  have hk : f.ker = Q := pointAction_kernel Q e hc
  let fq : (G ⧸ Q) →* Equiv.Perm (Fin 5) := QuotientGroup.lift Q f hk.symm.le
  have hfq : Function.Injective fq := (QuotientGroup.injective_lift_iff Q f _).mpr hk.symm
  let a := fq.comp eA.symm.toMonoidHom
  have heven (x : alternatingGroup (Fin 5)) : Equiv.Perm.sign (a x) = 1 := by
    have hh : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤
        (Equiv.Perm.sign.comp a).ker := by
      rw [← commutator_alternatingGroup_eq_top (by simp)]
      exact Abelianization.commutator_subset_ker _
    exact hh (mem_top x)
  let aa : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) := a.codRestrict _ heven
  have hinj : Function.Injective aa := by
    intro x y hxy
    exact eA.symm.injective (hfq (congrArg Subtype.val hxy))
  let da := MulEquiv.ofBijective aa
    ((Nat.bijective_iff_injective_and_card aa).mpr ⟨hinj,rfl⟩)
  refine ⟨eA.trans da,fun g => ?_⟩
  change fq (eA.symm (eA (QuotientGroup.mk' Q g))) = _
  rw [eA.symm_apply_apply]
  rfl

/-- The complete conjugation image is independent of the chosen core coordinates. -/
theorem coreAction_range (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q)
    (eA : (G ⧸ Q) ≃* alternatingGroup (Fin 5)) :
    (coreAction Q e).range = evenAutomorphisms := by
  obtain ⟨d,hd⟩ := exists_quotient_marking Q e hc eA
  have hr : (fivePointAction.comp (coreAction Q e)).range = alternatingGroup (Fin 5) := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact hd g ▸ (d (QuotientGroup.mk' Q g)).property
    · intro hx
      obtain ⟨q,hq⟩ := d.surjective ⟨x,hx⟩
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective Q q
      exact ⟨g,(hd g).symm.trans (congrArg Subtype.val hq)⟩
  have hk : fivePointAction.ker ≤ (coreAction Q e).range :=
    action_kernel ▸ inner_le_range Q e
  rw [evenAutomorphisms,←hr,←MonoidHom.map_range,comap_map_eq_self hk]

omit [Q.Normal] in
/-- Its central kernel is precisely the image of the core's center. -/
theorem centralizer_eq_center_image
    (hc : centralizer (Q : Set G) ≤ Q) :
    centralizer (Q : Set G) = (center Q).map Q.subtype := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨x,hc hx⟩,Subgroup.mem_center_iff.mpr (fun q => ?_),rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp hx q q.property)
  · rintro ⟨q,hq,rfl⟩
    exact mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hq ⟨y,hy⟩))

/-- The enlargement's center is the same central involution as its core. -/
theorem center_eq_center_image (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q) :
    center G = (center Q).map Q.subtype := by
  apply le_antisymm
  · rw [←centralizer_eq_center_image Q hc]
    exact center_le_centralizer _
  · apply central_of_normal_card_two
    rw [card_map_of_injective Q.subtype_injective,
      Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center

/-- The literal central quotient realizes the full even automorphism image. -/
def centralQuotientEquiv (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q)
    (eA : (G ⧸ Q) ≃* alternatingGroup (Fin 5)) :
    (G ⧸ center G) ≃* evenAutomorphisms :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [coreAction_kernel,centralizer_eq_center_image Q hc,center_eq_center_image Q e hc] :
    (coreAction Q e).ker = center G)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (coreAction Q e)).trans
      (MulEquiv.subgroupCongr (coreAction_range Q e hc eA)))

theorem centralQuotientEquiv_apply (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q)
    (eA : (G ⧸ Q) ≃* alternatingGroup (Fin 5)) (g : G) :
    (centralQuotientEquiv Q e hc eA (QuotientGroup.mk' (center G) g) : MulAut Model) =
      coreAction Q e g := rfl

/-- A perfect A₅ extension of the minus core is self-centralizing. -/
theorem selfCentralizing_of_perfect [Group.IsPerfect G] (e : Q ≃* Model)
    (eA : (G ⧸ Q) ≃* alternatingGroup (Fin 5)) :
    centralizer (Q : Set G) ≤ Q := by
  let f := fivePointAction.comp (coreAction Q e)
  have hQ : Q ≤ f.ker := by
    intro q hq
    change coreAction Q e q ∈ fivePointAction.ker
    rw [action_kernel]
    exact ⟨e ⟨q,hq⟩,(coreAction_subtype Q e ⟨q,hq⟩).symm⟩
  let fq := QuotientGroup.lift Q f hQ
  let a := fq.comp eA.symm.toMonoidHom
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hinj : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    rcases (inferInstance : a.ker.Normal).eq_bot_or_eq_top with ha | ha
    · exact ha
    · have hzero (g : G) : f g = 1 := by
        have hh : eA (QuotientGroup.mk' Q g) ∈ a.ker := ha ▸ mem_top _
        change fq (eA.symm (eA (QuotientGroup.mk' Q g))) = 1 at hh
        rw [eA.symm_apply_apply] at hh
        exact hh
      let I := (MulAut.conj : Model →* MulAut Model).range
      have hI : ⁅I,I⁆ = ⊥ := by
        change ⁅(MulAut.conj : Model →* MulAut Model).range,
          (MulAut.conj : Model →* MulAut Model).range⁆ = ⊥
        rw [MonoidHom.range_eq_map,←map_commutator,←commutator_def,
          IsExtraspecial.commutator_eq_center (p := 2)]
        apply le_bot_iff.mp
        apply (map_le_iff_le_comap).mpr
        intro q hq
        apply MulEquiv.ext
        intro v
        change q * v * q⁻¹ = v
        rw [←Subgroup.mem_center_iff.mp hq v,mul_inv_cancel_right]
      let R := (coreAction Q e).range
      have hRI : R ≤ I := by
        rintro _ ⟨g,rfl⟩
        change coreAction Q e g ∈ (MulAut.conj : Model →* MulAut Model).range
        rw [←action_kernel]
        exact hzero g
      let : IsMulCommutative R := commutator_self_eq_bot_iff.mp
        (le_antisymm ((commutator_mono hRI hRI).trans hI.le) bot_le)
      let : Group.IsPerfect R := Group.IsPerfect.range _
      have hR : R = ⊥ := eq_bot_iff.mpr (fun x hx =>
        congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : R) 1))
      have hh : MulAut.conj (quaternion (.a 1)) = 1 := by
        have hm := inner_le_range Q e (show MulAut.conj (quaternion (.a 1)) ∈ I from ⟨_,rfl⟩)
        change MulAut.conj (quaternion (.a 1)) ∈ R at hm
        rwa [hR] at hm
      have he := DFunLike.congr_fun hh (quaternion (.xa 0))
      exact (show MulAut.conj (quaternion (.a 1)) (quaternion (.xa 0)) ≠
        quaternion (.xa 0) by decide +kernel) he |>.elim
  intro g hg
  have hfg : f g = 1 := by
    change coreAction Q e g ∈ fivePointAction.ker
    have hh : g ∈ (coreAction Q e).ker := (coreAction_kernel Q e).symm ▸ hg
    rw [show coreAction Q e g = 1 from hh]
    exact one_mem _
  have ha : a (eA (QuotientGroup.mk' Q g)) = a 1 := by
    change fq (eA.symm (eA (QuotientGroup.mk' Q g))) = a 1
    rw [eA.symm_apply_apply,map_one]
    exact hfg
  have hh : QuotientGroup.mk' Q g = 1 := eA.injective (by
    simpa only [map_one] using hinj ha)
  exact (QuotientGroup.eq_one_iff g).mp hh

variable {H : Type*} [Group H]

/-- The actual conjugation of a chosen complement in prescribed coordinates. -/
def complementAction (e : Q ≃* Model) (C : Subgroup G) (eC : C ≃* H) :
    H →* MulAut Model :=
  (coreAction Q e).comp (C.subtype.comp eC.symm.toMonoidHom)

theorem complementAction_injective (e : Q ≃* Model)
    (hc : centralizer (Q : Set G) ≤ Q)
    (C : Subgroup G) (hC : Q.IsComplement' C) (eC : C ≃* H) :
    Function.Injective (complementAction Q e C eC) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hq : (eC.symm a : G) ∈ Q := hc (by
    rw [←coreAction_kernel Q e]
    exact ha)
  have hOne : (eC.symm a : G) = 1 := disjoint_def.mp hC.disjoint hq (eC.symm a).property
  change a = 1
  apply eC.symm.injective
  simpa only [map_one] using (show eC.symm a = 1 from Subtype.ext hOne)

/-- Coordinates on the split extension, using this same complement action. -/
def splitEquiv (e : Q ≃* Model)
    (C : Subgroup G) (hC : Q.IsComplement' C) (eC : C ≃* H) :
    G ≃* Model ⋊[complementAction Q e C eC] H :=
  (SemidirectProduct.mulEquivSubgroup hC).symm.trans
    (SemidirectProduct.congr e eC (fun c => MulEquiv.ext fun q => by
      change e (MulAut.conjNormal (c : G) q) =
        coreAction Q e (eC.symm (eC c) : G) (e q)
      rw [eC.symm_apply_apply,coreAction_apply]))

theorem splitEquiv_symm_apply (e : Q ≃* Model)
    (C : Subgroup G) (hC : Q.IsComplement' C) (eC : C ≃* H)
    (x : Model ⋊[complementAction Q e C eC] H) :
    (splitEquiv Q e C hC eC).symm x = (e.symm x.left : G) * (eC.symm x.right : G) := rfl

end MinusExtraspecial.AlternatingAction
