module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.Action
public import Theory.Representation.SLThreeCentralExtension.SylowCover
public import Theory.Representation.SLThreeCentralExtension.ChiefCohomology
public import Theory.Representation.FirstCohomologyAutomorphism.FixedSupplement

/-!
# The omega-center clause of the fixed-line MS alternative

The actual ambient two-core centralizes its elementary commutator core.
Vanishing H¹ of the four-dimensional natural cover splits Ω₁Z(O₂(J))
into that core and its component-fixed part. A Sylow-fixed core vector
must belong to the fixed kernel: otherwise the proved fourteen-vector
orbit calculation would split the cover into an order-eight module.
Thus Ω₁Z(S) centralizes L, and J=LR with R≤S makes it central in J.

Source: Aschbacher–Smith C.1.34(5), printed p.137; B.4.8(2), printed p.91;
Meierfrankenfeld–Stellmacher (1993), Main Theorem (8), printed p.830.
-/

public section

open Subgroup Representation Representation.OneCohomology Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]
namespace AbelianCore.NaturalQuotient
variable (q : NaturalQuotient h 1)

private theorem ambient_representation (j : J) (d : Additive (commutatorCore L)) :
    ((q.oneRepresentation h (q.ambientActor h j) d).toMul : J) =
      j * (d.toMul : J) * j⁻¹ := by
  change (q.action h inferInstance (q.ambientActor h j) d.toMul : J) = _
  rw [q.ambientActor_action, h.coreAmbientConjugation_apply]

include h q in
theorem core_le_centralModule : commutatorCore L ≤ centralModule J := by
  intro d hd
  apply (mem_centralModule J d).mpr
  refine ⟨commutator_le_left _ _ hd, ?_, ?_⟩
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) d hd
  · intro n hn
    have hnc : n ∈ centralizer (commutatorCore L : Set J) := by
      rwa [← q.ambientActor_ker_centralizer h, q.ambientActor_kernel]
    exact (hnc d hd).symm

private theorem oneRepresentation_finrank (hd : Nat.card (commutatorCore L) = 16) :
    Module.finrank (ZMod 2) (Additive (commutatorCore L)) = 4 := by
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (commutatorCore L))
  rw [Nat.card_zmod] at hh
  change Nat.card (commutatorCore L) = _ at hh
  rw [hd] at hh
  exact Nat.pow_right_injective (by decide : 1 < 2) (hh.symm.trans (by decide : 16 = 2^4))

include h q in
theorem centralModule_split (hd : Nat.card (commutatorCore L) = 16) :
    centralModule J = commutatorCore L ⊔ (centralModule J ⊓ centralizer (L : Set J)) := by
  let f : L →* BinaryLinearThree.Group :=
    q.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let e : commutatorCore L ≃* Multiplicative (Additive (commutatorCore L)) := {
    toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
    invFun := fun x => x.toAdd.toMul
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let := SLThreeCentralExtension.H1_subsingleton_of_four_dimensional_cover
    (q.oneRepresentation h) (q.oneProjection h) (q.oneProjection_isCover h)
    (oneRepresentation_finrank hd)
  apply eq_sup_inf_centralizer_of_H1_zero L (commutatorCore L) (centralModule J)
    (h.commutatorCore_le.trans (map_subtype_le _)) (q.core_le_centralModule h)
    f (q.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) e
    (q.oneRepresentation h)
  · intro l w
    change ((q.oneRepresentation h (f l) w).toMul : J) =
      (l : J) * (w.toMul : J) * (l : J)⁻¹
    dsimp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [q.oneRepresentation_component]
    exact h.coreConjugate_val l w.toMul
  · rintro n ⟨l,hl,rfl⟩ z hz
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
      (q.quotientEquiv.map_eq_one_iff.mp hl)
    have hn := (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hlcore)).1
    exact ((mem_centralModule J z).mp hz).2.2 l hn |>.symm
  · exact commutator_mono (fun z hz => ((mem_centralModule J z).mp hz).1) le_rfl

private theorem exists_component_lift {S : Subgroup J} (hPS : pCore 2 J ≤ S)
    {g : BinaryLinearThree.Group} (hg : g ∈ S.map (q.ambientActor h)) :
    ∃ l : L, (l : J) ∈ S ∧ q.ambientActor h l = g := by
  obtain ⟨s,hs,rfl⟩ := hg
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L)
    (q.quotientEquiv.symm (q.ambientActor h s))
  have he : q.ambientActor h l = q.ambientActor h s := by
    rw [q.ambientActor_component,hl,MulEquiv.apply_symm_apply]
  have hn : s * (l : J)⁻¹ ∈ pCore 2 J := by
    rw [← q.ambientActor_kernel]
    change q.ambientActor h (s * (l : J)⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  refine ⟨l,?_,he⟩
  have hh := S.mul_mem (S.inv_mem (hPS hn)) hs
  simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh

include h q in
/-- Every Sylow-fixed core vector lies in the actual component fixed kernel. -/
theorem sylow_fixed_core (hd : Nat.card (commutatorCore L) = 16)
    (S : Sylow 2 J) (d : commutatorCore L)
    (hfix : ∀ l : L, (l : J) ∈ (S : Subgroup J) →
      (l : J) * (d : J) = (d : J) * (l : J)) : d ∈ coreFixed L := by
  let T := S.mapSurjective (q.ambientActor_surjective h)
  apply (q.oneProjection_kernel h (Additive.ofMul d)).mp
  by_contra hnonzero
  have hf (g : BinaryLinearThree.Group) (hg : g ∈ (T : Subgroup BinaryLinearThree.Group)) :
      q.oneRepresentation h g (Additive.ofMul d) = Additive.ofMul d := by
    obtain ⟨l,hl,he⟩ := exists_component_lift h q (pCore_isPGroup.le_sylow_of_normal S) hg
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [← he,ambient_representation]
    change (l : J) * (d : J) * (l : J)⁻¹ = (d : J)
    rw [hfix l hl,mul_inv_cancel_right]
  have hbij := SLThreeCentralExtension.cover_bijective_of_sylow_fixed
    (q.oneRepresentation h) (q.oneProjection h) (q.oneProjection_isCover h)
    T (Additive.ofMul d) hnonzero hf
  have hcard := Nat.card_congr (Equiv.ofBijective (q.oneProjection h) hbij)
  have hV : Nat.card BinaryLinearThree.Vector = 8 := by
    simp only [BinaryLinearThree.Vector,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    decide
  change Nat.card (commutatorCore L) = Nat.card BinaryLinearThree.Vector at hcard
  rw [hd,hV] at hcard
  omega

include h q in
/-- The omega center of every Sylow two-subgroup is central in the original ambient group. -/
theorem sylow_omega_le_center (hd : Nat.card (commutatorCore L) = 16)
    (S : Sylow 2 J) (hRS : R ≤ (S : Subgroup J)) :
    omegaOneCenterAmbient (S : Subgroup J) ≤ center J := by
  let := h.component_normal
  intro z hz
  obtain ⟨hzS,hz2,hzfix⟩ := (mem_omegaOneCenterAmbient_iff (S : Subgroup J) z).mp hz
  have hzP : z ∈ pCore 2 J := h.core_selfCentralizing
    (fun n hn => hzfix n (pCore_isPGroup.le_sylow_of_normal S hn))
  have hzM : z ∈ centralModule J := (mem_centralModule J z).mpr
    ⟨hzP,hz2,fun n hn => hzfix n (pCore_isPGroup.le_sylow_of_normal S hn)⟩
  rw [q.centralModule_split h hd] at hzM
  obtain ⟨d,hdD,c,hc,he⟩ := mem_sup_of_normal_left.mp hzM
  have hdfix (l : L) (hl : (l : J) ∈ (S : Subgroup J)) :
      (l : J) * d = d * (l : J) := by
    have hzl := hzfix l hl
    have hcl : (l : J) * c = c * (l : J) := hc.2 l l.property
    rw [← he] at hzl
    apply mul_right_cancel (b := c)
    calc
      (l : J) * d * c = (l : J) * (d*c) := mul_assoc _ _ _
      _ = (d*c) * (l : J) := hzl
      _ = d * ((l : J) * c) := by rw [hcl]; group
      _ = (d * (l : J)) * c := (mul_assoc _ _ _).symm
  have hdC := q.sylow_fixed_core h hd S ⟨d,hdD⟩ hdfix
  have hzL : z ∈ centralizer (L : Set J) := by
    rw [← he]
    exact (centralizer (L : Set J)).mul_mem hdC hc.2
  apply mem_center_iff.mpr
  intro j
  obtain ⟨l,hl,r,hr,rfl⟩ := h.product j
  calc
    l*r*z = l*(r*z) := mul_assoc _ _ _
    _ = l*(z*r) := by rw [hzfix r (hRS hr)]
    _ = (l*z)*r := (mul_assoc _ _ _).symm
    _ = (z*l)*r := by rw [hzL l hl]
    _ = z*(l*r) := mul_assoc _ _ _

end AbelianCore.NaturalQuotient
end CFSG.Quasithin.ChapterC.BinaryMS
