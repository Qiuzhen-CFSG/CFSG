module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Double.Action
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender

/-!
# Thompson and Baumann on the complete doubled MS core

The actual conjugation coordinates have precisely the ambient centralizer
as kernel. Maximum elementary subgroup counting therefore makes every
nontrivial maximum image an offender. The simultaneously marked offender
in the native MS action identifies the entire Thompson image. Its exact
pointwise-fixer calculation then identifies the Baumann image as well.
The fixed subgroup in the full core has order sixteen in both cases.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open BinaryLinearThree BinaryLinearThree.DoubledOffenders
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
variable {J : Type*} [Group J] [Finite J] {κ : GroupClass} {L R : Subgroup J}
    {h : Input κ L R} {q : AbelianCore.NaturalQuotient h 2} {P : Sylow 2 J}

private theorem coordinates_fixed_iff (d : DoubledCoreAction h q P)
    (A : Subgroup J) (x : commutatorCore L) :
    (d.coordinates x).toAdd ∈ fixedSpace τ (A.map d.actor) ↔
      (x : J) ∈ centralizer (A : Set J) := by
  let := h.component_normal
  constructor
  · intro hx a ha
    let y : commutatorCore L := ⟨a*x*a⁻¹,
      (inferInstance : (commutatorCore L).Normal).conj_mem x x.property a⟩
    have he : d.coordinates y = d.coordinates x := by
      apply Multiplicative.toAdd.injective
      exact (d.equivariant a x y rfl).trans (hx ⟨d.actor a,mem_map_of_mem _ ha⟩)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (d.coordinates.injective he))
  · intro hx
    rintro ⟨_,a,ha,rfl⟩
    have he : (x : J) = a*x*a⁻¹ := by rw [hx a ha,mul_inv_cancel_right]
    exact (d.equivariant a x x he).symm

private theorem coordinates_kernel (d : DoubledCoreAction h q P) :
    d.actor.ker = centralizer (commutatorCore L : Set J) := by
  ext a
  constructor
  · intro ha x hx
    have hf : (d.coordinates ⟨x,hx⟩).toAdd ∈ fixedSpace τ ((zpowers a).map d.actor) := by
      have hh : (zpowers a).map d.actor = ⊥ :=
        (Subgroup.map_eq_bot_iff _).mpr (zpowers_le.mpr ha)
      rw [hh]
      intro b
      change τ (b : D) _ = _
      rw [mem_bot.mp b.property]
      rfl
    exact ((coordinates_fixed_iff d _ ⟨x,hx⟩).mp hf a (mem_zpowers a)).symm
  · intro ha
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
    have he : (x : J) = a*x*a⁻¹ := by rw [←ha x x.property,mul_inv_cancel_right]
    exact (d.equivariant a x x he).symm

private def fixedCoordinates (d : DoubledCoreAction h q P) (A : Subgroup J) :
    (commutatorCore L ⊓ centralizer (A : Set J) : Subgroup J) ≃
      fixedSpace τ (A.map d.actor) where
  toFun x := ⟨(d.coordinates ⟨x,x.property.1⟩).toAdd,
    (coordinates_fixed_iff d A _).mpr x.property.2⟩
  invFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val),
    (d.coordinates.symm (Multiplicative.ofAdd v.val)).property,
    (coordinates_fixed_iff d A _).mp (by rw [d.coordinates.apply_symm_apply]; exact v.property)⟩
  left_inv x := by simp
  right_inv v := by simp

private theorem maximum_image_offender (d : DoubledCoreAction h q P)
    (hc : IsMulCommutative (commutatorCore L)) (A : Subgroup J)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hne : A.map d.actor ≠ ⊥) :
    IsOffender τ (A.map d.actor) := by
  let := h.component_normal
  let : IsElementaryAbelian 2 (commutatorCore L) :=
    h.abelianCore_elementary_of_naturalQuotient hc q
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map d.actor) := IsElementaryAbelian.map d.actor
  let : Finite (A.map d.actor) := Finite.of_surjective
    (fun a : A => (⟨d.actor a,mem_map_of_mem _ a.property⟩ : A.map d.actor))
    (by rintro ⟨_,a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩)
  refine ⟨⟨hne,inferInstance⟩,?_⟩
  have hb := maxElementary_card_le_fixed_mul_image R (commutatorCore L) A
    ((commutator_le_left _ _).trans h.radical.twoCore_le) hA d.actor (coordinates_kernel d)
  have hV : Nat.card (commutatorCore L) = 64 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  rw [hV,Nat.card_congr (fixedCoordinates d A)] at hb
  have hF := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace τ (A.map d.actor))
  rw [Nat.card_zmod] at hF
  have hI : Nat.card (A.map d.actor) = 2 ^ rank (A.map d.actor) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (A.map d.actor)).exists_card_eq
    rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]
  rw [hF,hI,←pow_add] at hb
  have hb' : 6 ≤ Module.finrank (ZMod 2) (fixedSpace τ (A.map d.actor)) +
      rank (A.map d.actor) := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  have hd := fixedCodim_add_finrank τ (A.map d.actor)
  have hdim : Module.finrank (ZMod 2) (Vector × Vector) = 6 := by
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector,Module.finrank_prod]
  rw [hdim] at hd
  omega

private theorem actor_normalizes (d : DoubledCoreAction h q P) : d.actor.range ≤ N := by
  let := h.component_normal
  have hLC : L.map d.actor = δ.range := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      exact ⟨_,(d.component ⟨l,hl⟩).symm⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
      refine ⟨l,l.property,?_⟩
      rw [d.component,hl,MulEquiv.apply_symm_apply]
  change d.actor.range ≤ normalizer (δ.range : Set D)
  rw [←hLC]
  rintro _ ⟨j,rfl⟩
  exact L.le_normalizer_map d.actor (mem_map_of_mem d.actor
    (show j ∈ normalizer (L : Set J) by rw [normalizer_eq_top]; trivial))

/-- Both characteristic source subgroups have the same marked four-group
image. The statement retains the actual MS core, actor and component frame. -/
theorem DoubledCoreAction.thompson_baumann_images (d : DoubledCoreAction h q P)
    (hc : IsMulCommutative (commutatorCore L)) (hRP : R ≤ (P : Subgroup J)) :
    (elementaryAbelianMaxJ R).map d.actor =
        ((BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ) ∧
      (ChapterB.baumann R).map d.actor =
        ((BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ) := by
  let := h.component_normal
  let : IsElementaryAbelian 2 (commutatorCore L) :=
    h.abelianCore_elementary_of_naturalQuotient hc q
  let A := (BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ
  have hJ : ¬ elementaryAbelianMaxJ R ≤ d.actor.ker := by
    rw [coordinates_kernel]
    exact fun he => h.thompson_not_le_core
      (he.trans (h.abelianCore_centralizer_le_twoCore_of_twoCopies q))
  apply ChapterB.thompson_baumann_image_of_unique_maximum_image (commutatorCore L) R
    d.actor A ((commutator_le_left _ _).trans h.radical.twoCore_le) hJ
  · intro B hB hne
    exact d.unique_offender _ (map_mono (hB.1.trans hRP))
      (maximum_image_offender d hc B hB hne)
  · rintro _ ⟨x,hx,rfl⟩
    apply (fixes_conjugate_fixedSpace_iff d.frame (d.actor x)
      (actor_normalizes d ⟨x,rfl⟩)).mp
    intro v hv
    obtain ⟨c,hc⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
    have hcv : (d.coordinates c).toAdd = v := congrArg Multiplicative.toAdd hc
    have hca : (c : J) ∈ centralizer (A.comap d.actor : Set J) := by
      apply (coordinates_fixed_iff d _ c).mp
      rintro ⟨_,a,ha,rfl⟩
      rw [hcv]
      exact hv ⟨d.actor a,ha⟩
    have hcomm := hx.2 c ⟨c.property,hca⟩
    have he : (c : J) = x*c*x⁻¹ := by rw [←hcomm,mul_inv_cancel_right]
    rw [←hcv]
    exact (d.equivariant x c c he).symm

/-- The literal fixed subgroup of either characteristic source subgroup
has order sixteen in the full six-dimensional MS core. -/
theorem DoubledCoreAction.thompson_baumann_fixed_card (d : DoubledCoreAction h q P)
    (hc : IsMulCommutative (commutatorCore L)) (hRP : R ≤ (P : Subgroup J)) :
    Nat.card (commutatorCore L ⊓ centralizer (elementaryAbelianMaxJ R : Set J) : Subgroup J) = 16 ∧
      Nat.card (commutatorCore L ⊓ centralizer (ChapterB.baumann R : Set J) : Subgroup J) = 16 := by
  have hd := d.thompson_baumann_images hc hRP
  have hcard (A : Subgroup J)
      (hA : A.map d.actor = (BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ) :
      Nat.card (commutatorCore L ⊓ centralizer (A : Set J) : Subgroup J) = 16 := by
    rw [Nat.card_congr (fixedCoordinates d A),hA]
    have hcod : fixedCodim τ
        ((BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ) = 2 := by
      rw [conjugate_radical_eq,fixedCodim_map_conj]
      change Module.finrank (ZMod 2) ((Vector × Vector) ⧸ fixedSpace τ radical) = 2
      rw [fixedSpace_radical]
      exact DoubledFixedSpace.fixedCodim_radical
    have hd := fixedCodim_add_finrank τ
      ((BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ)
    have hdim : Module.finrank (ZMod 2) (Vector × Vector) = 6 := by
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector,Module.finrank_prod]
    rw [hcod,hdim] at hd
    have hf : Module.finrank (ZMod 2) (fixedSpace τ
        ((BinaryLinearThree.R.map (MulAut.conj d.frame).toMonoidHom).map δ)) = 4 := by omega
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hf]
    rfl
  exact ⟨hcard _ hd.1,hcard _ hd.2⟩

end CFSG.Quasithin.ChapterC.BinaryMS
