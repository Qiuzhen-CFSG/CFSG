module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalExclusionRecognition
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalExclusionSeed
public import Theory.Representation.BinaryPermutation.SixCentralDerived
public import Theory.GroupTheory.Commutator.CentralFixedMoved

/-!
# Derived order in the central cover of a reciprocal FF module

A fully moved normal subgroup maps onto the actual binary FF module with a
central kernel. Full movement and nonabelianness make the S6 action faithful.
The complete FF classification then recognizes its natural A6 moved section.
The three-subgroups lemma puts the lifted fixed-space kernel in the center,
so the natural central-cover commutator theorem gives derived order at most
two. The quotient coordinates and ambient residual action remain literal.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10)(i) and (5.12)(2), printed pp.880,926; Aschbacher--Smith
B.4.2 and B.5.1.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
open CFSG.Quasithin.ChapterB.QuasisimpleSource
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)

private theorem reciprocal_alternatingSix_quasisimple : IsQuasisimple A6 where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
  [Module.Finite (ZMod 2) W]

/-- A fully moved central cover of a literal S6 FF module has derived order
at most two when the residual fixes its derived subgroup. The natural
coordinates are supplied by the complete source FF classification. -/
theorem reciprocal_ff_central_cover_derived_le_two
    (P : Subgroup J) [P.Normal]
    (π : J →* S6) (_hπ : Function.Surjective π)
    (hπL : (pResidual 2 J).map π = A6)
    (ρ : Representation (ZMod 2) S6 W)
    (q : P →* Multiplicative W) (hq : Function.Surjective q)
    (hker : q.ker ≤ center P)
    (hact : ∀ (g : J) (x : P), (q (MulAut.conjNormal g x)).toAdd =
      ρ (π g) (q x).toAdd)
    (hfull : ⁅P,pResidual 2 J⁆ = P)
    (hfix : ⁅P,P⁆ ≤ centralizer (pResidual 2 J : Set J))
    (hsq : IsSQTK KnownSimple.IsKnownSimple A6) (hff : IsFFModule ρ) :
    Nat.card (_root_.commutator P) ≤ 2 := by
  by_cases habel : _root_.commutator P = ⊥
  · rw [habel,card_bot]; decide
  have hfullW : subspaceCommutator ρ ⊤ A6 = ⊤ := by
    let D := subspaceCommutator ρ ⊤ A6
    let K := D.toAddSubgroup.toSubgroup'.comap q
    have hPK : P ≤ K.map P.subtype := by
      conv_lhs => rw [←hfull,commutator_comm]
      apply commutator_le.mpr
      intro l hl x hx
      refine ⟨MulAut.conjNormal l ⟨x,hx⟩ / ⟨x,hx⟩,?_,?_⟩
      · change (q (MulAut.conjNormal l ⟨x,hx⟩ / ⟨x,hx⟩)).toAdd ∈ D
        rw [map_div]
        change (q (MulAut.conjNormal l ⟨x,hx⟩)).toAdd - (q ⟨x,hx⟩).toAdd ∈ D
        rw [hact]
        exact Submodule.subset_span ⟨π l,hπL ▸ mem_map_of_mem π hl,
          (q ⟨x,hx⟩).toAdd,Submodule.mem_top,rfl⟩
      · change l*x*l⁻¹/x = ⁅l,x⁆
        rw [div_eq_mul_inv,commutatorElement_def]
    apply top_unique
    intro w _
    obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd w)
    obtain ⟨y,hy,he⟩ := hPK x.property
    have hyx : y = x := Subtype.ext he
    rw [hyx] at hy
    change (q x).toAdd ∈ D at hy
    change (q x).toAdd ∈ subspaceCommutator ρ ⊤ A6 at hy
    simpa only [hx,toAdd_ofAdd] using hy
  have hf : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    by_contra hne
    have hAlt : A6 ≤ ρ.ker := Equiv.Perm.alternatingGroup_le_of_normal
      (by simp) ((nontrivial_iff_ne_bot _).mpr hne)
    have hzero : subspaceCommutator ρ ⊤ A6 = ⊥ := by
      apply (subspaceCommutator_eq_bot_iff ρ ⊤ A6).mpr
      intro w _ g
      change ρ g w = w
      rw [show ρ g = 1 from hAlt g.property]
      rfl
    have hw (w : W) : w = 0 := by
      have hm : w ∈ subspaceCommutator ρ ⊤ A6 := hfullW.symm ▸ Submodule.mem_top
      rwa [hzero,Submodule.mem_bot] at hm
    have hc (x : P) : x ∈ center P :=
      hker (show q x = 1 from Multiplicative.toAdd.injective (hw (q x).toAdd))
    apply habel
    apply le_bot_iff.mp
    apply commutator_le.mpr
    intro x _ y _
    exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hc y) x))
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple A6 := reciprocal_alternatingSix_quasisimple
  obtain ⟨hi,⟨E⟩⟩ := ReciprocalRecognition.ff_card360_moved_natural ρ A6
    (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
    (GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)) hsq hf hff
  let sec := MovedSection.ofNormal ρ A6
  have hspace : sec.space.toSubmodule = ⊤ := sec.space_eq.trans hfullW
  let r : Additive P →+ sec.space.toSubmodule := {
    toFun := fun x => ⟨(q x.toMul).toAdd,by rw [hspace]; trivial⟩
    map_zero' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one q)
    map_add' := by intro x y; apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_mul q x.toMul y.toMul) }
  have hr : Function.Surjective r := by
    intro w
    obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd w.val)
    exact ⟨Additive.ofMul x,Subtype.ext (congrArg Multiplicative.toAdd hx)⟩
  let f : P →* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    ((E.linearEquiv.toLinearMap.comp sec.central.toSubmodule.mkQ).toAddMonoidHom.comp r).toMultiplicativeRight
  have hfonto : Function.Surjective f := by
    intro w
    obtain ⟨x,hx⟩ := E.linearEquiv.surjective.comp (sec.central.toSubmodule.mkQ_surjective.comp hr) w.toAdd
    exact ⟨x.toMul,congrArg Multiplicative.ofAdd hx⟩
  have hfker : f.ker ≤ center P := by
    let K := f.ker
    have hKL : ⁅K.map P.subtype,pResidual 2 J⁆ ≤ centralizer (P : Set J) := by
      rw [commutator_comm]
      apply commutator_le.mpr
      rintro l hl _ ⟨x,hx,rfl⟩
      have hx0 : E.linearEquiv (sec.central.toSubmodule.mkQ (r (Additive.ofMul x))) = 0 := hx
      have hxF : r (Additive.ofMul x) ∈ fixedSpace sec.space.toRepresentation A6 := by
        rw [E.linearEquiv.map_eq_zero_iff,←LinearMap.mem_ker,Submodule.ker_mkQ,sec.central_eq] at hx0
        exact hx0
      have he := congrArg Subtype.val (hxF ⟨π l,hπL ▸ mem_map_of_mem π hl⟩)
      change ρ (π l) (q x).toAdd = (q x).toAdd at he
      have hqx : q (MulAut.conjNormal l x / x) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [map_div]
        change (q (MulAut.conjNormal l x)).toAdd - (q x).toAdd = 0
        rw [hact,he,sub_self]
      have hxc := hker hqx
      intro y hy
      have hh := congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hy⟩)
      change y * (l * (x : J) * l⁻¹ / (x : J)) = (l * (x : J) * l⁻¹ / (x : J)) * y at hh
      change y * (l * (x : J) * l⁻¹ * (x : J)⁻¹) = (l * (x : J) * l⁻¹ * (x : J)⁻¹) * y
      simpa only [div_eq_mul_inv] using hh
    have hKC := (commutator_centralizes_iff_centralizes_moved P (pResidual 2 J)
      (K.map P.subtype) (map_subtype_le _) hfix).mp hKL
    rw [hfull] at hKC
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hKC (mem_map_of_mem P.subtype hx) y y.property)
  let πL : pResidual 2 J →* A6 := {
    toFun := fun x => ⟨π x,hπL ▸ mem_map_of_mem π x.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' := fun x y => Subtype.ext (map_mul π (x : J) (y : J)) }
  have hπLonto : Function.Surjective πL := by
    intro a
    have ha : (a : S6) ∈ (pResidual 2 J).map π := hπL.symm ▸ a.property
    obtain ⟨g,hg,he⟩ := ha
    exact ⟨⟨g,hg⟩,Subtype.ext he⟩
  let τ := (alternatingGroup (Fin 6)).subtype.comp (E.groupEquiv.toMonoidHom.comp πL)
  apply BinaryPermutation.SixCentralDerived.card_derived_le_two f hfonto hfker
    ((MulAut.conjNormal (H := P)).comp (pResidual 2 J).subtype) τ
  · intro a ha
    obtain ⟨g,hg⟩ := E.groupEquiv.surjective.comp hπLonto ⟨a,ha⟩
    exact ⟨g,congrArg Subtype.val hg⟩
  · intro g x
    have hract : r (Additive.ofMul (MulAut.conjNormal (g : J) x)) =
        sec.space.toRepresentation (π g) (r (Additive.ofMul x)) :=
      Subtype.ext (hact g x)
    change E.linearEquiv (sec.central.toSubmodule.mkQ
      (r (Additive.ofMul (MulAut.conjNormal (g : J) x)))) = _
    rw [hract,←sec.central.quotientRepresentation_mk]
    exact E.intertwines (πL g) _
  · intro g _ z hz
    apply Subtype.ext
    have hz' : (z : J) ∈ ⁅P,P⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem P.subtype hz
    change (g : J)*(z : J)*(g : J)⁻¹ = (z : J)
    rw [hfix hz' g g.property,mul_inv_cancel_right]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
