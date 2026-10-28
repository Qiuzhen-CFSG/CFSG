module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore

/-!
# Original small MS pairs as binary source inputs

All subgroups in the binary source live in the actual join L ∨ R. We transport
components and the quotient through the inclusion equivalence, retain the odd
index of the original overgroup, and pull characteristic subgroups back along
the same relative radical equivalence. The resulting source input has no new
mathematical premises. Mapping its commutator core back along the join subtype
recovers the literal `msQ L R`.

The two consumers transfer residual idempotence and the already proved abelian
core models to this literal subgroup. They provide genuine input for the binary
branch of C.1.34, without asserting its remaining centralizer or stabilizer
clauses. Source: Aschbacher--Smith C.1.31--34, printed pp.135--137.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] {κ : GroupClass.{u}} {L R : Subgroup G}

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  exact ⟨b y, (characteristic_iff_le_comap.mp hC b) hy, e.apply_symm_apply _⟩

/-- Restrict the ambient group to the literal product without changing MS2 or MS3. -/
def SmallMSPair.binaryInput (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    BinaryMS.Input κ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) := by
  let J := L ⊔ R
  let K := L.subgroupOf J
  let T := R.subgroupOf J
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  refine {
    sqtk := h.sqtk
    fitting := h.fitting
    component := h.component
    quotientEquiv := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e
    product := ?_
    radical := ?_
    characteristic := ?_ }
  · intro j
    obtain ⟨l, hl, r, hr, he⟩ := h.product j j.property
    exact ⟨⟨l,(le_sup_left : L ≤ L ⊔ R) hl⟩,hl,
      ⟨r,(le_sup_right : R ≤ L ⊔ R) hr⟩,hr,Subtype.ext he⟩
  · obtain ⟨A,hA,hodd,hcore⟩ := h.radical
    refine ⟨A.subgroupOf J,lt_top_iff_ne_top.mpr ?_,hodd,?_⟩
    · intro ht
      have hh := congrArg (map J.subtype) ht
      rw [map_subgroupOf_eq_of_le hA.le,← MonoidHom.range_eq_map,range_subtype] at hh
      exact hA.ne hh
    · apply map_injective J.subtype_injective
      change ((A.subgroupOf J).pCoreIn 2).map J.subtype = T.map J.subtype
      rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
        map_subgroupOf_eq_of_le hA.le,map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)]
      exact hcore
  · intro C hC hne hn
    let eT : T ≃* R := subgroupOfEquivOfLe le_sup_right
    let D : Subgroup R := C.map eT.toMonoidHom
    have hD : D.Characteristic := characteristic_map_equiv eT C hC
    have he : (D.map R.subtype).subgroupOf J = C.map T.subtype := by
      apply map_injective J.subtype_injective
      rw [map_subgroupOf_eq_of_le ((map_subtype_le D).trans le_sup_right),map_map,map_map]
      rfl
    have hz := h.characteristic D hD (he.symm ▸ hn)
    exact hne ((map_eq_bot_iff_of_injective C eT.injective).mp hz)

/-- The binary source uses exactly the commutator core of C.1.34. -/
theorem binaryCore_map (L R : Subgroup G) :
    (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))).map (L ⊔ R).subtype = msQ L R := by
  rw [BinaryMS.commutatorCore,map_commutator,map_subgroupOf_eq_of_le le_sup_left]
  rfl

/-- The actual join inclusion identifies the two commutator-core carriers. -/
noncomputable def binaryCoreEquiv (L R : Subgroup G) :
    BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R)) ≃* msQ L R :=
  ((BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))).equivMapOfInjective
    (L ⊔ R).subtype (L ⊔ R).subtype_injective).trans
      (MulEquiv.subgroupCongr (binaryCore_map L R))

/-- Residual idempotence on the original ambient commutator core. -/
theorem SmallMSPair.msQ_idempotent (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ⁅msQ L R,L⁆ = msQ L R := by
  let := h.finite
  have hh := congrArg (map (L ⊔ R).subtype) (h.binaryInput e).commutatorCore_idempotent
  rwa [map_commutator,binaryCore_map,map_subgroupOf_eq_of_le le_sup_left] at hh

open scoped IsMulCommutative
/-- The original abelian source core has one of the three proved elementary models. -/
theorem SmallMSPair.abelian_msQ_model (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) :
    ∃ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 6) ∧
      Nonempty (msQ L R ≃* Multiplicative (Fin d → ZMod 2)) := by
  let := h.finite
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  obtain ⟨d,hd,⟨f⟩⟩ := (h.binaryInput e).abelianCore_model hc'
  exact ⟨d,hd,⟨(binaryCoreEquiv L R).symm.trans f⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
