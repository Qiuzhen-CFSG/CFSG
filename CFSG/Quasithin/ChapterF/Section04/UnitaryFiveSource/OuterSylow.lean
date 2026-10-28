module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphSymplectic
public import Theory.GroupTheory.SylowOuterCentralizerSelection

/-!
# Saturating an outer involution in the same U₅(4) extension

The native flag count gives the odd middle index 1132625. Thus a Sylow
subgroup of the specified middle remains Sylow in the full extension.
Conjugate an outer involution into that supplied Sylow with maximal
centralizer, and restrict to the normal inner subgroup. Both full-extension
and inner centralizers are saturated, on the same carrier and base map.

These are the local selection and saturation inputs to F.4.37, printed
p.293 of refs/quasithin.pdf. Graph type and Sylow placement in the original
ambient completion are not conclusions of this selection argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
variable (U : GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)

theorem five_middle_index : (E.middle.subgroupOf E.carrier).index = 1132625 := by
  have hn := E.card_neighbors_eq_native (five_conj_injective U) false
  rw [five_native_card_neighbors] at hn
  change Nat.card ((graph E.family).neighborSet (base E.family false)) = 65 at hn
  rw [card_neighbor_base] at hn
  have hi := E.card_coset_eq_native (five_conj_injective U) false
  rw [five_native_card_coset] at hi
  change (E.family false).index = 17425 at hi
  have hmid : E.middle.subgroupOf E.carrier = E.family true ⊓ E.family false := by
    ext x
    exact and_comm
  rw [hmid, ← relIndex_mul_index inf_le_right, inf_relIndex_right]
  change (E.family true).relIndex (E.family false) = 65 at hn
  rw [hn,hi]

/-- The middle Sylow is Sylow in the same full extension. -/
def fiveMiddleSylow (P : Sylow 2 E.middle) : Sylow 2 E.carrier :=
  (P.isPGroup'.map (inclusion (inf_le_left.trans E.left_le))).toSylow (by
    rw [index_map_of_injective _ (inclusion_injective _), inclusion_range,
      five_middle_index]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index (by decide))

theorem five_base_normal : E.baseHom.range.Normal := by
  constructor
  rintro a ⟨x,rfl⟩ b
  refine ⟨b.val x,?_⟩
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  symm
  change b.val (x * b.val.symm y * x⁻¹) = b.val x * y * (b.val x)⁻¹
  rw [map_mul,map_mul,map_inv,b.val.apply_symm_apply]

/-- Reselect an outer involution with saturated full and inner native centralizers. -/
theorem five_outer_saturated (P : Sylow 2 E.middle)
    (x : E.middle) (hxo : orderOf x = 2) (hxi : x.val ∉ inner U.Carrier) :
    ∃ y : E.middle, y ∈ (P : Subgroup E.middle) ∧ orderOf y = 2 ∧
      y.val ∉ inner U.Carrier ∧
      let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
      (∃ Q : Sylow 2 (centralizer ({j y} : Set E.carrier)),
        (Q : Subgroup _).map (centralizer ({j y} : Set E.carrier)).subtype =
          ((P : Subgroup E.middle).map j) ⊓ centralizer ({j y} : Set E.carrier)) ∧
      (∃ R : Sylow 2 (E.baseHom.range ⊓ centralizer ({j y} : Set E.carrier) : Subgroup E.carrier),
        (R : Subgroup _).map (E.baseHom.range ⊓ centralizer ({j y} : Set E.carrier)).subtype =
          ((P : Subgroup E.middle).map j) ⊓
            (E.baseHom.range ⊓ centralizer ({j y} : Set E.carrier))) := by
  let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
  let S := fiveMiddleSylow U E P
  let : E.baseHom.range.Normal := five_base_normal U E
  have hxn : j x ∉ E.baseHom.range := by
    rintro ⟨v,hv⟩
    exact hxi ⟨v,congrArg Subtype.val hv⟩
  have hxp : orderOf (j x) = 2^1 :=
    (orderOf_injective j (inclusion_injective _) x).trans (by simpa using hxo)
  obtain ⟨⟨y,hy⟩,hyo,hyn,Q,hQ⟩ :=
    S.exists_outer_with_centralizer_sylow E.baseHom.range (j x) 1 hxp hxn
  change y ∈ (P : Subgroup E.middle).map j at hy
  obtain ⟨z,hz,rfl⟩ := hy
  have ho : orderOf z = 2 :=
    (orderOf_injective j (inclusion_injective _) z).symm.trans (by simpa using hyo)
  have hi : z.val ∉ inner U.Carrier := by
    rintro ⟨v,hv⟩
    exact hyn ⟨v,Subtype.ext hv⟩
  exact ⟨z,hz,ho,hi,⟨Q,hQ⟩,
    S.centralizer_normal_intersection E.baseHom.range (j z) Q hQ⟩

/-- Pull the saturated representative back through the specified middle equivalence. -/
theorem five_outer_saturated_preimage {M : Type*} [Group M]
    (e : M ≃* E.middle) (T S : Subgroup M) (P : Sylow 2 E.middle)
    (hP : (P : Subgroup E.middle) = T.map e.toMonoidHom)
    (hinner : (P : Subgroup E.middle) ⊓ (inner U.Carrier).comap E.middle.subtype = S.map e.toMonoidHom)
    (x : M) (hxo : orderOf x=2) (hxi : (e x).val ∉ inner U.Carrier) :
    ∃ t : M, t ∈ T ∧ orderOf t=2 ∧ t ∉ S ∧ e t ∈ (P : Subgroup E.middle) ∧
      (e t).val ∉ inner U.Carrier ∧
      let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
      (∃ Q : Sylow 2 (centralizer ({j (e t)} : Set E.carrier)),
        (Q : Subgroup _).map (centralizer ({j (e t)} : Set E.carrier)).subtype =
          ((P : Subgroup E.middle).map j) ⊓ centralizer ({j (e t)} : Set E.carrier)) ∧
      (∃ R : Sylow 2 (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier) : Subgroup E.carrier),
        (R : Subgroup _).map (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier)).subtype =
          ((P : Subgroup E.middle).map j) ⊓
            (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier))) := by
  have ho : orderOf (e x)=2 := (e.orderOf_eq x).trans hxo
  have hdata := five_outer_saturated U E P (e x) ho hxi
  obtain ⟨y,hyP,hyo,hyi,hsat⟩ := hdata
  rw [hP] at hyP
  obtain ⟨t,ht,rfl⟩ := hyP
  have hto : orderOf t=2 := (e.orderOf_eq t).symm.trans
    hyo
  have hti : t ∉ S := by
    intro hts
    have hm : e t ∈ S.map e.toMonoidHom := mem_map_of_mem _ hts
    rw [←hinner] at hm
    exact hyi hm.2
  have htP : e t ∈ (P : Subgroup E.middle) := by
    rw [hP]
    exact mem_map_of_mem _ ht
  exact ⟨t,ht,hto,hti,htP,hyi,hsat⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
