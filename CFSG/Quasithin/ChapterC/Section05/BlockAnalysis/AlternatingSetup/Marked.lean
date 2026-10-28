module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Normalized

/-!
# Choosing the source's two-transposition coordinates

Restrict the actual normalized-block action to K Baum(T), then conjugate
both the permutation action and the module coordinates by the permutation
supplied by the Thompson-image theorem. This marks the actual Baumann image
as D₅ without adding a coordinate choice to the source hypotheses.

Source: Aschbacher–Smith C.5.4(3), printed p.155.
-/
public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ConjugateSource
variable {G : Type*} [Group G]

private theorem map_subgroupOf_inclusion {A B C : Subgroup G}
    (hAB : A ≤ B) (hCA : C ≤ A) :
    (C.subgroupOf A).map (inclusion hAB) = C.subgroupOf B := by
  apply map_injective B.subtype_injective
  rw [map_map,show B.subtype.comp (inclusion hAB) = A.subtype from rfl,
    map_subgroupOf_eq_of_le hCA,map_subgroupOf_eq_of_le (hCA.trans hAB)]

variable [Finite G]

theorem marked_normalized_source (K T : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmove : K = ⁅K,Stellmacher.elementaryAbelianMaxJ T⁆) :
    (K ⊔ ChapterB.baumann T).pCoreIn 2 ≤ ChapterB.baumann T ∧
    ∃ (q : (K ⊔ ChapterB.baumann T : Subgroup G) →* FivePerm)
      (e : sourceModule K ≃* Multiplicative (core (Fin 5))),
      (K.subgroupOf (K ⊔ ChapterB.baumann T)).map q = alternatingGroup (Fin 5) ∧
      ((ChapterB.baumann T).subgroupOf (K ⊔ ChapterB.baumann T)).map q = ChapterB.Offenders.D 5 ∧
      ∀ (s : (K ⊔ ChapterB.baumann T : Subgroup G)) (u : sourceModule K),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) =
            (s : G) * (u : G) * (s : G)⁻¹ := by
  obtain ⟨q,e,hker,himage,he,hcore,a,ha⟩ := normalized_source K T hK hT hn P hP hmove
  let A := K ⊔ T
  let B := K ⊔ ChapterB.baumann T
  have hBA : B ≤ A := sup_le_sup_left (show ChapterB.baumann T ≤ T from inf_le_left) K
  let inc := inclusion hBA
  let q₀ := q.comp inc
  let q' := (MulAut.conj a⁻¹).toMonoidHom.comp q₀
  let c := LinearEquiv.ofBijective (coreRepresentation (Fin 5) a⁻¹)
    ((coreRepresentation (Fin 5)).apply_bijective a⁻¹)
  let e' : sourceModule K ≃* Multiplicative (core (Fin 5)) :=
    e.trans c.toAddEquiv.toMultiplicative
  have hm (C : Subgroup G) (hCB : C ≤ B) :
      (C.subgroupOf B).map q₀ = (C.subgroupOf A).map q := by
    rw [show q₀ = q.comp inc from rfl,←map_map,map_subgroupOf_inclusion hBA hCB]
  refine ⟨hcore,q',e',?_,?_,?_⟩
  · rw [show q' = (MulAut.conj a⁻¹).toMonoidHom.comp q₀ from rfl,←map_map,
      hm K le_sup_left,himage]
    exact Normal.map_conj_eq (alternatingGroup (Fin 5)) a⁻¹
  · rw [show q' = (MulAut.conj a⁻¹).toMonoidHom.comp q₀ from rfl,←map_map,
      hm (ChapterB.baumann T) le_sup_right,ha,map_map]
    have hid : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
        MonoidHom.id FivePerm := by ext x; simp [MulAut.conj_apply,mul_assoc]
    rw [hid,map_id]
  · intro s u
    have hcoord : e'.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q' s) (e' u).toAdd)) =
        e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q (inc s)) (e u).toAdd)) := by
      apply e'.injective
      rw [e'.apply_symm_apply]
      change Multiplicative.ofAdd (coreRepresentation (Fin 5) (a⁻¹ * q (inc s) * a)
          (coreRepresentation (Fin 5) a⁻¹ (e u).toAdd)) =
        Multiplicative.ofAdd (coreRepresentation (Fin 5) a⁻¹
          (e (e.symm (Multiplicative.ofAdd
            (coreRepresentation (Fin 5) (q (inc s)) (e u).toAdd)))).toAdd)
      rw [e.apply_symm_apply]
      change coreRepresentation (Fin 5) (a⁻¹ * q (inc s) * a)
          (coreRepresentation (Fin 5) a⁻¹ (e u).toAdd) =
        coreRepresentation (Fin 5) a⁻¹ (coreRepresentation (Fin 5) (q (inc s)) (e u).toAdd)
      rw [← Module.End.mul_apply,←map_mul]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
      rw [map_mul,Module.End.mul_apply]
    exact (congrArg Subtype.val hcoord).trans (he (inc s) u)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
