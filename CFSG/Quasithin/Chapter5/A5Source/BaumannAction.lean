module
public import CFSG.Quasithin.Chapter5.A5Source.ConjugateCore
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Relabel
public import Stellmacher.BaumannMap
/-!
The literal Baumann action is the four-group of disjoint transpositions,
after relabelling the original source module. This is the action used on
both original and conjugate cores in 5.1.7(1).
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
open Chapter13.Section06.CentralizerReduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem local_baumann_four_group
    (hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ∃ a : Equiv.Perm (Fin 5),
      ((baumann (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor =
        (Offenders.D 5).map (MulAut.conj a).toMonoidHom := by
  let := d.reduced.normal
  let := d.reduced.elementary
  let K := L ⊔ (T : Subgroup G)
  let R := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hq := d.localActor_surjective_of_thompson_moves hJ
  let f := d.localModuleCoordinates.symm
  have hk : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation (V.subgroupOf K)
        d.localActor hq d.localActor_kernel g v = v := by
    intro v hv _ _
    have hz : v = 0 := f.injective (hv.trans (map_zero f).symm)
    subst v
    exact map_zero _
  have hs := (SymmetricFive.source_thompson_baumann (V.subgroupOf K) R
    (fun _ hv => d.chosen.le_sylow hv) d.localActor hq d.localActor_kernel
    f.toLinearMap f.surjective (local_full_equivariant d hq) hk (local_thompson_moves d hJ)).2.2
  have hB : baumann (R : Subgroup K) = (baumann (T : Subgroup G)).subgroupOf K := by
    apply map_injective K.subtype_injective
    change ((R : Subgroup K) ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (R : Subgroup K)) : Set K)).map K.subtype = _
    rw [baumann_map_injective K.subtype K.subtype_injective]
    rw [map_subgroupOf_eq_of_le (show baumann (T : Subgroup G) ≤ K from inf_le_left.trans le_sup_right)]
    have hR : (R : Subgroup K).map K.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le le_sup_right
    rw [hR]
    rfl
  rwa [hB] at hs

/-- A simultaneous marking of the original module and Baumann action. -/
theorem exists_baumann_action_marking
    (hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ∃ q : normalizer (V : Set G) →* Equiv.Perm (Fin 5),
      ∃ m : Multiplicative (BinaryPermutation.core (Fin 5)) →* G,
        Function.Surjective q ∧ Function.Injective m ∧ m.range = V ∧
        (∀ (n : normalizer (V : Set G)) (x : BinaryPermutation.core (Fin 5)),
          (n:G) * m (Multiplicative.ofAdd x) * (n:G)⁻¹ =
            m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q n) x))) ∧
        ((baumann (T : Subgroup G)).subgroupOf (normalizer (V : Set G))).map q = Offenders.D 5 := by
  obtain ⟨a,ha⟩ := local_baumann_four_group d hJ
  let r := d.flag.relabel a
  have hq : Function.Surjective d.flag.normalizerAction := by
    intro p
    obtain ⟨g,hg⟩ := d.localActor_surjective_of_thompson_moves hJ p
    exact ⟨⟨g,(sup_le d.chosen.normalizes d.flag.T_normalizes) g.property⟩,hg⟩
  refine ⟨r.normalizerAction,r.module.map,
    (MulAut.conj a⁻¹).surjective.comp hq,r.module.injective,r.module.range_eq,
    r.normalizer_equivariant,?_⟩
  have he : ((baumann (T : Subgroup G)).subgroupOf (normalizer (V : Set G))).map
      d.flag.normalizerAction =
      ((baumann (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor := by
    ext p
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨⟨n,(le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hn.1⟩,hn,rfl⟩
    · rintro ⟨n,hn,rfl⟩
      exact ⟨⟨n,d.flag.T_normalizes hn.1⟩,hn,rfl⟩
  change (((baumann (T : Subgroup G)).subgroupOf (normalizer (V : Set G))).map
    ((MulAut.conj a⁻¹).toMonoidHom.comp d.flag.normalizerAction)) = _
  rw [←map_map,he,ha,map_map]
  have hc : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      MonoidHom.id (Equiv.Perm (Fin 5)) := by
    ext p
    simp [MulAut.conj_apply,mul_assoc]
  rw [hc,map_id]

/-- The same action marking on the actual conjugate module, preserving S. -/
theorem exists_conjugate_baumann_action_marking
    (hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G)) :
    let U := V.map (MulAut.conj g⁻¹).toMonoidHom
    ∃ q : normalizer (U : Set G) →* Equiv.Perm (Fin 5),
      ∃ m : Multiplicative (BinaryPermutation.core (Fin 5)) →* G,
        Function.Surjective q ∧ Function.Injective m ∧ m.range = U ∧
        (∀ (n : normalizer (U : Set G)) (x : BinaryPermutation.core (Fin 5)),
          (n:G) * m (Multiplicative.ofAdd x) * (n:G)⁻¹ =
            m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q n) x))) ∧
        ((baumann (T : Subgroup G)).subgroupOf (normalizer (U : Set G))).map q = Offenders.D 5 := by
  obtain ⟨q,m,hq,hm,hr,he,hS⟩ := exists_baumann_action_marking d hJ
  let e := MulAut.conj g⁻¹
  let U := V.map e.toMonoidHom
  let N := normalizer (V : Set G)
  let N' := normalizer (U : Set G)
  have hn : N.map e.toMonoidHom = N' := map_equiv_normalizer_eq V e
  let f : N' ≃* N := {
    toFun := fun n => ⟨e.symm n,mem_map_equiv.mp (hn.symm ▸ n.property)⟩
    invFun := fun n => ⟨e n,hn ▸ mem_map_of_mem e.toMonoidHom n.property⟩
    left_inv := fun n => Subtype.ext (e.apply_symm_apply n)
    right_inv := fun n => Subtype.ext (e.symm_apply_apply n)
    map_mul' := fun n k => Subtype.ext (map_mul e.symm (n:G) (k:G)) }
  refine ⟨q.comp f.toMonoidHom,e.toMonoidHom.comp m,hq.comp f.surjective,
    e.injective.comp hm,?_,?_,?_⟩
  · rw [MonoidHom.range_comp,hr]
  · intro n x
    have hh := congrArg e (he (f n) x)
    have hf : e (f n : G) = (n:G) := e.apply_symm_apply (n:G)
    simpa only [map_mul,map_inv,hf,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] using hh
  · let S := baumann (T : Subgroup G)
    have hSe : S.map e.toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hg)
    rw [←hS]
    ext p
    constructor
    · rintro ⟨n,hn,rfl⟩
      refine ⟨f n,?_,rfl⟩
      change e.symm n ∈ S
      exact mem_map_equiv.mp (hSe.symm ▸ hn)
    · rintro ⟨n,hn,rfl⟩
      refine ⟨f.symm n,?_,by simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,f.apply_symm_apply]⟩
      change e n ∈ S
      exact hSe ▸ mem_map_of_mem e.toMonoidHom hn
end CFSG.Quasithin.Chapter5.A5Source
