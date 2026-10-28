module
public import Theory.Representation.BinaryPermutation.SevenFiveFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FourGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.Complete
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.QuotientEscape

/-!
# Six-dimensional control in the local Cartan contradiction

The original FF action on U = [⟨Ω₁Z(T)^K⟩,K] is the deleted seven-letter
module when |U| = 64. Its faithful quotient extends the marked A₇ action
to permutations on seven letters, with kernel exactly O₂(KT).

A Sylow-normalized A₅ section fixes a pair of letters. Fixing the whole
Sylow-fixed space preserves that pair and normalizes the same A₅.
Perfectness lifts this normalizer through the actual two-kernel. Thus
centralizing the original omega-center in KT normalizes the original
residual of H, and the escaping cubic cannot do so in the six-space case.

Source: Aschbacher–Smith 5.1.13, printed p.637. This proves the six-space
obstruction in the centralizing-cubic branch; the comparison with the
left module and the block arguments remain separate source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource

private theorem six_natural_action
    {M : Type*} [Group M] [Finite M] (P : Sylow 2 M) (B U : Subgroup M)
    [B.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hr : IsPReduced 2 U) (hz : center (B ⧸ pCore 2 B) = ⊥)
    (hm : ⁅U,B⁆ = U) (hc : Nat.card U = 64)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hth : ⁅B,elementaryAbelianMaxJ (P : Subgroup M)⁆ = B)
    (hquot : IsPGroup 2 (M ⧸ B))
    (ha : Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((action U).comp (offenderSubgroup (action U)).subtype)
      ((B.map (actionMk U)).subgroupOf (offenderSubgroup (action U))))) :
    ∃ f : M →* Equiv.Perm (Fin 7), f.ker = pCore 2 M ∧
      B.map f = alternatingGroup (Fin 7) ∧
      ∃ l : Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 7),
        ∀ (m : M) v, l (Additive.ofMul (MulAut.conjNormal m v.toMul)) =
          BinaryPermutation.coreRepresentation (Fin 7) (f m) (l v) := by
  have hne : U ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    omega
  let q := actionMk U
  let C := B.map q
  let N := offenderSubgroup (action U)
  let D := C.subgroupOf N
  let : N.Normal := offenderSubgroup_normal (action U)
  let : C.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hCN : C ≤ N := by
    change B.map q ≤ N
    rw [←hth,map_commutator]
    exact (commutator_mono le_rfl (thompson_image_le P U)).trans (commutator_le_right _ _)
  let j := reducedQuasisimpleImageEquiv U B hr hz (by rwa [hm])
  let E := (subgroupOfEquivOfLe hCN).symm
  have hz' : center D = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : (E.symm.trans j.symm) x ∈ center (B ⧸ pCore 2 B) :=
      MulEquivClass.apply_mem_center (E.symm.trans j.symm) hx
    rw [hz] at hh
    exact (E.symm.trans j.symm).injective (by simpa only [mem_bot,map_one] using hh)
  have hmove : ChapterB.QuasisimpleSource.moved ((action U).comp N.subtype) D = ⊤ := by
    change subspaceCommutator ((action U).comp N.subtype) ⊤ D = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCN]
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (B.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) B]
    apply top_unique
    intro v _
    change (v.toMul : M) ∈ ⁅U,B⁆
    rw [hm]
    exact v.toMul.property
  obtain ⟨c⟩ := ha
  have hn := ExceptionalFixed.natural_or_four ((action U).comp N.subtype) D c
    ((E.symm.trans j.symm).trans e) hz' hmove
  have hnat : IsAlternatingNatural ((action U).comp (N.subtype.comp D.subtype)) 7 := by
    rcases hn with hn | hd
    · exact hn
    · have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
      change Nat.card U = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive U) at hh
      rw [hc,hd,Nat.card_zmod] at hh
      norm_num at hh
  obtain ⟨b⟩ := hnat
  let eC := E.trans b.groupEquiv
  let cn := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let l := b.linearEquiv.trans cn.symm
  have hl : ∀ (x : C) v, l (action U x.val v) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) (eC x) (l v) := by
    intro x v
    apply cn.injective
    change cn (cn.symm (b.linearEquiv (action U x.val v))) =
      cn (BinaryPermutation.coreRepresentation (Fin 7) (eC x).val (l v))
    rw [cn.apply_symm_apply,BinaryPermutation.coreEquivNatural_equivariant]
    change b.linearEquiv (action U x.val v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 7) (eC x)
        (cn (cn.symm (b.linearEquiv v)))
    rw [cn.apply_symm_apply]
    exact b.intertwines (E x) v
  obtain ⟨f,hfi,hfC,hact⟩ := BinaryPermutation.SevenParabolic.faithful_extension C
    (action U) (action_faithful U) eC l hl
  refine ⟨f.comp q,?_,?_,l,?_⟩
  · rw [MonoidHom.ker_comp_of_injective q f hfi,QuotientGroup.ker_mk']
    exact reduced_quasisimple_centralizer_eq_pCore U B hr hz (by rwa [hm]) hquot
  · rw [←map_map]
    change C.map f = alternatingGroup (Fin 7)
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [hfC ⟨x,hx⟩]
      exact (eC ⟨x,hx⟩).property
    · intro x hx
      obtain ⟨c,hc⟩ := eC.surjective ⟨x,hx⟩
      exact ⟨c.val,c.property,(hfC c).trans (congrArg Subtype.val hc)⟩
  · intro m v
    have he : action U (q m) v = Additive.ofMul (MulAut.conjNormal m v.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m v
    exact he ▸ hact (q m) v

namespace LocalA7Configuration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A Y X D K : Subgroup G} {n : ℕ}

/-- The six-space is the literal deleted permutation action, with both
identifications of its kernel. Surjectivity and Thompson geometry are proved
in the companion SixThompson module. -/
theorem six_action
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    let M := K ⊔ (T : Subgroup G)
    let U := (localOmegaModule T K).subgroupOf M
    letI := (LocalOmega.reduced_internal a.reduced).normal
    letI := (LocalOmega.reduced_internal a.reduced).elementary
    ∃ f : M →* Equiv.Perm (Fin 7), f.ker = centralizer (U : Set M) ∧
      f.ker = pCore 2 M ∧ (K.subgroupOf M).map f = alternatingGroup (Fin 7) ∧
      ∃ l : Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 7),
        ∀ g v, l (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
          BinaryPermutation.coreRepresentation (Fin 7) (f g) (l v) := by
  let M := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer a.sylow_normalizes)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 K)
    (subgroupOfEquivOfLe (show K ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)))
  let := LocalOmega.quotient_quasisimple a.maximal.1 (Or.inl a.quotient)
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : e b ∈ center (K ⧸ pCore 2 K) := MulEquivClass.apply_mem_center e hb
    rw [LocalOmega.quotient_center a.maximal.1 (Or.inl a.quotient)] at hh
    exact e.injective (by simpa only [mem_bot,map_one] using hh)
  have hmove : ⁅U,B⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le a.reduced.1,
      map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),
      LocalOmega.full_movement (h.qtke.evenCharacteristic T) a.maximal.1 a.sylow_normalizes]
  have hcard : Nat.card U = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv).trans hc
  have hnonG : localOmegaModule T K ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    omega
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hth : ⁅B,elementaryAbelianMaxJ (P : Subgroup M)⁆ = B := by
    apply map_injective M.subtype_injective
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      hPmap,map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),a.actor_thompson]
  have hquot : IsPGroup 2 (M ⧸ B) := by
    apply isPGroup_quotient_of_sup_eq_top B ((T : Subgroup G).subgroupOf M)
      T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show K ≤ M from le_sup_left) (show (T : Subgroup G) ≤ M from le_sup_right)]
    exact subgroupOf_self M
  have ha := LocalOmega.source_classification h.qtke a.maximal.1 a.sylow_normalizes
    (Or.inl a.quotient) a.reduced hnonG (d.not_le_baumann_normalizer h hH a.contains)
  obtain ⟨f,hker,hB,l,hact⟩ := six_natural_action P B U hr hz hmove hcard
    (e.trans a.quotient.some) hth hquot ha.2
  refine ⟨f,?_,hker,hB,l,hact⟩
  exact hker.trans (reduced_quasisimple_centralizer_eq_pCore U B hr hz
    (by rw [hmove]; intro he; rw [he,card_bot] at hcard; omega) hquot).symm

/-- In the six-dimensional case, fixing the original omega-center inside KT
forces normalization of the original residual, through the actual two-core. -/
theorem six_omega_centralizer_le_residual_normalizer
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    (K ⊔ (T : Subgroup G)) ⊓ omegaCentralizer T ≤ normalizer (residual H : Set G) := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  let B := K.subgroupOf M
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer a.sylow_normalizes)
  obtain ⟨f,hcentralizer,hker,hB,l,hact⟩ := a.six_action h hH d hc
  let R := (residual H).subgroupOf M
  have hRK := d.residual_le.trans a.contains
  have hRM : residual H ≤ M := hRK.trans le_sup_left
  let := LocalSieve.residual_perfect h.qtke h.sylow_normalizes hH hgen
  let r := subgroupOfEquivOfLe hRM
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := r.symm.toMonoidHom) r.symm.surjective
  let rH := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨F,_,_,hF,⟨dF⟩⟩ := d.residual_linear
  obtain ⟨d5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eR := (QuotientGroup.congr (pCore 2 R) (pCore 2 (pResidual 2 H))
    (r.trans rH.symm) (pCore_map_iso 2 (r.trans rH.symm))).trans (dF.trans d5)
  have hPR : (P : Subgroup M) ≤ normalizer (R : Set M) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp ((hH.1.1.2.trans (le_normalizer_residual H)) ht) x.val
  let := a.reduced.2.1
  have hUT : localOmegaModule T K ≤ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans
      (LocalOmega.span_elementary_le_sylow T K (h.qtke.evenCharacteristic T)
        a.maximal.1 a.sylow_normalizes).2
  intro g hg
  have hn : (⟨g,hg.1⟩ : M) ∈ normalizer (R : Set M) :=
    BinaryPermutation.SevenFiveFixed.fixed_kernel_normalizes_perfect_preimage f
      (hker.symm ▸ pCore_isPGroup) B hB R (comap_mono hRK) eR P hPR (by
        intro v hv
        let w := l.symm v
        have hw : ∀ t : P, MulAut.conjNormal (t.val : M) w.toMul = w.toMul := by
          intro t
          apply Additive.ofMul.injective
          apply l.injective
          rw [hact,l.apply_symm_apply]
          change BinaryPermutation.coreRepresentation (Fin 7) (f t.val) v = l (l.symm v)
          rw [l.apply_symm_apply]
          exact hv ⟨f t.val,mem_map_of_mem f t.property⟩
        have hwZ : ((w.toMul : U) : M).val ∈ omegaOneCenterAmbient (T : Subgroup G) := by
          apply (mem_omegaOneCenterAmbient_iff _ _).mpr
          refine ⟨hUT w.toMul.property,
            elemPow_eq_one_of_isElementaryAbelian (p := 2)
              (A := localOmegaModule T K) _ w.toMul.property,?_⟩
          intro t ht
          have he := congrArg (fun u : U => (u.val : G))
            (hw ⟨⟨t,(show (T : Subgroup G) ≤ M from le_sup_right) ht⟩,ht⟩)
          change t * (w.toMul.val : G) * t⁻¹ = (w.toMul.val : G) at he
          exact mul_inv_eq_iff_eq_mul.mp he
        have hwg : MulAut.conjNormal (⟨g,hg.1⟩ : M) w.toMul = w.toMul := by
          apply Subtype.ext
          apply Subtype.ext
          change g * (w.toMul.val : G) * g⁻¹ = (w.toMul.val : G)
          rw [←hg.2 _ hwZ,mul_inv_cancel_right]
        rw [←l.apply_symm_apply v,←hact,hwg]
        rfl)
  have hh := (R.le_normalizer_map M.subtype) (mem_map_of_mem M.subtype hn)
  rwa [map_subgroupOf_eq_of_le hRM] at hh

/-- The actual escaping cubic moves omega in the six-dimensional alternative. -/
theorem six_cubic_not_centralizes
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 64) : ¬ D ≤ omegaCentralizer T := by
  intro hd
  apply d.cubic_escape
  exact (le_inf ((d.cubic_le.trans inf_le_right).trans (a.contains.trans le_sup_left)) hd).trans
    (a.six_omega_centralizer_le_residual_normalizer h hH hgen d hc)

end LocalA7Configuration
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
